module preimage;

import std.algorithm;
import std.array;
import std.range;
import std.stdio;

@safe:

const string NODE2 = "NODE2";
const uint NumberOfCycles = 5;

static assumeNothrow (T)(lazy T exp) nothrow
{
    try return exp();
    catch (Exception ex) assert(0, ex.msg);
}

const ulong HashInit = 1_000_000;
const uint EnrollCycle = 2;
private struct Hash
{
    private ulong value = HashInit;

    static Height imageToHeight (Hash image)
    {
        return Height((EnrollCycle * NumberOfCycles) - image.value - 1);
    }
}

unittest
{
    assert(Hash.init.value == HashInit);
}

public Hash hashFull (in Hash h) nothrow @nogc
{
    return Hash(h.value + 1);
}

public Hash hashMulti (Scalar secret, in string ignore, uint nonce) nothrow @nogc @safe
{
    return Hash(nonce * 50_000);
}

private struct Scalar
{
    string name;
}

/// A type to ensure that height and other integer values aren't mixed
public struct Height
{
    ///
    public ulong value;

    /// Provides implicit conversion to `ulong`
    public alias value this;

    /// Prevent needing to cast when using unary post plus operator
    public Height opUnary (string op) () if (op == "++")
    {
        return Height(this.value++);
    }

    /// Allow to offset an height by a fixed number
    public Height opBinary (string op : "+") (ulong offset) const
    {
        return Height(this.value + offset);
    }

    /// Allow to offset an height by a fixed number
    public ref Height opBinaryAssign (string op : "+=") (ulong offset) return
    {
        this.value += offset;
        return this;
    }
}

public struct PreImageCache
{
    nothrow:

    private Hash[] data;
    private ulong interval;

    /// Construct an instance using already existing data
    public this (inout(Hash)[] data_, ulong sample_size) inout @nogc pure
    {
        assert(sample_size > 0, "The distance must be at least 1");

        this.data = data_;
        this.interval = sample_size;
    }

    public this (ulong count, ulong sample_size) pure
    {
        assert(count > 1, "A count of less than 2 does not make sense");
        this(new Hash[](count), sample_size);
    }

    public void reset (in Hash seed, size_t length)
    {
        // Set the length, so that extra entries are not accessible through
        // `opIndex`
        assert(length > 0, "The length of the array should be at least 1");
        this.data.length = length;
        () @trusted { assumeSafeAppend(this.data); }();
        this.reset(seed);
    }

    public void reset (Hash seed) @nogc
    {
        this.data[0] = seed;
        foreach (ref entry; this.data[1 .. $])
        {
            foreach (idx; 0 .. this.interval)
                seed = hashFull(seed);
            entry = seed;
        }
    }

    public Hash opIndex (size_t index) const @nogc
    {
        immutable startIndex = (index / this.interval);
        Hash value = this.data[startIndex];
        foreach (_; (startIndex * this.interval) .. index)
            value = hashFull(value);
        return value;
    }

    /// Alias to the underlying data, useful when dealing with multiple levels
    public const(Hash)[] byStride () const pure @nogc { return this.data; }

    /// Returns: The number of preimages this cache can represent
    public size_t length () const pure nothrow @nogc @safe
    {
        return this.interval * this.data.length;
    }

    alias opDollar = length;
}

public struct PreImageCycle
{
    @safe nothrow:

    private Scalar secret;
    private ulong cycles;
    public uint nonce = 0;
    public ulong index = 0;
    public PreImageCache seeds;
    public PreImageCache preimages;

    public this (Scalar secret, uint cycle_length,
        uint cycles = NumberOfCycles,
        Height first_seek = Height(0))
    {
        assumeNothrow(writefln("SETUP cycle: secret:%s cycle_length:%s cycles:%s first_seek:%s",
            secret, cycle_length, cycles, first_seek));
        this.secret = secret;
        this.cycles = cycles;
        this.seeds = PreImageCache(cycles, cycle_length);
        this.preimages = PreImageCache(cycle_length, 1);
        this.seek(this.secret, first_seek);
        assumeNothrow(writefln("PreImageCycle: Height 0 preimage = %s", this[Height(0)]));
        assumeNothrow(writefln("PreImageCycle: %s\n", this));
    }

    public Hash opIndex (in Height height) @safe nothrow @nogc
    {
        this.seek(this.secret, height);
        auto offset = height % this.preimages.length();
        return this.preimages[$ - offset - 1];
    }

    private void seek (in Scalar secret, in Height height) @nogc
    {
        ulong seek_index = height / this.preimages.length();
        uint seek_nonce = cast (uint) (seek_index / this.cycles);
        seek_index %= this.cycles;

        debug { writefln("enter seek height: %s, PreImageCycle: %s", height, this); }
        if (this.seeds[0] == Hash.init || seek_nonce != this.nonce)
        {
            this.nonce = seek_nonce;
            this.index = seek_index;
            debug { writefln("seek height: %s, index updated to: %s", height, this.index); }
            const cycle_seed = hashMulti(
                secret, "consensus.preimages", this.nonce);
            this.seeds.reset(cycle_seed);
            this.preimages.reset(this.seeds.byStride[$ - 1 - this.index]);
        }
        else if (seek_index != this.index)
        {
            this.index = seek_index;
            debug { writefln("seek height: %s, index updated to: %s", height, this.index); }
            this.preimages.reset(this.seeds.byStride[$ - 1 - this.index]);
        }
        debug { writefln("exit seek height: %s, PreImageCycle: %s", height, this); }
    }
}

unittest
{
    PreImageCycle cycle_cache = PreImageCycle(Scalar("TEST 1"), EnrollCycle);
    writeln("\nTesting preimage cycles.");
    [6,1].each!(h => writefln("Height: %4s preimage: %4s\n", h, Hash.imageToHeight(cycle_cache[Height(h)])));
    // writefln("Height: %4s preimage: %4s", 1, Hash.imageToHeight(cycle_cache[Height(1)]));
}

private struct PublicKey
{
    private string name;
}

private struct KeyPair
{
    private Scalar secret;
    private PublicKey address;
}

private PreImageCycle[PublicKey] CycleCaches;

public ref PreImageCycle getWellKnownPreimages (KeyPair kp) @safe nothrow
{
    if (kp.address !in CycleCaches)
    {
        CycleCaches[kp.address] = PreImageCycle(Scalar("TESTING"), EnrollCycle);
    }
    return CycleCaches[kp.address];
}

public Hash wellKnownPreimages (Height height, KeyPair kp) @safe nothrow
{
    return getWellKnownPreimages(kp)[height];
}

// Check that cached cycles can handle being used with previous cycle heights
unittest
{
    const secret = Scalar(NODE2);
    auto NODE2_KP = KeyPair(secret, PublicKey(NODE2));
    Height preimages_height_1 = Hash.imageToHeight(wellKnownPreimages(Height(1), NODE2_KP));
    Height preimages_height_6 = Hash.imageToHeight(wellKnownPreimages(Height(6), NODE2_KP));
    assert(Hash.imageToHeight(wellKnownPreimages(Height(1), NODE2_KP)) == preimages_height_1);
}

// Test all heights of multiple cycles
unittest
{
    const cycle_length = 2;
    const number_of_cycles = 5;
    const secret = Scalar("TEST ALL");
    auto cycle = PreImageCycle(secret, cycle_length, number_of_cycles);
    writefln("cycle=%s", cycle);
    ulong total_images = cycle_length * number_of_cycles;
    void testBatch (uint nonce)
    {
        writefln("\nTESTING batch with nonce=%s", nonce);
        Hash[] batch;
        iota(total_images).each!( i =>
            batch ~= i == 0 ?
                hashMulti(secret, "consensus.preimages", nonce)
                : hashFull(batch[i - 1]));
        writefln("batch=%s", batch);
        batch.enumerate.each!( (idx, image) =>
            assert(cycle[Height((total_images * nonce) + total_images - idx - 1)] == image));
    }
    iota(3).each!( i => testBatch(i));
}
