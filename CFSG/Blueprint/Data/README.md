# Sporadic group generators

The `.m1` and `.m2` files are the standard generators `a` and `b` of 20 sporadic groups (type I
for J4) from the *ATLAS of Finite Group Representations*, Version 3 (R. A. Wilson et al.,
<https://brauer.maths.qmul.ac.uk/Atlas/v3/>). Each file is
`https://brauer.maths.qmul.ac.uk/Atlas/spor/<group>/mtx/<file>`

For example, `J1G1-f11r7B0.m1` is generator `a` of J1 as a 7 × 7 matrix over `GF(11)`.
The files are in MeatAxe text format.

[`NativeSporadic.lean`](../NativeSporadic.lean) reads them with `include_str` and defines each group
as the units of the matrix monoid the pair generates.

`th-H-involution-trees.txt` holds the conjugation trees of the two involution classes of
`H = ⟨xJ, yJ⟩` in the Thompson group, read by
[`CFSG/Sporadic/Th/Max3/MaxGen.lean`](../../Sporadic/Th/Max3/MaxGen.lean).
