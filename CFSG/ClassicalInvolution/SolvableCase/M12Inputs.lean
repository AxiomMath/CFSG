module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ClassicalInvolution.TwoGroupCase.Q8
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.Schreier.Outer

public section

namespace CFSG.ClassicalInvolution

open CFSG CFSG.Open
open scoped MatrixGroups
open CFSG.Sporadic.Schreier (centralizerIn mem_centralizerIn)

variable {M : Type*} [Group M]

section Lists

variable [DecidableEq M]

@[expose] def commutatorCheck (KL UL : List M) (k : ℕ) : Bool :=
  decide ((1 : M) ∈ UL) && UL.all (fun x => UL.all fun y => decide (x * y ∈ UL)) &&
    UL.all (fun x => decide (x⁻¹ ∈ UL)) && UL.all (fun u => decide (u ∈ KL)) &&
    UL.all (fun u => decide (u ^ 2 ^ k = 1)) &&
    KL.all (fun g => UL.all fun u => decide (g * u * g⁻¹ ∈ UL)) &&
    KL.all (fun g => decide (g ^ 3 ≠ 1) || decide (g = 1) ||
      decide (8 < (UL.map fun u => u * g * u⁻¹ * g⁻¹).dedup.length))

end Lists

end CFSG.ClassicalInvolution
