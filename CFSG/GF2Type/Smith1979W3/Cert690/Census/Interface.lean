module

public import CFSG.GF2Type.Smith1979W3.Cert690.Census.Conj
public import Certificates.Data.Smith1979W3.CensusData

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62

@[expose] def InCodeList (minus : Bool) (A : Array ℕ) (x : V₀ ≃ₗ[ZMod 2] V₀) : Prop :=
  ∃ i ∈ A, i < (grpData minus ()).O.size ∧
    Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) (grpData minus ()).O[i]!

@[expose] def CensusLGoal (minus : Bool) (ci : ℕ) : Prop :=
  ∀ H : Subgroup (V₀ ≃ₗ[ZMod 2] V₀), H ≤ O₀ minus → NoNormalTwo H → IrreducibleSub H →
  ∀ L : Subgroup (V₀ ≃ₗ[ZMod 2] V₀),
    (∀ x, x ∈ L ↔ InCodeList minus
      ((ldata minus ()).Llist[(candidatesOf minus (ldata minus ()).Llist)[ci]!]!) x) →
    CensusCond minus H L (Code.vec (b0Of minus)) →
    (if minus then CensusMinusConcl H else CensusPlusConcl H)

end CFSG.GF2Type.Smith1979W3.Cert690

end
