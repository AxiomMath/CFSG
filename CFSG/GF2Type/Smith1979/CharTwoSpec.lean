module

public import CFSG.GF2Type.Smith1979.IdxFourHBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open Module CFSG.LargeExtraspecial

variable {G : Type} [Group G] [Finite G]

@[expose] def HasLbar (S : Setting G) (v : S.Qt) : Prop :=
  ∃ P : Subgroup S.O, P ≤ stab S v ∧ (∀ s ∈ stab S v, ∀ p ∈ P, s * p * s⁻¹ ∈ P) ∧
    IsPGroup 2 P ∧ Nat.card P = 2 ^ 5

structure CharTwoFacts (S : Setting G) : Prop where
  sub6 : ∀ v : S.Qt, v ≠ 0 → S.q v = 0 → HasLbar S v → ∀ U : Submodule (ZMod 2) S.Qt,
    finrank (ZMod 2) U = 6 → v ∈ U →
    (∀ s ∈ stab S v, ∀ u ∈ U, (s : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U) →
    ∃ w ∈ U, w ≠ 0 ∧ S.q w = 0 ∧ ¬ HasLbar S w
  orbit : ∀ w : S.Qt, w ≠ 0 → S.q w = 0 → ¬ HasLbar S w → ∀ v : S.Qt, v ≠ 0 → S.q v = 0 →
    HasLbar S v → QuadraticMap.polar S.q v w = 0 →
    64 ≤ Set.ncard {u : S.Qt | ∃ s ∈ stab S w, (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v = u}

end CFSG.GF2Type.Smith1979.IdxFour
