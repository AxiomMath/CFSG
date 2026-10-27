module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LargeExtraspecial.AS35CHyp
public import CFSG.LargeExtraspecial.S14Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open

@[expose] def FSmithSixFiveOddInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Setting X), 3 ≤ T.width →
    timmesfeldOddCore X = ⊥ →
      (∀ g : X, g * T.z * g⁻¹ ∈ T.QG → g * T.z * g⁻¹ = T.z) → T.AschbacherHyp

@[expose] def SmithE23a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* timmesfeldPSU 6) →
      ∀ t u : G, IsConj S.z t → IsConj S.z u → t ∈ S.M → u ∈ S.M → t ∉ S.QG → u ∉ S.QG →
        orderOf (t * u) = 3 →
          (∀ c ∈ S.M, Commute c t → Commute c u →
            (∀ q ∈ S.QG, Commute q t → Commute q u → Commute c q) → c ∈ S.QG) ∧
          (∀ P : Subgroup G, P ≤ S.M → (∀ p ∈ P, Commute p t ∧ Commute p u) →
            (∀ c ∈ S.M, Commute c t → Commute c u → ∀ p ∈ P, c * p * c⁻¹ ∈ P) →
              IsPGroup 2 P → P ≤ S.QG) ∧
          (∀ R : Subgroup G, S.z ∈ R → R ≤ S.QG → (∀ r ∈ R, Commute r t ∧ Commute r u) →
            (∀ c ∈ S.M, Commute c t → Commute c u → ∀ r ∈ R, c * r * c⁻¹ ∈ R) →
              R = zpowers S.z ∨ ∀ q ∈ S.QG, Commute q t → Commute q u → q ∈ R) ∧
          (∃ y : G, IsConj S.z y ∧ y ∈ S.M ∧ y ∉ S.QG ∧ Commute y t ∧ Commute y u)

end CFSG.LargeExtraspecial.S14
