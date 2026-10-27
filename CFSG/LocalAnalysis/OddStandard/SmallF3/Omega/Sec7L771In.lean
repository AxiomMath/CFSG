module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82E8Cent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), IsOm6P K →
    ∀ (E : Subgroup G) (z ν : G), IsElemAb2 E 3 → E ≤ K → z ∈ E → IsI4PlusIn K z →
      ν ∈ K → orderOf ν = 3 → ν ∈ normalizer (E : Set G) →
      (∀ e ∈ E, ν * e = e * ν → e = 1 ∨ e = z) →
      (∃ P : Subgroup G, IsSylow2Of P K ∧
          IsNormalE16In P (K ⊓ centralizer (E : Set G)) ∧
          E ≤ K ⊓ centralizer (E : Set G)) ∧
      (∀ x ∈ normalizer (K : Set G), (∀ e ∈ E, x * e = e * x) →
          ∀ b ∈ K ⊓ centralizer (E : Set G), x * b = b * x) ∧
      (centralizer (K : Set G)).relIndex
          (normalizer (K : Set G) ⊓ centralizer (E : Set G)) ≤ 32

@[expose] def Asc82E8Stab : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K P : Subgroup G), IsOm6P K → IsSylow2Of P K →
    ∀ (E : Subgroup G) (z ν : G), IsElemAb2 E 3 → E ≤ K → z ∈ centerIn P → z ∈ E →
      ν ∈ K → orderOf ν = 3 → ν ∈ normalizer (E : Set G) →
      (∀ e ∈ E, ν * e = e * ν → e = 1 ∨ e = z) → ¬ (P ≤ normalizer (E : Set G)) →
      ∀ Y : Subgroup G, Nat.card Y = 128 → Y ⊓ centralizer (K : Set G) = ⊥ →
        Y ≤ normalizer (K : Set G) → Y ≤ normalizer (P : Set G) →
        Y ≤ normalizer (E : Set G) →
          ∃ B : Subgroup G, IsNormalE16In Y B ∧ ∃ y ∈ Y, y ∉ B ∧ ∀ b ∈ B, y * b = b * y

end CFSG.OddStandard.SmallF3.Omega
