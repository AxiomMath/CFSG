module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocIdx2
public import CFSG.Sporadic.B
public import CFSG.Monster.Existence.BabyOrder
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def BPair (G : Type) [Group G] (L K : Subgroup G) (u : G) : Prop :=
  u ∈ L ∧ orderOf u = 2 ∧ K ≤ L ∧ (∀ k ∈ K, k * u = u * k) ∧ Nat.card K = 2 * ordTwistedE6 2

structure BabyCoverFacts : Prop where
  cover : ∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G) (u : G), IsSporadic L .B →
    BPair G L K u →
      IsIdx2Cover ↥(L ⊓ centralizer ({u} : Set G)) (K.subgroupOf (L ⊓ centralizer ({u} : Set G)))
  aut : ∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G) (u : G), IsSporadic L .B →
    BPair G L K u → ∀ α : MulAut ↥K, ∃ c ∈ L ⊓ centralizer ({u} : Set G),
      ∀ k : K, ((α k : K) : G) = c * (k : G) * c⁻¹
  sylow : ∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G) (u : G), IsSporadic L .B →
    BPair G L K u → ∀ S : Subgroup G, S ≤ L ⊓ centralizer ({u} : Set G) → IsPGroup 2 S →
      (∀ S' : Subgroup G, S' ≤ L ⊓ centralizer ({u} : Set G) → IsPGroup 2 S' → S ≤ S' →
        S' = S) → ∀ z ∈ S, (∀ s ∈ S, z * s = s * z) → z ∈ K
  overgroups : ∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G) (u : G), IsSporadic L .B →
    BPair G L K u → ∀ X : Subgroup G, K ≤ X → X ≤ L →
      X ≤ L ⊓ centralizer ({u} : Set G) ∨ X = L

theorem factorization_two_cent_b : (2 * (2 * ordTwistedE6 2)).factorization 2 = 38 := by
  have h : 2 * (2 * ordTwistedE6 2) = 2 ^ 38 * 1113694156575 := by
    unfold ordTwistedE6
    norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem factorization_two_monsterBabyOrder : monsterBabyOrder.factorization 2 = 41 := by
  have h : monsterBabyOrder = 2 ^ 41 * 1889375872099856765625 := by
    unfold monsterBabyOrder
    norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem b_isSimpleGroup_of_isSporadic {Y : Type} [Group Y] (h : IsSporadic Y .B) :
    IsSimpleGroup Y := by
  obtain ⟨e⟩ := h
  have e' : Y ≃* NativeSporadic.B := e
  exact @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.B.fam_b_simplicity e'

theorem b_card_of_isSporadic {Y : Type} [Group Y] (h : IsSporadic Y .B) :
    Nat.card Y = monsterBabyOrder := by
  obtain ⟨e⟩ := h
  have e' : Y ≃* NativeSporadic.B := e
  rw [Nat.card_congr e'.toEquiv]
  exact CFSG.Monster.Existence.card_nativeB

theorem b_exists_not_commute {Y : Type} [Group Y] (h : IsSporadic Y .B) :
    ∃ a b : Y, a * b ≠ b * a := by
  have hs := b_isSimpleGroup_of_isSporadic h
  by_contra hc
  push Not at hc
  let _ : CommGroup Y := { (inferInstance : Group Y) with mul_comm := hc }
  have hp := IsSimpleGroup.prime_card (α := Y)
  rw [b_card_of_isSporadic h] at hp
  unfold monsterBabyOrder at hp
  norm_num at hp

end CFSG.EvenSporadicStandard.Solomon78
