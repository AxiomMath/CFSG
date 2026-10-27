module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

@[expose] def KFactSmallThreeOrders : Prop :=
  ∀ (K : Type) [Group K], (IsSmallUnitary 3 K → Nat.card K = 6048) ∧
    (IsLinThreeFour K → Nat.card K = 20160) ∧ (IsSmallLinTwo 3 K → Nat.card K = 360)

@[expose] def KFactL34OuterGen : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsLinThreeFour K → ∀ T : Sylow 3 K, ∀ f : MulAut K,
    f ^ 3 = 1 → f ∉ (MulAut.conj : K →* MulAut K).range →
    (∀ t ∈ (T : Subgroup K), f t ∈ (T : Subgroup K)) → ∀ S : Subgroup K,
    (∀ k : K, f k = k → k ∈ S) → Subgroup.normalizer ((T : Subgroup K) : Set K) ≤ S → S = ⊤

@[expose] def KFactL34AutExp : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsLinThreeFour K → ∀ f : MulAut K,
    (∃ n : ℕ, f ^ 3 ^ n = 1) → f ^ 3 = 1

@[expose] def KFactJ3CoverA6 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Open.IsQuasisimple X →
    Nonempty (X ⧸ Subgroup.center X ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) →
    ∀ z ∈ Subgroup.center X, orderOf z = 3 →
    ∀ (A : Subgroup X) (L : Type) [Group L], IsAltTwoP 3 L → ∀ f : A →* L,
      Function.Surjective f →
    ∃ U B : Subgroup X, IsElemAbelian 3 U ∧ Nat.card U = 9 ∧ z ∈ U ∧
      B ≤ Subgroup.centralizer (U : Set X) ∧ (∃ t ∈ B, orderOf t = 3 ∧ t ∉ U) ∧
      ∀ Y : Subgroup X, B ≤ Y → (∃ S : Sylow 3 X, (S : Subgroup X) ≤ Y) → Y = ⊤

theorem card_of_isAltTwoP_three {K : Type} [Group K] (h : IsAltTwoP 3 K) : Nat.card K = 360 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  decide

theorem not_l34_and_not_a6_of_u33 (hO : KFactSmallThreeOrders) {K : Type} [Group K]
    (h : IsSmallUnitary 3 K) : ¬ IsLinThreeFour K ∧ ¬ IsAltTwoP 3 K := by
  have h1 := (hO K).1 h
  refine ⟨fun h2 => ?_, fun h2 => ?_⟩
  · have := (hO K).2.1 h2
    omega
  · have := card_of_isAltTwoP_three h2
    omega

theorem not_l34_of_a6 (hO : KFactSmallThreeOrders) {K : Type} [Group K] (h : IsAltTwoP 3 K) :
    ¬ IsLinThreeFour K := fun h2 => by
  have h1 := card_of_isAltTwoP_three h
  have := (hO K).2.1 h2
  omega

theorem not_spl_of_l34 (hO : KFactSmallThreeOrders) {K : Type} [Group K]
    (h : IsLinThreeFour K) : ¬ IsSPLFamily 3 K := by
  have h1 := (hO K).2.1 h
  rintro (h2 | h2 | ⟨-, h2⟩)
  · have := (hO K).2.2 h2
    omega
  · have := (hO K).1 h2
    omega
  · have := card_of_isAltTwoP_three h2
    omega

end CFSG.AGLEmbedding
