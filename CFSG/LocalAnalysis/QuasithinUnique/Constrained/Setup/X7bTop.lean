module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bCovers
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.TopDefs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExterior

public section

namespace CFSG.QuasithinUnique.Setup.X7b

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Family
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

@[expose] def SimpleSummandsStable {P M : Type} [Group P] [AddCommGroup M] [Module (ZMod 2) M]
    (π : P →* (M ≃ₗ[ZMod 2] M)) (A : Subgroup (M ≃ₗ[ZMod 2] M)) : Prop :=
  ∃ (ι : Type) (U : ι → Submodule (ZMod 2) M), iSupIndep U ∧ (⨆ i, U i) = ⊤ ∧ ∀ i,
    U i ≠ ⊥ ∧ (∃ x ∈ U i, ∃ g, π g x ≠ x) ∧ (∀ g, ∀ x ∈ U i, π g x ∈ U i) ∧
    (∀ W : Submodule (ZMod 2) M, W ≤ U i → (∀ g, ∀ x ∈ W, π g x ∈ W) → W = ⊥ ∨ W = U i) ∧
    ∀ a ∈ A, ∀ x ∈ U i, a x ∈ U i

@[expose] def UniqueSylowOddDiagramCoset : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 2 ≤ f → Nat.card K = 2 ^ f →
    ∀ H S : Subgroup (MulAut (StatedProj (StatedSp 2 K))),
      CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSp 2 K)) ≤ H →
      S ≤ H →
      CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSp 2 K)) ⊔ S = H →
      IsSylowTwoOf S H → (∃! M : Subgroup ↥H, IsCoatom M ∧ S.subgroupOf H ≤ M) →
      ∃ s ∈ S, ∃ (g : StatedSp 2 K) (j : ℕ), Odd j ∧ 1 ≤ j ∧ j < 2 * f ∧
        s = spInner 2 K g * exceptionalAut K ^ j

@[expose] def DiagramNormalizerExcludesOffenders : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 2 ≤ f → Nat.card K = 2 ^ f →
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
      (π : StatedProj (StatedSp 2 K) →* (M ≃ₗ[ZMod 2] M)), Function.Injective π →
      ∀ (b : M ≃ₗ[ZMod 2] M) (g₀ : StatedSp 2 K) (j : ℕ), Odd j → 1 ≤ j → j < 2 * f →
        (∀ x, b * π x * b⁻¹ = π ((spInner 2 K g₀ * exceptionalAut K ^ j) x)) →
        ∀ A : Subgroup (M ≃ₗ[ZMod 2] M),
          (∀ a ∈ A, ∀ x, ∃ y, a * π x * a⁻¹ = π y) → CFSG.IsElementaryAbelian 2 A → A ≠ ⊥ →
          SimpleSummandsStable π A →
          Nat.card A * Nat.card {m : M // ∀ a ∈ A, a m = m} < Nat.card M

@[expose] def ActualSymplecticFourData : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H T M E : Subgroup (MulAut V)), FFHyp V H T M E →
    ¬ Group.IsSolvable H → ∀ L : Subgroup (MulAut V), IsComp L H →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 2 ≤ f → Nat.card K = 2 ^ f →
    ∀ _θ : ↥L ≃* StatedProj (StatedSp 2 K),
      ∃ (HD SD : Subgroup (MulAut (StatedProj (StatedSp 2 K)))) (W : Type) (_ : AddCommGroup W)
        (_ : Module (ZMod 2) W) (_ : Finite W) (π : StatedProj (StatedSp 2 K) →* (W ≃ₗ[ZMod 2] W))
        (A : Subgroup (W ≃ₗ[ZMod 2] W)),
        CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSp 2 K)) ≤ HD ∧
        SD ≤ HD ∧
        CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSp 2 K)) ⊔ SD =
          HD ∧
        IsSylowTwoOf SD HD ∧ (∃! M' : Subgroup ↥HD, IsCoatom M' ∧ SD.subgroupOf HD ≤ M') ∧
        Function.Injective π ∧ (∀ a ∈ A, ∀ x, ∃ y, a * π x * a⁻¹ = π y) ∧
        CFSG.IsElementaryAbelian 2 A ∧ A ≠ ⊥ ∧ SimpleSummandsStable π A ∧
        Nat.card W ≤ Nat.card A * Nat.card {w : W // ∀ a ∈ A, a w = w} ∧
        ∀ s ∈ SD, ∃ b : W ≃ₗ[ZMod 2] W, ∀ x, b * π x * b⁻¹ = π (s x)

theorem charP_two_of_card_pow {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    CharP K 2 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])

theorem original_minimal_parabolic_FF_actor_excludes_PSp4_components
    (h15 : UniqueSylowOddDiagramCoset) (h27 : DiagramNormalizerExcludesOffenders)
    (hdata : ActualSymplecticFourData) {V : Type} [CommGroup V] [Finite V]
    {H T M E : Subgroup (MulAut V)} (hF : FFHyp V H T M E) (hns : ¬ Group.IsSolvable H)
    {L : Subgroup (MulAut V)} (hL : IsComp L H) {f : ℕ} (hf : 2 ≤ f) :
    ¬ StatedClassicalModel (CQ L) .PSp 2 2 f := by
  intro hmodel
  obtain ⟨hadm, K, hK, hKfin, hcard, ⟨e⟩⟩ := hmodel
  have : CharP K 2 := charP_two_of_card_pow hcard
  have hQ : CFSG.IsQuasisimple ↥L := isQuasisimple_of_isComp hL
  have hbij := (perfect_full_central_covers_trivial hQ
    (Or.inl ⟨f, hf, Or.inl ⟨by decide, ⟨hadm, K, hK, hKfin, hcard, ⟨e⟩⟩⟩⟩)).2
  let θ : ↥L ≃* StatedProj (StatedSp 2 K) :=
    (MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center ↥L)) hbij).trans e
  obtain ⟨HD, SD, W, _, _, _, π, A, hInn, hSD, hHD, hSyl, huniq, hfaith, hnorm, hAe, hA1, hsum,
    hoff, hlift⟩ := hdata V H T M E hF hns L hL f K hf hcard θ
  obtain ⟨s, hs, g₀, j, hj, hj1, hj2, rfl⟩ := h15 f K hf hcard HD SD hInn hSD hHD hSyl huniq
  obtain ⟨b, hb⟩ := hlift _ hs
  have := h27 f K hf hcard W π hfaith b g₀ j hj hj1 hj2 hb A hnorm hAe hA1 hsum
  omega

theorem noPSp4Component
    (h15 : UniqueSylowOddDiagramCoset) (h27 : DiagramNormalizerExcludesOffenders)
    (hdata : ActualSymplecticFourData) : CFSG.QuasithinUnique.Setup.Top.NoPSp4Component :=
  fun _ _ _ _ _ _ _ hF hns _ _ hL _ hf =>
    original_minimal_parabolic_FF_actor_excludes_PSp4_components h15 h27 hdata hF hns hL hf

end CFSG.QuasithinUnique.Setup.X7b
