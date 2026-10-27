module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34PushUpL34
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFCover
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFAlpha
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFBeta

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem d1SmallPushUpL34_of_ff (hFF : CitedFFL34BestOffender) : D1SmallPushUpL34 := by
  intro G _ _ p P M H R Rbar K hd z hz _ hp3 hL hOR _ V hV hRV
  subst hp3
  have hV1 : V ≠ ⊥ := fun h => twoLocal_pCoreOf_ne_bot hd.cfg.ext.maxTwoLocal_H.1
    (le_bot_iff.mp (h ▸ hd.twoCore_le_of_isSylowTwoOf hV))
  have key : ∀ C : Subgroup G, C ≤ V → C ≠ ⊥ → (C.subgroupOf V).Characteristic →
      (∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (C : Set G), ∃ ha : a ∈ H,
        QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k) →
      ∃ C : Subgroup G, C ≤ V ∧ C ≠ ⊥ ∧ (C.subgroupOf V).Characteristic ∧
        (∀ h ∈ H, ∃ a ∈ H ⊓ Subgroup.normalizer (C : Set G), ∃ b ∈ H ⊓ M, h = a * b) ∧
        (∀ t ∈ d1LiftX 3 H R K, t ≠ 1 → ∀ s ∈ d1LiftX 3 H R K, s ≠ 1 →
          ∃ n ∈ (H ⊓ Subgroup.normalizer (C : Set G)) ⊓ Subgroup.normalizer (R : Set G),
            n * z * n⁻¹ = z ∧ (∀ x ∈ d1LiftX 3 H R K, n * x * n⁻¹ ∈ d1LiftX 3 H R K) ∧
            n * t * n⁻¹ = s) := by
    intro C hCV hC1 hchar hcov
    have hRC : R ≤ Subgroup.normalizer (C : Set G) := by
      have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (H := V) (C.subgroupOf V)
      rw [Subgroup.map_subgroupOf_eq_of_le hCV] at h1
      exact hRV.trans h1
    exact ⟨C, hCV, hC1, hchar, hd.factor_of_l34Cover hcov,
      hd.trans_of_l34Cover hz hL hOR inf_le_left (le_inf hd.cfg.ext.le_H hRC) hcov⟩
  by_cases hα : ∀ A : Subgroup G, IsMaxElemAbelian V A → ∀ a ∈ A, ∃ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ ∈
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3))
  · exact key (thompsonJ V) (B6.thompsonJ_le V) (Setup.thompsonJ_ne_bot hV.2.1 hV1)
      (Setup.characteristic_thompsonJ V) (hd.cover_thompsonJ hV hα)
  · push Not at hα
    obtain ⟨A, hA, a, haA, haC⟩ := hα
    exact key (omegaOneCenterOf V) (Setup.omegaOneCenterOf_le V)
      (Setup.omegaOneCenterOf_ne_bot hV.2.1 hV1) (Setup.characteristic_omegaOneCenterOf V)
      (hd.cover_omegaOneCenterOf hFF hL hV hA haA haC)

end CFSG.AGLEmbedding
