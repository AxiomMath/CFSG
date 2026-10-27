module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthPlusAut
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthPlusCover
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthPlusTransfer
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubCenter
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194OmegaPlanes

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthPlus
open scoped commutatorElement

namespace OrthPlus

theorem four_le_pRank_three_of_equiv {A : Type} [Group A] [Finite A] {Y : Subgroup A}
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (ρ : ↥(orthElementaryGroup (quadPlus 4 K)) ≃* ↥Y) : 4 ≤ CFSG.Open.pRank 3 Y := by
  have h := CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven.four_le_pRank_three_omegaPlus
    (K := K) (le_refl 4)
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
    ← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3)
      ((statedProjOmegaPlusEquiv (by norm_num)).trans ρ)]
  exact h

end OrthPlus

theorem parabCommOn_idxD_of
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    ParabCommOn (CFSG.AGLEmbedding.IsLieOf CFSG.AGLEmbedding.IdxD) := by
  intro A _ _ Y P p hp hp2 hY h2 hF hpar hne hna
  obtain ⟨r, K, _, _, _, D, ρ, hr4, hD, hD1, hρ⟩ :=
    exists_flag_setup (oddCenterRest_of_griess hGA) hY h2 hF hpar hne
  by_cases h43 : r = 4 ∧ p = 3
  · obtain ⟨rfl, rfl⟩ := h43
    exact Or.inr (four_le_pRank_three_of_equiv ρ)
  refine Or.inl ?_
  have hPY : P ≤ Y := hpar.1
  have hp_odd : Odd p := hp.odd_of_ne_two hp2
  have hr3 : 3 ≤ r := by omega
  have hD' : ∀ d ∈ D, d ≤ r := fun d hd => (hD d hd).2
  have hD1' : ∀ d ∈ D, 1 ≤ d := fun d hd => (hD d hd).1
  have ht : D.sup id = 0 ∨ D.sup id ∈ D := sup_eq_zero_or_mem D
  have hDt : ∀ d ∈ D, d ≤ D.sup id := fun d hd => Finset.le_sup (f := id) hd
  obtain ⟨m, htm⟩ : ∃ m, D.sup id + m = r :=
    ⟨r - D.sup id, by have := Finset.sup_le (f := id) (a := r) hD'; omega⟩
  have hm : m = 0 ∨ 2 ≤ m := eq_zero_or_two_le hr3 hD1 ht hDt htm
  have hblk : (∃ b ∈ D, 2 ≤ b - predCut D b) ∨ 2 ≤ m :=
    exists_block_of_nonabelian (ρ := ρ) (hρ := hρ) hPY hD1' hDt hD' ht htm hm hna
  have hsl : ∀ (b : ↥(Subgroup.normalizer (Y : Set A))) (k : ℕ), (b : A) ^ p ^ k = 1 →
      IsSemilinear (autHom ρ b) := by
    intro b k hb
    rcases hr4.eq_or_lt with hr | hr5
    · subst hr
      have h4 : p ≠ 4 := by
        rintro rfl
        exact absurd hp (by norm_num)
      have : 3 < p := by
        have := hp.two_le
        have h3 : p ≠ 3 := fun h => h43 ⟨rfl, h⟩
        omega
      exact isSemilinear_of_pow_eq_one_four hp this _ (autHom_pow_eq_one ρ b hb)
    · exact isSemilinear_of_five_le (by omega) _
  intro b₁ b₂ ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ ⟨k₃, hk₃⟩ hb₁Y hb₂Y hb₁P hb₂P hW₁ hW₂ y hy
  let β₁ : ↥(Subgroup.normalizer (Y : Set A)) := ⟨b₁, hb₁Y⟩
  let β₂ : ↥(Subgroup.normalizer (Y : Set A)) := ⟨b₂, hb₂Y⟩
  have hN₁ : NormFix hD' ht htm (autHom ρ β₁) :=
    normFix_autHom (ρ := ρ) (hρ := hρ) hPY hr3 hD1' hDt hm hb₁Y hb₁P hW₁
  have hN₂ : NormFix hD' ht htm (autHom ρ β₂) :=
    normFix_autHom (ρ := ρ) (hρ := hρ) hPY hr3 hD1' hDt hm hb₂Y hb₂P hW₂
  have hoc : Odd (orderOf ⁅autHom ρ β₁, autHom ρ β₂⁆) := by
    rw [← map_commutatorElement]
    exact odd_orderOf_autHom ρ ⁅β₁, β₂⁆ hp_odd hk₃
  have hcomm := orthModelComm hr3 hD hD1 ht hDt htm hblk (hsl β₁ k₁ hk₁) (hsl β₂ k₂ hk₂)
    (odd_orderOf_autHom ρ β₁ hp_odd hk₁) (odd_orderOf_autHom ρ β₂ hp_odd hk₂) hoc hN₁ hN₂
  exact centralizes_of_autHom_eq_one ρ ⁅β₁, β₂⁆ (by rw [map_commutatorElement]; exact hcomm) y hy

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm
