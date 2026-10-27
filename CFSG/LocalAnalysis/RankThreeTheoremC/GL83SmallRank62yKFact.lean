module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yCommon
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yRank
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yBasic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem sr628_kfact_conclusion (hS : Setting G) (hI : GL83SmallRankInterface G)
    (hK : KFactZAction628) {p : ℕ} {P : Sylow p G}
    {M : Subgroup G} {x z : G} {T : Subgroup G} (hf : Prop627Failure G p P M x z T) {f : ℕ}
    (hfp : f.Prime) (hf2 : f ≠ 2) (hfp' : f ≠ p) {F₁ : Subgroup G} (hF₁ : IsPGroup f F₁)
    (hAF₁ : smallRankS x T ⊔ (zpowers x ⊔ zpowers z) ≤ normalizer (F₁ : Set G))
    (hF₁M : ¬ F₁ ≤ M) :
    (p = 3 ∨ p = 5) ∧ (p = 3 → Nonempty (↥(smallRankR x z T) ≃* QuaternionGroup 2)) ∧
      (p = 5 → smallRankIsQ8D8 (smallRankR x z T)) := by
  have : Fact f.Prime := ⟨hfp⟩
  have hSM : smallRankS x T ≤ M := hf.S_le_M
  have hBM : zpowers x ⊔ zpowers z ≤ M := hf.B_le_M hS
  have hAM : smallRankS x T ⊔ (zpowers x ⊔ zpowers z) ≤ normalizer (M : Set G) :=
    (sup_le hSM hBM).trans le_normalizer
  obtain ⟨N, hN⟩ : ∃ N : Subgroup G, N = F₁ ⊓ M := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Subgroup G, X = F₁ ⊓ normalizer (N : Set G) := ⟨_, rfl⟩
  have hNF : N ≤ F₁ := by rw [hN]; exact inf_le_left
  have hNM : N ≤ M := by rw [hN]; exact inf_le_right
  have hleN : ∀ K : Subgroup G, K ≤ F₁ → K ≤ M → K ≤ N := fun K h1 h2 => by
    rw [hN]; exact le_inf h1 h2
  have hmemN : ∀ g : G, g ∈ F₁ → g ∈ M → g ∈ N := fun g h1 h2 => by
    rw [hN]; exact ⟨h1, h2⟩
  have hXF : X ≤ F₁ := by rw [hX]; exact inf_le_left
  have hXnorm : X ≤ normalizer (N : Set G) := by rw [hX]; exact inf_le_right
  have hNX : N ≤ X := by rw [hX]; exact le_inf hNF le_normalizer
  have hNnorm : (N.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hNX).mpr hXnorm
  have hXN : ¬ X ≤ N := by
    have hlt : N < F₁ := lt_of_le_of_ne hNF fun h => hF₁M (h ▸ hNM)
    obtain ⟨y, hyF, hyN, hyn⟩ := sr628_exists_mem_normalizer_not_mem hF₁ hlt
    refine fun hXN => hyn (hXN ?_)
    rw [hX]
    exact ⟨hyF, hyN⟩
  have hXp : IsPGroup f X := hF₁.to_le hXF
  have hAN : smallRankS x T ⊔ (zpowers x ⊔ zpowers z) ≤ normalizer (N : Set G) := by
    rw [hN]
    exact (le_inf hAF₁ hAM).trans inf_normalizer_le_normalizer_inf
  have hAX : smallRankS x T ⊔ (zpowers x ⊔ zpowers z) ≤ normalizer (X : Set G) := by
    rw [hX]
    exact (le_inf hAF₁ (hAN.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hSzA : smallRankS x T ⊔ zpowers z ≤ smallRankS x T ⊔ (zpowers x ⊔ zpowers z) :=
    sup_le_sup_left le_sup_right _
  refine hK G p f hf.prime hfp hf.ne_two hf2 hfp' (smallRankS x T) X N z hf.S_isPGroup hXp hNX
    hNnorm hXN hf.central.pow_eq_one hf.central.ne_one hf.z_le_normalizer_S (hSzA.trans hAX)
    (hSzA.trans hAN) (hf.R_ne_bot hS) ?_ ?_ ?_ ?_
  ·
    intro S₀ hS₀S hS₀ne hzS₀ g hg
    obtain ⟨hgX, hgc⟩ := Subgroup.mem_inf.mp hg
    exact hmemN g (hXF hgX)
      (hI.prop614 p P M x z T hf S₀ hS₀S hS₀ne hzS₀ (centralizer_le_normalizer _ hgc))
  ·
    intro g hg
    obtain ⟨hgX, hgc⟩ := Subgroup.mem_inf.mp hg
    exact hmemN g (hXF hgX)
      (hf.normalizer_zpowers_le hS (sr628_centralizer_le_normalizer_zpowers z hgc))
  ·
    exact smallRankInvolutionRankLE_of_localRank hfp _ X (smallRank_localRank_le_three hS hfp hf2)
  ·
    intro hp3
    subst hp3
    have h5 : 5 ≤ f := by
      by_contra hlt
      have h4 : f = 4 := by have := hfp.two_le; omega
      exact absurd hfp (by rw [h4]; norm_num)
    exact smallRankInvolutionRankLE_of_localRank hfp _ X
      (localRank_le_two_of_three hS hf.situation hfp h5)

end CFSG.LocalAnalysis.RankThreeTheoremC
