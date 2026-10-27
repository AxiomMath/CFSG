module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yCommon
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yChar
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62ySetup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem sr629_five_le {f : ℕ} (hfp : f.Prime) (hf2 : f ≠ 2) (hf3 : f ≠ 3) : 5 ≤ f := by
  have h4 : f ≠ 4 := by
    rintro rfl
    norm_num at hfp
  have := hfp.two_le
  omega

theorem lemma629_of_interface (hS : Setting G) (hI : GL83SmallRankInterface G)
    (hK : KFactZAction629) : GL83SmallRankLemma629 G := by
  intro p P M x z T hf hcov h28 f hfp hf2 hfD
  have hp : p.Prime := hf.prime
  have hp2 : p ≠ 2 := hf.ne_two
  have : Fact f.Prime := ⟨hfp⟩
  have hfp' : f ≠ p := sr629_ne_prime hp hfp x hfD
  obtain ⟨hp35, hQ, hQ8, hfit⟩ := h28
  have hFab : IsElemAbelian f (smallRankF p f x) := sr629_isElemAbelian_omega_center f _
  have hFne : smallRankF p f x ≠ ⊥ :=
    sr629_omega_center_ne_bot hfp (CFSG.LieType.BorelTits.pCoreOf_isPGroup f _) hfD
  have hCF : centralizer ({x} : Set G) ≤ normalizer (smallRankF p f x : Set G) :=
    sr629_centralizer_le_normalizer_F hp x
  have hzx : z ∈ centralizer ({x} : Set G) := by
    refine mem_centralizer_singleton_iff.mpr ?_
    exact (mem_centralizer_iff.mp hf.central.centralizes x hf.point.mem).symm
  have hxx : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have hSC : smallRankS x T ≤ centralizer ({x} : Set G) := inf_le_right
  have hSF : smallRankS x T ≤ normalizer (smallRankF p f x : Set G) := hSC.trans hCF
  have hBC : zpowers x ⊔ zpowers z ≤ centralizer ({x} : Set G) :=
    sup_le (zpowers_le.mpr hxx) (zpowers_le.mpr hzx)
  have hBF : zpowers x ⊔ zpowers z ≤ normalizer (smallRankF p f x : Set G) := hBC.trans hCF
  have hzS : zpowers z ≤ normalizer (smallRankS x T : Set G) := hf.z_le_normalizer_S
  have hFM : smallRankF p f x ⊓ M = ⊥ := by
    rw [eq_bot_iff, ← hfit]
    exact inf_le_inf_right M (sr629_F_le_fitting hp hfp hf2 x)
  have hH2 : ∀ S₀ : Subgroup G, S₀ ≤ smallRankS x T → S₀ ≠ ⊥ →
      zpowers z ≤ normalizer (S₀ : Set G) →
      smallRankF p f x ⊓ centralizer (S₀ : Set G) = ⊥ := by
    intro S₀ hS₀S hS₀1 hzS₀
    have hNM : normalizer (S₀ : Set G) ≤ M := hI.prop614 p P M x z T hf S₀ hS₀S hS₀1 hzS₀
    rw [eq_bot_iff, ← hFM]
    exact inf_le_inf_left _ ((Subgroup.centralizer_le_normalizer _).trans hNM)
  have hH3 : smallRankF p f x ⊓ centralizer ({z} : Set G) = ⊥ := by
    have hNM : centralizer ({z} : Set G) ≤ M :=
      (sr628_centralizer_le_normalizer_zpowers z).trans (hf.normalizer_zpowers_le hS)
    rw [eq_bot_iff, ← hFM]
    exact inf_le_inf_left _ hNM
  have hrank3 : SmallRankInvolutionRankLE f 3 (smallRankS x T) (smallRankF p f x) :=
    smallRankInvolutionRankLE_of_localRank hfp _ _ (smallRank_localRank_le_three hS hfp hf2)
  have hrank2 : p = 3 →
      SmallRankInvolutionRankLE f 2 (smallRankS x T) (smallRankF p f x) := by
    intro hp3
    subst hp3
    exact smallRankInvolutionRankLE_of_localRank hfp _ _
      (localRank_le_two_of_three hS hf.situation hfp (sr629_five_le hfp hf2 hfp'))
  have hH6 : ¬ (p = 3 ∧ ∃ n : ℕ, rankThreeIsQ8CentralCyclic (smallRankS x T) n) := by
    rintro ⟨hp3, n, hn⟩
    subst hp3
    exact hf.fails ⟨rfl, Or.inr ⟨⟨n, hn⟩, hcov⟩⟩
  obtain ⟨⟨hcard, hinv⟩, ⟨hi5, hi3, hcen⟩, hA⟩ :=
    hK G p f hp hfp hp2 hf2 hfp' hp35 (smallRankS x T) (smallRankF p f x) z hf.S_isPGroup hFab
      hFne hf.central.pow_eq_one hf.central.ne_one hzS (sup_le hSF (le_sup_right.trans hBF)) hQ
      hQ8 hH2 hH3 hrank3 hrank2 hH6
  refine ⟨⟨hi5, hi3, hcen⟩, ?_, ?_, hFab, hcard, hinv⟩
  ·
    have hAS : pCoreOf 2 M ⊓ centralizer ({x} : Set G) ≤ smallRankS x T :=
      inf_le_inf hf.pCoreOf_two_le_T le_rfl
    have hzA : zpowers z ≤
        normalizer ((pCoreOf 2 M ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) := by
      rw [zpowers_le]
      refine Subgroup.inf_normalizer_le_normalizer_inf ⟨?_, Subgroup.le_normalizer hzx⟩
      exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hf.sylow_le hS hf.central.mem)
    have hcomm : ⁅pCoreOf 2 M ⊓ centralizer ({x} : Set G), zpowers z⁆ ≠ ⊥ := by
      rw [Subgroup.commutator_comm]
      exact sr629_commutator_pCoreOf_inf_centralizer_ne_bot hS hf.situation hf.point hf.central
    exact (hA _ hAS hzA hcomm).trans inf_le_left
  · exact smallRank_localRank_le_three hS hfp hf2

end CFSG.LocalAnalysis.RankThreeTheoremC
