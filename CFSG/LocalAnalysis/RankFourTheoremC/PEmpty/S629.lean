module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S628Rank
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yChar
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yRank
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.StrongMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (smallRankS smallRankR smallRankD smallRankF
  smallRankCenter Lemma628Concl Lemma629Concl KFactZAction629 sr629_ne_prime
  sr629_isElemAbelian_omega_center sr629_omega_center_ne_bot sr629_centralizer_le_normalizer_F
  sr629_F_le_fitting sr629_F_isPGroup smallRankInvolutionRankLE_of_localRank)

theorem stepL629_of_kfacts (hK : KFactZAction629) : StepL629 := by
  intro G _ _ p P M x z hS hx hz h614 T hT hcov h28 f hfp hf2 hfD
  have c : S62Config p P M x z T := ⟨hS, hx, hz, h614, hT⟩
  have hp : p.Prime := c.prime
  have hp2 : p ≠ 2 := c.ne_two
  have : Fact f.Prime := ⟨hfp⟩
  have hfp' : f ≠ p := sr629_ne_prime hp hfp x hfD
  obtain ⟨hp35, hQ, hQ8, hfit⟩ := h28
  have hFab : IsElemAbelian f (smallRankF p f x) := sr629_isElemAbelian_omega_center f _
  have hFne : smallRankF p f x ≠ ⊥ :=
    sr629_omega_center_ne_bot hfp (CFSG.LieType.BorelTits.pCoreOf_isPGroup f _) hfD
  have hCF : centralizer ({x} : Set G) ≤ normalizer (smallRankF p f x : Set G) :=
    sr629_centralizer_le_normalizer_F hp x
  have hSC : smallRankS x T ≤ centralizer ({x} : Set G) := inf_le_right
  have hSF : smallRankS x T ≤ normalizer (smallRankF p f x : Set G) := hSC.trans hCF
  have hBF : zpowers x ⊔ zpowers z ≤ normalizer (smallRankF p f x : Set G) :=
    c.B_le_centralizer.trans hCF
  have hzS : zpowers z ≤ normalizer (smallRankS x T : Set G) := c.z_le_normalizer_S
  have hFM : smallRankF p f x ⊓ M = ⊥ := by
    rw [eq_bot_iff, ← hfit]
    exact inf_le_inf_right M (sr629_F_le_fitting hp hfp hf2 x)
  have hH2 : ∀ S₀ : Subgroup G, S₀ ≤ smallRankS x T → S₀ ≠ ⊥ →
      zpowers z ≤ normalizer (S₀ : Set G) → smallRankF p f x ⊓ centralizer (S₀ : Set G) = ⊥ := by
    intro S₀ hS₀S hS₀1 hzS₀
    have hNM : normalizer (S₀ : Set G) ≤ M := c.normalizer_le hS₀S hS₀1 hzS₀
    rw [eq_bot_iff, ← hFM]
    exact inf_le_inf_left _ ((Subgroup.centralizer_le_normalizer (S₀ : Set G)).trans hNM)
  have hH3 : smallRankF p f x ⊓ centralizer ({z} : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hFM]
    exact inf_le_inf_left _ c.centralizer_le_M
  have hFp : IsPGroup f (smallRankF p f x) := sr629_F_isPGroup hfp x
  have hF2 : 2 ≤ CFSG.Open.pRank f (smallRankF p f x) :=
    s62_two_le_pRank_of_commutator c hfp hf2 hFp (hCF c.z_mem_centralizer) hSF
      fun S₀ h1 h2 h3 hFC => hFne ((inf_eq_left.mpr hFC).symm.trans (hH2 S₀ h1 h2 h3))
  have hFM' : ¬ smallRankF p f x ≤ M := fun h =>
    hFne ((inf_eq_left.mpr h).symm.trans hFM)
  have hrank3 : rankThreeLocalRank f G ≤ 3 :=
    s62_localRank_le_three hS h614 hfp hf2 hFp hF2 hFM' c.S_isPGroup c.S_le_M c.S_ne_bot
      c.B_le_normalizer_S (sup_le hSF hBF)
  obtain ⟨⟨hcard, hinv⟩, ⟨hi5, hi3, hcen⟩, hA⟩ :=
    hK G p f hp hfp hp2 hf2 hfp' hp35 (smallRankS x T) (smallRankF p f x) z c.S_isPGroup hFab
      hFne c.central.pow_eq_one c.central.ne_one hzS (sup_le hSF (le_sup_right.trans hBF)) hQ
      hQ8 hH2 hH3 (smallRankInvolutionRankLE_of_localRank hfp _ _ hrank3)
      (fun hp3 => absurd hp3 (by have := hS.p_ge; omega))
      (fun ⟨hp3, _⟩ => absurd hp3 (by have := hS.p_ge; omega))
  refine ⟨⟨hi5, hi3, hcen⟩, ?_, hrank3, hFab, hcard, hinv⟩
  have hAS : pCoreOf 2 M ⊓ centralizer ({x} : Set G) ≤ smallRankS x T :=
    inf_le_inf c.pCoreOf_two_le_T le_rfl
  have hzA : zpowers z ≤
      normalizer ((pCoreOf 2 M ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) := by
    rw [zpowers_le]
    refine Subgroup.inf_normalizer_le_normalizer_inf
      ⟨?_, Subgroup.le_normalizer c.z_mem_centralizer⟩
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hS.sylow_le c.central.mem)
  have hcomm : ⁅pCoreOf 2 M ⊓ centralizer ({x} : Set G), zpowers z⁆ ≠ ⊥ := by
    rw [Subgroup.commutator_comm]
    exact c.commutator_pCoreOf_ne_bot
  exact (hA _ hAS hzA hcomm).trans inf_le_left

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
