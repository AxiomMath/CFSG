module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisCenter
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisOut
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamDSigma
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamDOmega
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubCenter
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisRank
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.AGLEmbedding
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedClassicalModel)

theorem heisD_noHeisAut_of_omegaModel
    {L : Type} [Group L] [Finite L] (hperf : Group.IsPerfect L) (hrk : OddRankLeThree L)
    (hsimple : IsSimpleGroup (L ⧸ Subgroup.center L)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hZp : ¬ p ∣ Nat.card (Subgroup.center L)) {t : StatedLieTag} {n f : ℕ}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus)
    (hmodel : StatedClassicalModel (L ⧸ Subgroup.center L) t n 2 f) :
    NoHeisAut p (L ⧸ Subgroup.center L) := by
  haveI := hperf
  haveI := hsimple
  have hp2 : p ≠ 2 := by omega
  have htc : t ∈ CFSG.Blueprint.classicalTags := by
    rcases ht with rfl | rfl <;> decide
  have hlie : CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) t n 2 f := Or.inl ⟨htc, hmodel⟩
  have hL : t ≠ .PSL := by rcases ht with rfl | rfl <;> decide
  have hU : t ≠ .PSU := by rcases ht with rfl | rfl <;> decide
  have hT : t ≠ .Tits := by rcases ht with rfl | rfl <;> decide
  obtain ⟨hCyc, hout⟩ :=
    heis_out_data hp hp5 hlie hT (fun h => absurd h hL) (fun h => absurd h hU)
  have hf : 1 ≤ f := hmodel.1.2.1
  obtain ⟨ha, N, hN⟩ := heisD_exists_sigmaModel_sylow_of_omegaModel ht hmodel hp hp2
  refine heisD_noHeisAut_of_sigmaModel_sylow hp hp5 (heis_conj_injective L) hCyc
    (fun A hA hAq => heis_rank_quotient hrk hp hp2 hZp A hA hAq) ha hN fun h => ?_
  obtain ⟨f₀, rfl⟩ := hout h
  refine ⟨2 ^ f₀, by rw [pow_mul'], fun hd => ?_, ?_⟩
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  · have hf₀ : 1 ≤ f₀ := by
      rcases Nat.eq_zero_or_pos f₀ with h0 | h0
      · rw [h0, mul_zero] at hf
        omega
      · exact h0
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) hf₀

theorem heisCoreOn_idxD_of_oddCenterRest
    (hZ : OddCenterRest) : HeisCoreOn IdxD := by
  intro L _ _ hperf hodd hrk hsimple d hd e p hp hp5
  left
  obtain ⟨d, hv⟩ := d
  cases d
  case D r q =>
    have hq2 : q.p = 2 := hd
    have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hq2 e
    rw [hq2] at hmodel
    have hZp := heis_not_dvd_center_rest hZ ⟨hperf.commutator_eq_top, hsimple⟩ hodd
      (Or.inr (Or.inl ⟨⟨_, hv⟩, hd, ⟨e⟩⟩)) hp hp5
    exact heisD_noHeisAut_of_omegaModel hperf hrk hsimple hp hp5 hZp (Or.inl rfl) hmodel
  all_goals exact hd.elim

theorem heisCoreOn_idxTwistedD_of_oddCenterRest
    (hZ : OddCenterRest) : HeisCoreOn IdxTwistedD := by
  intro L _ _ hperf hodd hrk hsimple d hd e p hp hp5
  left
  obtain ⟨d, hv⟩ := d
  cases d
  case twistedD r q =>
    have hq2 : q.p = 2 := hd
    have hmodel :=
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hq2 e
    rw [hq2] at hmodel
    have hZp := heis_not_dvd_center_rest hZ ⟨hperf.commutator_eq_top, hsimple⟩ hodd
      (Or.inr (Or.inr (Or.inl ⟨⟨_, hv⟩, hd, ⟨e⟩⟩))) hp hp5
    exact heisD_noHeisAut_of_omegaModel hperf hrk hsimple hp hp5 hZp (Or.inr rfl) hmodel
  all_goals exact hd.elim

theorem heisCoreOn_idxD
    (hGA : CFSG.Open.GriessAllModelsStatement) : HeisCoreOn IdxD :=
  heisCoreOn_idxD_of_oddCenterRest (oddCenterRest_of_griess hGA)

theorem heisCoreOn_idxTwistedD
    (hGA : CFSG.Open.GriessAllModelsStatement) : HeisCoreOn IdxTwistedD :=
  heisCoreOn_idxTwistedD_of_oddCenterRest (oddCenterRest_of_griess hGA)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
