module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FAt
public import CFSG.LieType.ChevTwo.Main
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142MClose
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3ChevSimple
import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FParMin
import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FParAbs
import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FParQuot
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma123c
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142Main

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141FPar

open CFSG.Open

section Cert


theorem parityModel_holds : I141F.ParityModel := by
  intro p hp hp2 Γ _ _ H E J hHn hO hchev hE hJ
  haveI := hHn
  haveI : Fact p.Prime := ⟨hp⟩
  have hJ' := hJ
  obtain ⟨hJX, hJsn, -, -⟩ := hJ'
  have hJH : J ≤ H := hJX.trans inf_le_left
  have hperf : ⁅J, J⁆ = J :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53Ns.glaPComponent_perfect hJ
  have hQJ : GLAPPrimeCoreOf p J ≤ J := Subgroup.map_subtype_le _
  have hQn : ((GLAPPrimeCoreOf p J).subgroupOf J).Normal := inferInstance
  have hQp : Nat.Coprime p (Nat.card ↥(GLAPPrimeCoreOf p J)) :=
    I142.coprime_card_glaPPrimeCoreOf p J
  have hcard := card_zBar (hQJ.trans hJH) hO hQp
  rw [← hcard]
  have hPperf := zBar_perfect hJH hperf
  by_cases hab : ∃ a b : ↥H ⧸ Subgroup.center ↥H, a * b ≠ b * a
  · haveI hsimp : IsSimpleGroup (↥H ⧸ Subgroup.center ↥H) :=
      CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.isSimpleGroup_of_isChevSimple_two hchev
    have hĒ : IsElemAbelian p (E.map (conjQ H)) := I142.isElemAbelian_map_of (conjQ H) hE
    have hsn : IsSubnormal (zBar H J) (I142.centFix (E.map (conjQ H))) :=
      isSubnormal_zBar_centFix hJsn
    have hPL : zBar H J ≤ GLALayer (I142.centFix (E.map (conjQ H))) :=
      I142.lieSemisimpleCentE_of_residuals I142.residualCyc_holds I142M.residualNonCyc_holds
        _ hsimp hab hchev p hp hp2 _ hĒ _ hsn.le hPperf
    have hres := zBar_res hJH fun N hN hNn hc => eq_of_normal_of_coprime_relIndex hp hJ hN hNn hc
    have hMc := commute_of_pPrime_normal_of_le_layer hsn hPperf hPL hres (zBar_mono hQJ)
      (zBar_normal hQJ hJH hQn) (by rw [hcard]; exact hQp)
    have hO2 : pCoreOf 2 (I142.centFix (E.map (conjQ H))) = ⊥ := by
      rw [← autCentralizer_eq_centFix]
      exact CFSG.LieType.ChevTwo.chev2CoreCent_of_leaves _ hsimp hab
        (CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma123.isChevTwo_of_isChevSimple_two hchev)
        p hp hp2 _ hĒ.isPGroup
    exact odd_card_of_commute_of_isSubnormal hsn hO2 (zBar_mono hQJ) hMc
  · push Not at hab
    have hbot : zBar H J = ⊥ := by
      rw [← hPperf, eq_bot_iff, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hab a b
    have hQbot : zBar H (GLAPPrimeCoreOf p J) = ⊥ :=
      le_bot_iff.mp (by rw [← hbot]; exact zBar_mono hQJ)
    rw [hQbot, Subgroup.card_bot]
    exact odd_one

end Cert

end CFSG.LocalAnalysis.GLTheoremA.I141FPar

end
