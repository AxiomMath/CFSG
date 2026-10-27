module

public import CFSG.Open.StatedDefs
import CFSG.RankThree.PartTwo.KFacts.AutPSp4Odd
import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.LieType.Chevalley.LangRootArithmetic
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.StronglyEmbedded.ParityCriterion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  (conjAut multiplier conjAut_mem_inner_of_isSquare)

theorem mem_range_conj_of_pow_eq_one {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (_hpq : p ≠ q)
    (α : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 (ZMod q)))) (hα : α ^ p = 1) :
    α ∈ (MulAut.conj : CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 (ZMod q)) →* MulAut _).range := by
  have hodd : ringChar (ZMod q) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hq2
  obtain ⟨A, σ, rfl⟩ := CFSG.RankThree.PartTwo.KFacts.psp4_odd_automorphism_normal_form hodd α
  have hσ : σ = 1 := RingEquiv.ext fun y =>
    DFunLike.congr_fun (RingHom.ext_zmod σ.toRingHom (RingHom.id _)) y
  subst hσ
  rw [map_one, mul_one] at hα ⊢
  obtain ⟨j, hj⟩ := hp.odd_of_ne_two hp2
  have hsq : conjAut 2 (ZMod q) A = conjAut 2 (ZMod q) (A ^ 2) ^ (j + 1) := by
    rw [map_pow, ← pow_mul]
    calc conjAut 2 (ZMod q) A = conjAut 2 (ZMod q) A ^ p * conjAut 2 (ZMod q) A := by
          rw [hα, one_mul]
      _ = conjAut 2 (ZMod q) A ^ (2 * (j + 1)) := by rw [← pow_succ, hj]; ring_nf
  rw [hsq]
  refine Subgroup.pow_mem _
    (conjAut_mem_inner_of_isSquare ⟨(multiplier 2 (ZMod q) A : ZMod q), ?_⟩) _
  rw [map_pow, Units.val_pow_eq_pow_val, sq]

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
