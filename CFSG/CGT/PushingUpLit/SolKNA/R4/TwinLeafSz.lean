module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafAut
public import CFSG.ClassicalInvolution.SmallCases.NobqSz
public import CFSG.LieType.Suzuki.SuzukiOuterCyclic
public import CFSG.LieType.Ree.SuzukiSimple
public import Certificates.Certificate113
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeDefs
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocCyc4
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocal
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinNoQ16E4Check
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerpCentral
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerpMainR
public import CFSG.ClassicalInvolution.Asc77.AscT8X4
public import CFSG.ClassicalInvolution.Asc77.AscT8YA3
public import CFSG.ClassicalInvolution.AschTight.S19BCSW
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.InnerOvergroup
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Reduction
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinResF
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinResLift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
public import CFSG.ClassicalInvolution.Q3.Q3AMDBStmt
public import CFSG.ClassicalInvolution.Q3.Q3T6BSymEx
public import CFSG.ClassicalInvolution.Q3.Q3T6DCfg
public import CFSG.ClassicalInvolution.Q3.Q3T6DPart1
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenSDEnd
public import CFSG.ClassicalInvolution.Q3.Q3T8B10
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T01
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T02
public import CFSG.ClassicalInvolution.Q3.Q3T8P26TH01
public import CFSG.ClassicalInvolution.Q3.TA3SOLCore
public import CFSG.ClassicalInvolution.Q3.TA3SOLCoreRank
public import CFSG.ClassicalInvolution.Q3.TA3SmallModelM12
public import CFSG.ClassicalInvolution.Q3.TL3S8Gold
public import CFSG.ClassicalInvolution.Q3.TL3S8Sd
public import CFSG.ClassicalInvolution.Q3.TL3T28
public import CFSG.ClassicalInvolution.Q3.TL4Conn274M
public import CFSG.ClassicalInvolution.Q3.TL4D1Basic
public import CFSG.ClassicalInvolution.Q3.TL4Sep2FB
public import CFSG.ClassicalInvolution.Q3.TL4SepAlphaB
public import CFSG.ClassicalInvolution.Q3.TL4TwistTw
public import CFSG.ClassicalInvolution.SmallCases.A7T22Setup
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8Lift
public import CFSG.Foundations
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.GH74.GLS.IVK.L2.Lemma19c
public import CFSG.GH74.GLS.IVK.L2.SylowAux
public import CFSG.GH74.GLS.IVK.L2.Torus
public import CFSG.GH74.GLS.IVK.L2.TorusGeneral
public import CFSG.GH74.GLS.Stage4.RestP93
public import CFSG.GH74.GLS.Stage4.RestSetup
public import CFSG.GH74.Generic.S3.LeavesFine
public import CFSG.GH74.Generic.S3.Lem37
public import CFSG.GH74.Generic.S45.LEvSporGen
public import CFSG.Goldschmidt.Steps.G310Core2
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.Goldschmidt75.TheoremB
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingCore
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingEscape
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingInherit
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingOddQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingThreeOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.Permutation.BurnsideSchur
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup
public import CFSG.Timmesfeld.Moufang.Three

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Nobq
open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.CGT.PushingUpLit.SolKNA.R4 CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall

theorem noQ16_suzukiMatrixGroup (m : ℕ) (hm : 0 < m) : NoQ16 (SuzukiMatrixGroup m) := by
  have hfin : Finite (SuzukiMatrixGroup m) := inferInstance
  refine noQ16_of_sylow (P := suzukiCoverRoot m) (suzukiCoverRoot_structure m hm).1
    (suzukiCoverRoot_index_odd m hm).not_two_dvd_nat ?_
  rintro x y ⟨hx4, -, -, -⟩
  apply hx4
  obtain ⟨a, b, rfl⟩ := suzukiCoverRootElement_surjective m x
  have h1 := suzukiCoverRootElement_sq' m hm a b
  have h2 := suzukiCoverRootElement_sq' m hm 0 (a * suzukiCoverTits m a)
  rw [show suzukiCoverRootElement m a b ^ 4 = (suzukiCoverRootElement m a b ^ 2) ^ 2 by
    rw [← pow_mul], h1, h2, zero_mul, suzukiCoverRootElement_zero_zero]

theorem exists_noncomm_suzukiMatrixGroup (m : ℕ) (hm : 0 < m) :
    ∃ x y : SuzukiMatrixGroup m, x * y ≠ y * x := by
  obtain ⟨c, hc, -⟩ := exists_not_mem_commutator_values m hm (a := 1) one_ne_zero
  refine ⟨(suzukiCoverRootElement m 1 0 : SuzukiMatrixGroup m),
    (suzukiCoverRootElement m c 0 : SuzukiMatrixGroup m), fun h => ?_⟩
  have h' : suzukiCoverRootElement m 1 0 * suzukiCoverRootElement m c 0 =
      suzukiCoverRootElement m c 0 * suzukiCoverRootElement m 1 0 := Subtype.ext h
  have h2 := suzukiCoverRootElement_commutator m hm 1 0 c 0
  rw [h'] at h2
  have h3 : suzukiCoverRootElement m c 0 * suzukiCoverRootElement m 1 0 *
      suzukiCoverRootElement m 0 (1 * suzukiCoverTits m c + c * suzukiCoverTits m 1) =
      suzukiCoverRootElement m c 0 * suzukiCoverRootElement m 1 0 * 1 := by
    rw [mul_one]; exact h2.symm
  have h4 := mul_left_cancel h3
  rw [← suzukiCoverRootElement_zero_zero m] at h4
  exact hc (suzukiCoverRootElement_injective m 0 _ 0 0 h4).2


theorem noQ16_mulAut_of_suzukiModel {F : Type} [Group F] {p f : ℕ}
    (h : CFSG.Blueprint.SuzukiModel F p f) : NoQ16 (MulAut F) := by
  have hodd :=
    (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} F p f h).1.2.2
  obtain ⟨-, a, ha, L, hLf, hLfin, hf, hcard, ⟨e⟩⟩ := h
  have hK : Nat.card L = 2 ^ (2 * a + 1) := by rw [← hf]; exact hcard
  let e' : F ≃* SuzukiMatrixGroup a :=
    e.trans (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK)
  have hsimple : IsSimpleGroup F := by
    have := (CFSG.LieType.Ree.suzuki_simple (K := L) ha hK).2.2
    exact e.isSimpleGroup
  have hnc : ∃ x y : F, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := exists_noncomm_suzukiMatrixGroup a ha
    exact ⟨e'.symm x, e'.symm y, fun h' => hxy (e'.symm.injective (by simpa using h'))⟩
  exact noQ16_mulAut_of_odd_outer (center_eq_bot_of_simple hnc) hodd
    (NoQ16.of_injective e'.toMonoidHom e'.injective (noQ16_suzukiMatrixGroup a ha))

open CFSG.Blueprint in
theorem noQ16_mulAut_of_lieModel_twistedB2 {F : Type} [Group F] {f : ℕ}
    (h : LieModel F .twistedB2 0 2 f) : NoQ16 (MulAut F) := by
  rcases h with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact noQ16_mulAut_of_suzukiModel h


open CFSG.Blueprint in
theorem twinLeafR_sz8 {r n : ℕ} (hr : 4 ≤ r) :
    TwinLeafR r n fun F _ => LieModel F .twistedB2 0 2 3 :=
  twinLeafR_of_noQ16Aut hr fun _ _ hF => noQ16_mulAut_of_lieModel_twistedB2 hF

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
