
module

public import CFSG.Certificates.Kernel.Th.Gen.Seed
public import CFSG.Certificates.Kernel.Th.Gen.Dce
public import CFSG.Certificates.Kernel.Th.Gen.Sylow2
public import CFSG.Certificates.Kernel.Th.Gen.Sylow3
public import CFSG.Certificates.Kernel.Th.Gen.Sylow5
public import CFSG.Certificates.Kernel.Th.Gen.Sylow7
public import CFSG.Certificates.Kernel.Th.Gen.Orders
public import CFSG.Certificates.Kernel.Th.Gen.Fwd
public import CFSG.Certificates.Kernel.Th.Gen.Gen
public import CFSG.Certificates.Kernel.Th.Gen.DceStruct
public import CFSG.Sporadic.Th.KernelInputsBase
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.Common.Generalize
import CFSG.Certificates.Kernel.Th.Spec.Big
import CFSG.Certificates.Kernel.Th.Spec.Dce
import CFSG.Certificates.Kernel.Th.Spec.DceHsw
import CFSG.Certificates.Kernel.Th.Spec.Seed
import CFSG.Certificates.Kernel.Th.Spec.Orders
import CFSG.Certificates.Kernel.Th.Spec.GenSBase
import CFSG.Certificates.Kernel.Th.Spec.FwdBase
import CFSG.Certificates.Kernel.Th.Spec.SylowAsm
import CFSG.Certificates.Kernel.Th.Spec.SylowOrbitBase
import CFSG.Certificates.Kernel.Th.Spec.DceStrMain
import CFSG.Certificates.Kernel.Th.Spec.Sylow2Base
import all CFSG.Sporadic.Th.Max3.AllConjBase
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all CFSG.Sporadic.Bridge.Common
public import CFSG.Certificates.Kernel.Th.S.HswTC
import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddPrimeInvertersBasic

@[expose] public section

namespace CFSG.KC.Th.Soundness

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Kernel CFSG.Sporadic.Bridge CFSG.Sporadic.ThSchreier
  Pointwise CFSG.KC.Th.Gen

set_option maxRecDepth 100000 in
#kc_generalize DceStructGen (p : TauCeti.GroupPresentation)
    using [TauCeti.SporadicName.presentation TauCeti.SporadicName.Th ↦ p]
    from [TauCeti.Sporadic.Thompson.presentation, CFSG.Sporadic.Th.Native.seedA,
      CFSG.Sporadic.Th.Native.seedB, CFSG.Blueprint.NativeSporadic.ThSeed1,
      CFSG.Blueprint.NativeSporadic.ThSeed2] :
  DceFacts

theorem seed_sound_gen (sA sB : String) (D : SeedData) (_hA : sA = String.ofList D.ThSeed_LA)
    (_hB : sB = String.ofList D.ThSeed_LB) (_h : seedChk D = true) :
    let A := Native.rowsOf sA
    let B := Native.rowsOf sB
    Native.eqRows (Native.mulRows A A) Native.idRows = true ∧
      Native.eqRows (Native.mulRows (Native.mulRows B B) B) Native.idRows = true ∧
      Native.eqRows (Native.mulRows (Native.mulRows (Native.transposeRows A) Native.fcRows) A)
        Native.fcRows = true ∧
      Native.eqRows (Native.mulRows (Native.mulRows (Native.transposeRows B) Native.fcRows) B)
        Native.fcRows = true := by
  dsimp only
  subst _hA _hB
  unfold seedChk at _h
  have h1 := andB_left _h
  have h2 := andB_right _h
  have h11 := andB_left h1
  have h12 := andB_right h1
  have hk := andB_left h11
  have hdA := andB_right h11
  have hdB := andB_left h12
  have hpF := andB_right h12
  have h21 := andB_left h2
  have h22 := andB_right h2
  have e1 := Nat.eq_of_beq_eq_true (andB_left h21)
  have e2 := Nat.eq_of_beq_eq_true (andB_right h21)
  have e3 := Nat.eq_of_beq_eq_true (andB_left h22)
  have e4 := Nat.eq_of_beq_eq_true (andB_right h22)
  obtain ⟨-, hAm⟩ := CFSG.KC.Th.Spec.decOK_sound hdA
  obtain ⟨-, hBm⟩ := CFSG.KC.Th.Spec.decOK_sound hdB
  have hFm : CFSG.KC.Th.Spec.pkMat D.ThSeed_SF = rowsMatrix Native.fcRows := by
    rw [CFSG.KC.Th.Spec.packOK_sound hpF, CFSG.KC.Th.Spec.fcRowsList_toArray]
  have wA := CFSG.KC.Th.Spec.wfRows_rowsOf (String.ofList D.ThSeed_LA)
  have wB := CFSG.KC.Th.Spec.wfRows_rowsOf (String.ofList D.ThSeed_LB)
  have wF := CFSG.KC.Th.Spec.wfRows_fcRows
  have wI := CFSG.KC.Th.Spec.wfRows_idRows
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine CFSG.KC.Th.Spec.eqRows_of_rowsMatrix_eq
      (CFSG.KC.Th.Spec.wfRows_mulRows wA wA) wI ?_
    have h := congrArg CFSG.KC.Th.Spec.pkMat e1
    rw [CFSG.KC.Th.Spec.pkMat_mulB hk, CFSG.KC.Th.Spec.pkMat_one hk, hAm] at h
    rw [rowsMatrix_mulRows, rowsMatrix_idRows]
    exact h
  · refine CFSG.KC.Th.Spec.eqRows_of_rowsMatrix_eq
      (CFSG.KC.Th.Spec.wfRows_mulRows (CFSG.KC.Th.Spec.wfRows_mulRows wB wB) wB) wI ?_
    have h := congrArg CFSG.KC.Th.Spec.pkMat e2
    rw [CFSG.KC.Th.Spec.pkMat_mulB hk, CFSG.KC.Th.Spec.pkMat_mulB hk,
      CFSG.KC.Th.Spec.pkMat_one hk, hBm] at h
    rw [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_idRows]
    exact h
  · refine CFSG.KC.Th.Spec.eqRows_of_rowsMatrix_eq
      (CFSG.KC.Th.Spec.wfRows_mulRows (CFSG.KC.Th.Spec.wfRows_mulRows
        (CFSG.KC.Th.Spec.wfRows_transposeRows _) wF) wA) wF ?_
    have h := congrArg CFSG.KC.Th.Spec.pkMat e3
    rw [CFSG.KC.Th.Spec.pkMat_mulB hk, CFSG.KC.Th.Spec.pkMat_mulB hk,
      CFSG.KC.Th.Spec.pkMat_trB hk, hAm, hFm] at h
    rw [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_transposeRows]
    exact h
  · refine CFSG.KC.Th.Spec.eqRows_of_rowsMatrix_eq
      (CFSG.KC.Th.Spec.wfRows_mulRows (CFSG.KC.Th.Spec.wfRows_mulRows
        (CFSG.KC.Th.Spec.wfRows_transposeRows _) wF) wB) wF ?_
    have h := congrArg CFSG.KC.Th.Spec.pkMat e4
    rw [CFSG.KC.Th.Spec.pkMat_mulB hk, CFSG.KC.Th.Spec.pkMat_mulB hk,
      CFSG.KC.Th.Spec.pkMat_trB hk, hBm, hFm] at h
    rw [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_transposeRows]
    exact h

end CFSG.KC.Th.Soundness

end
