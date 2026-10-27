
module

public import CFSG.Certificates.Kernel.Th.SoundnessTsGenBase

public import CFSG.Certificates.Kernel.Th.Gen.Ts
public import CFSG.Sporadic.ThSchreier.LocalOrbitInputs
public meta import CFSG.Sporadic.ThSchreier.WordsBase1
public meta import CFSG.Sporadic.ThSchreier.LocalData
public import CFSG.Sporadic.ThSchreier.TwoCentralizerInputs
public meta import CFSG.Sporadic.ThSchreier.OrbitCheck819Base
public meta import CFSG.Sporadic.Th.Max3.PacketBase1
import CFSG.Certificates.Kernel.Common.Generalize
import CFSG.Certificates.Kernel.Th.Spec.Big
import CFSG.Certificates.Kernel.Th.Spec.Loops
import CFSG.Certificates.Kernel.Th.Spec.Parse
import CFSG.Certificates.Kernel.Th.Spec.Seed
import CFSG.Certificates.Kernel.Th.Spec.Ts2313
import CFSG.Certificates.Kernel.Th.Spec.Ts2324
import CFSG.Certificates.Kernel.Th.Spec.TsLeaves
public import CFSG.Sporadic.Th.BaseBase1
public import CFSG.Sporadic.Th.ChainBase1
public import CFSG.Sporadic.Th.Max3.AllConjBase1
public import CFSG.Sporadic.Th.Max3.AllConjInputs
public import CFSG.Sporadic.Th.Max3.CoreBase1
public import CFSG.Sporadic.Th.Max3.InvolutionsBase1
public import CFSG.Sporadic.Th.Max3.InvolutionsInputs
public import CFSG.Sporadic.Th.Max3.QuotientBase1
public import CFSG.Sporadic.Th.Max3.QuotientInputs
public import CFSG.Sporadic.ThSchreier.WordsBase1
import CFSG.Certificates.Kernel.Th.Spec.GjBase
import CFSG.Sporadic.ThSchreier.UASpaceInputs

public section

namespace CFSG.KC.Th.Soundness

open CFSG CFSG.Sporadic CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Th.Max3 Pointwise
open CFSG.Sporadic.Th.Max3
open CFSG.KC.Th.Gen CFSG.Sporadic.Th CFSG.Sporadic.ThSchreier

#kc_generalize TsGen2324 (sA sB : String)
    using [CFSG.Sporadic.Th.Native.seedA ↦ sA, CFSG.Sporadic.Th.Native.seedB ↦ sB]
    from [CFSG.Blueprint.NativeSporadic.ThSeed1, CFSG.Blueprint.NativeSporadic.ThSeed2,
      CFSG.Sporadic.ThSchreier.localRowsTxt, CFSG.Sporadic.ThSchreier.localPermX,
      CFSG.Sporadic.ThSchreier.localPermY, CFSG.Sporadic.ThSchreier.localTreePts,
      CFSG.Sporadic.ThSchreier.localTreePar, CFSG.Sporadic.ThSchreier.localTreeLab] :
  (eqRows (CFSG.Sporadic.Th.Native.mulRows (hRows centWord0) rowsT) (CFSG.Sporadic.Th.Native.mulRows rowsT (hRows centWord0)) = true ∧
    eqRows (CFSG.Sporadic.Th.Native.mulRows (hRows centWord1) rowsT) (CFSG.Sporadic.Th.Native.mulRows rowsT (hRows centWord1)) = true ∧
    (∀ R ∈ twoRowsList, eqRows (CFSG.Sporadic.Th.Native.mulRows R (invRows R)) idRows = true ∧
      (invRows R).size = 248 ∧ ∀ r ∈ invRows R, r.wf = true) ∧
    twoRowsList.length = 10 ∧
    eqRows (signedRows (tupleRows twoRowsList) origWord0) rowsLX = true ∧
    eqRows (signedRows (tupleRows twoRowsList) origWord1) rowsLY = true ∧
    eqRows rowsTwoR rowsE217 = true ∧ eqRows rowsTwoR idRows = false ∧
    eqRows rowsTwoR rowsZ = false)

theorem ts_sound2313_gen (sA sB rows : String) (px py tp tpa tla : Array ℕ) (D : TsData)
    (_hA : sA = String.ofList D.ThSeed_LA) (_hB : sB = String.ofList D.ThSeed_LB)
    (_hR : rows = String.ofList D.ThTs_Lrows)
    (_hX : px = (natsOf (String.ofList D.ThTs_Lpx)).toArray)
    (_hY : py = (natsOf (String.ofList D.ThTs_Lpy)).toArray)
    (_hP : tp = (natsOf (String.ofList D.ThTs_Ltp)).toArray)
    (_hQ : tpa = (natsOf (String.ofList D.ThTs_Ltpa)).toArray)
    (_hL : tla = (natsOf (String.ofList D.ThTs_Ltla)).toArray)
    (_h : tsChk D = true) : TsGen2313 sA sB rows px py tp tpa tla := by
  have L := Spec.tsChk_leaves _h
  have hA : Spec.WfRows (Native.rowsOf sA) := Spec.wfRows_rowsOf sA
  have hB : Spec.WfRows (Native.rowsOf sB) := Spec.wfRows_rowsOf sB
  have hSA : Spec.pkMat D.ThSeed_SA = rowsMatrix (Native.rowsOf sA) := by
    rw [_hA]; exact (Spec.decOK_sound L.c5).2
  have hSB : Spec.pkMat D.ThSeed_SB = rowsMatrix (Native.rowsOf sB) := by
    rw [_hB]; exact (Spec.decOK_sound L.c6).2
  have hrows : hexsOf rows = (List.range 2457).map D.ThTs_ROWS := by
    rw [_hR]; exact Spec.hexsOf_ofList_of_natsRun L.c604
  have hpx : px = ((List.range 2457).map D.ThTs_PX).toArray := by
    rw [_hX, Spec.natsOf_ofList_of_natsRun L.c605]
  have hpy : py = ((List.range 2457).map D.ThTs_PY).toArray := by
    rw [_hY, Spec.natsOf_ofList_of_natsRun L.c606]
  have htp : tp = ((List.range 2457).map D.ThTs_TP).toArray := by
    rw [_hP, Spec.natsOf_ofList_of_natsRun L.c607]
  have htpa : tpa = ((List.range 2457).map D.ThTs_TPA).toArray := by
    rw [_hQ, Spec.natsOf_ofList_of_natsRun L.c608]
  have htla : tla = ((List.range 2457).map D.ThTs_TLA).toArray := by
    rw [_hL, Spec.natsOf_ofList_of_natsRun L.c609]
  have hdist : ∀ i < 2457, ∀ j < 2457, i < j → D.ThTs_ROWS i ≠ D.ThTs_ROWS j :=
    Spec.runSorted_inj L.c0 L.c610 (by norm_num) (by norm_num)
  have hperm : ∀ i < 2457, TsS.permOK D.ThTs_ROWS D.ThTs_PX D.ThTs_PY D.ThS_rm (D.ThTs_RB 1)
      (D.ThTs_RB 3) 2457 i = true := fun i hi =>
    (Spec.runItems_spec D.cs1 (by norm_num) (L.c1.trans L.c629) (by norm_num)).2 i (by omega)
      (by omega)
  have hinv : ∀ i < 2457, TsS.invOK D.ThTs_TP D.ThTs_INV 2457 i = true := fun i hi =>
    (Spec.runItems_spec D.cs2 (by norm_num) (L.c2.trans L.c630) (by norm_num)).2 i (by omega)
      (by omega)
  have htree : ∀ i < 2457, TsS.treeOK D.ThTs_TP D.ThTs_TPA D.ThTs_TLA D.ThTs_PX D.ThTs_PY 2457 i =
      true := fun i hi =>
    (Spec.runItems_spec D.cs3 (by norm_num) (L.c3.trans L.c631) (by norm_num)).2 i (by omega)
      (by omega)
  exact Spec.concl2313_of_facts L hA hB hSA hSB hrows hpx hpy htp htpa htla hdist hperm hinv htree

theorem ts_sound2324_gen (sA sB : String) (D : TsData) (_hA : sA = String.ofList D.ThSeed_LA)
    (_hB : sB = String.ofList D.ThSeed_LB) (_h : tsChk D = true) : TsGen2324 sA sB := by
  have L := Spec.tsChk_leaves _h
  have hA : Spec.WfRows (Native.rowsOf sA) := Spec.wfRows_rowsOf sA
  have hB : Spec.WfRows (Native.rowsOf sB) := Spec.wfRows_rowsOf sB
  have hSA : Spec.pkMat D.ThSeed_SA = rowsMatrix (Native.rowsOf sA) := by
    rw [_hA]; exact (Spec.decOK_sound L.c5).2
  have hSB : Spec.pkMat D.ThSeed_SB = rowsMatrix (Native.rowsOf sB) := by
    rw [_hB]; exact (Spec.decOK_sound L.c6).2
  exact Spec.concl2324_of_leaves L hA hB hSA hSB

end CFSG.KC.Th.Soundness

end
