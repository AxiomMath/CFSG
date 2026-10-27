module

public import CFSG.Certificates.Kernel.Cert690.EnumSound
public import CFSG.Certificates.Kernel.Cert690.CBaseSound
public import CFSG.GF2Type.Smith1979W3.Cert690.Census.Main

public section

namespace CFSG.KC.C690

open CFSG.GF2Type.Smith1979W3.Cert690

structure GrpChecks (minus : Bool) (O : List ℕ) (par S : List (ℕ × ℕ)) (Om : List ℕ)
    (omPar Sm : List (ℕ × ℕ)) (inv : List ℕ) : Prop where
  lenO : O.length = if minus then 51840 else 40320
  lenOm : Om.length = if minus then 25920 else 20160
  ixO : ixOK S O = true
  ixOm : ixOK Sm Om = true
  bfsO : bfsOK (fun y => (idxT S).find y O.length) (oGensC minus) O par = true
  bfsOm : bfsOK (fun y => (idxT Sm).find y Om.length) (omegaGensC minus) Om omPar = true
  invO : invK (idxT S) O.length O inv = true
  head : O.head? = some oneF
  headm : Om.head? = some oneF
  parO : enumParK (fun i => (posT O).find i 0) (oGensC minus) O par 0 = true
  clO : enumClK (fun y => (idxT S).find y O.length) O.length (oGensC minus) O = true
  invGO : enumInvK (oGensC minus) O = true
  parOm : enumParK (fun i => (posT Om).find i 0) (omegaGensC minus) Om omPar 0 = true
  clOm : enumClK (fun y => (idxT Sm).find y Om.length) Om.length (omegaGensC minus) Om = true
  invGOm : enumInvK (omegaGensC minus) Om = true
  invMul : invMulK (fun i => (posT O).find i 0) O.length O inv = true

namespace GrpChecks

variable {minus : Bool} {O : List ℕ} {par S : List (ℕ × ℕ)} {Om : List ℕ}
  {omPar Sm : List (ℕ × ℕ)} {inv : List ℕ} (h : GrpChecks minus O par S Om omPar Sm inv)
include h

theorem len_le : O.length ≤ 65535 := by rw [h.lenO]; cases minus <;> decide

theorem len_le_m : Om.length ≤ 65535 := by rw [h.lenOm]; cases minus <;> decide

theorem ix : O.Nodup ∧ ∀ c, (idxT S).find c O.length = O.idxOf c := find_idxT_eq_idxOf h.ixO

theorem ixm : Om.Nodup ∧ ∀ c, (idxT Sm).find c Om.length = Om.idxOf c :=
  find_idxT_eq_idxOf h.ixOm

theorem enumO : enumData (oGensC minus) = (O.toArray, par.toArray) :=
  enumData_of_bfsOK h.ix.2 h.bfsO (by rw [h.lenO]; cases minus <;> decide)

theorem enumOm : enumData (omegaGensC minus) = (Om.toArray, omPar.toArray) :=
  enumData_of_bfsOK h.ixm.2 h.bfsOm (by rw [h.lenOm]; cases minus <;> decide)

theorem grp_O : (grpData minus ()).O = O.toArray := by
  unfold grpData
  rw [h.enumO]

theorem grp_par : (grpData minus ()).par = par.toArray := by
  unfold grpData
  rw [h.enumO]

theorem grp_Om : (grpData minus ()).Om = Om.toArray := by
  unfold grpData
  rw [h.enumOm]

theorem grp_OmPar : (grpData minus ()).OmPar = omPar.toArray := by
  unfold grpData
  rw [h.enumOm]

theorem grp_idx (c : ℕ) :
    (grpData minus ()).idx.getD c O.length = (idxT S).find c O.length := by
  have e : (grpData minus ()).idx = idxMapOf O.toArray := by
    unfold grpData
    rw [h.enumO]
  rw [e, idxMapOf_getD h.ix.1, h.ix.2]

theorem grp_invI : (grpData minus ()).invI = inv.toArray := by
  have e : (grpData minus ()).invI =
      (invArr O.toArray).map fun c => (idxMapOf O.toArray).getD c O.toArray.size := by
    unfold grpData
    rw [h.enumO]
  rw [e]
  exact invI_of h.ix.1 h.ix.2 h.invO

theorem lenInv : inv.length = O.length := (invMulK_spec _ _ O inv h.invMul).1

theorem getO_eq (i : ℕ) : (posT O).find i 0 = O[i]! := by
  rw [find_posT h.len_le, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rfl

theorem getInv_eq (i : ℕ) : (posT inv).find i 0 = inv[i]! := by
  rw [find_posT (by rw [h.lenInv]; exact h.len_le), List.getElem!_eq_getElem?_getD,
    List.getD_eq_getElem?_getD]
  rfl

theorem rel : GRel (grpData minus ()) (gkOf O S inv O.length) where
  size := by rw [h.grp_O, List.size_toArray]; rfl
  get i := by rw [h.grp_O, List.getElem!_toArray]; exact (h.getO_eq i).symm
  idx c := h.grp_idx c
  inv i := by rw [h.grp_invI, List.getElem!_toArray]; exact (h.getInv_eq i).symm

theorem groupOK : CFSG.GF2Type.Smith1979W3.Cert690.groupOK minus (grpData minus ()) = true := by
  have e1 : enumOK (oGensC minus) (grpData minus ()).O (grpData minus ()).par = true := by
    rw [h.grp_O, h.grp_par]
    exact enumOK_of h.ixO h.len_le h.head h.parO h.clO h.invGO
  have e2 : enumOK (omegaGensC minus) (grpData minus ()).Om (grpData minus ()).OmPar = true := by
    rw [h.grp_Om, h.grp_OmPar]
    exact enumOK_of h.ixOm h.len_le_m h.headm h.parOm h.clOm h.invGOm
  have R := h.rel
  have hidx : idxOK (grpData minus ()) = true := by
    unfold idxOK
    rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range, R.size] at hi
    rw [R.size, R.get, R.idx, beq_iff_eq]
    show (idxT S).find ((posT O).find i 0) O.length = i
    rw [h.ix.2, h.getO_eq, getElem!_pos O i hi]
    exact h.ix.1.idxOf_getElem i _
  have hinv : invArrOK (grpData minus ()) = true := by
    obtain ⟨hl, hm⟩ := invMulK_spec _ _ O inv h.invMul
    unfold invArrOK
    rw [h.grp_invI, h.grp_O]
    simp only [List.all_toArray]
    simp only [List.size_toArray, hl, beq_self_eq_true, Bool.true_and, Bool.and_eq_true,
      List.all_eq_true, decide_eq_true_eq, List.mem_range, List.getElem!_toArray, beq_iff_eq]
    refine ⟨fun j hj => ?_, fun i hi => ?_⟩
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hj
      exact (hm k (by rw [← hl]; exact hk) hk).1
    · have hj : i < inv.length := by rw [hl]; exact hi
      have hlt := (hm i hi hj).1
      have := (hm i hi hj).2
      rw [h.getO_eq, getElem!_pos O _ hlt] at this
      rw [getElem!_pos O i hi, getElem!_pos inv i hj, getElem!_pos O _ hlt, mul_eq_mulF,
        one_eq_oneF]
      exact this
  unfold CFSG.GF2Type.Smith1979W3.Cert690.groupOK
  rw [e1, e2, hidx, hinv, h.grp_O, h.grp_Om, List.size_toArray, List.size_toArray, h.lenO,
    h.lenOm]
  cases minus <;> rfl

end GrpChecks

theorem censusBase_of {minus : Bool} {O : List ℕ} {par S : List (ℕ × ℕ)} {Om : List ℕ}
    {omPar Sm : List (ℕ × ℕ)} {inv : List ℕ} (h : GrpChecks minus O par S Om omPar Sm inv)
    (htr : transK (gkOf O S inv O.length) (singL minus) (b0Of minus)
      (transWitK (gkOf O S inv O.length) (singL minus) (b0Of minus)) = true)
    (hls : censusLsK (gkOf O S inv O.length) minus (ldata minus ()) = true) :
    censusBase minus () = true := by
  unfold censusBase
  rw [censusBaseOf_eq h.rel, h.groupOK, htr, hls]
  rfl

end CFSG.KC.C690

end
