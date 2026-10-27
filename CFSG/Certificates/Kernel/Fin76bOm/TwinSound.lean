module

public import Certificates.Data.Kernel.Fin76bOm.Twin
public import CFSG.Certificates.Kernel.YoshQ.ReplaySound
public import CFSG.Certificates.Kernel.YoshQ.TwinSound

public section

namespace CFSG.KC.Fin76bOm

open CFSG.KC.YoshQ CFSG.KC.Enum CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier.Native CFSG.EvenSporadicStandard.Fin76b

variable {n w : Nat}

theorem find?_congr' {l : List Nat} {p q : Nat → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.find?_cons, List.find?_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem all_congr' {l : List Nat} {p q : Nat → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem toArray_map_tabN_getElem! (L : List Nat) {a : Nat} (ha : a < L.length) :
    ((L.map (tabN n w)).toArray)[a]! = tabN n w (L.getD a 0) := by
  rw [getElem!_pos _ a (by simpa using ha)]
  simp [List.getElem?_eq_getElem ha]

theorem wRoots_tabN (d : Dims n w) (t : Nat) (L : List Nat) :
    wRoots n (tabN n w t) (L.map (tabN n w)).toArray =
      ((L.filter fun x => eqN n w (pmN n w x x) t).map (tabN n w)).toArray := by
  unfold wRoots
  rw [List.filter_toArray, filter_map_tabN']
  simp only [compT_tabN' d, tblEq_tabN' d]

theorem centEOK_tabN (d : Dims n w) (t : Nat) (R W : List Nat) :
    centEOK n (tabN n w t) (R.map (tabN n w)).toArray (W.map (tabN n w)).toArray =
      centEN n w t R W := by
  unfold centEOK centEN
  simp only [List.all_toArray, all_map_tabN, commTT_tabN d, tblEq_tabN' d, idT_tabN' d]

theorem betaOK_tabN (d : Dims n w) (E : List Nat) (b : Nat) :
    betaOK n (E.map (tabN n w)).toArray (tabN n w b) =
      (ordTest n 3 (tabN n w b) && betaN n w E b) := by
  unfold betaOK betaN betaAux
  rw [toList_map_tabN, filter_map_tabN']
  simp only [commTT_tabN d, List.length_map, any_map_tabN]

theorem tblMulIdx_tabN (d : Dims n w) (L : List Nat) {a b : Nat} (ha : a < L.length)
    (hb : b < L.length) : tblMulIdx n (L.map (tabN n w)).toArray a b = mulIdxN n w L a b := by
  unfold tblMulIdx mulIdxN
  simp only [List.size_toArray, List.length_map]
  rw [toArray_map_tabN_getElem! L ha, toArray_map_tabN_getElem! L hb, compT_tabN' d]
  rw [find?_congr' fun c hc => by
    rw [toArray_map_tabN_getElem! L (List.mem_range.1 hc), tblEq_tabN' d]]

theorem tblClosedOK_tabN (d : Dims n w) (L : List Nat) :
    tblClosedOK n (L.map (tabN n w)).toArray = closedN n w L := by
  unfold tblClosedOK closedN
  simp only [List.size_toArray, List.length_map]
  apply all_congr'
  intro a ha
  apply all_congr'
  intro b hb
  have ha' := List.mem_range.1 ha
  have hb' := List.mem_range.1 hb
  rw [tblMulIdx_tabN d L ha' hb', toArray_map_tabN_getElem! L ha',
    toArray_map_tabN_getElem! L hb', compT_tabN' d]
  by_cases hc : mulIdxN n w L a b < L.length
  · rw [toArray_map_tabN_getElem! L hc, tblEq_tabN' d]
  · simp [hc]

structure OmRecs (n w : Nat) (gens : Array Table) (t : Nat) (GS RW : List Nat)
    (cW EPW PLW POSW : Nat) (SMW SFW GE RE : List Nat) (cE EPE PLE POSE : Nat)
    (SME SFE : List Nat) : Prop where
  dims : Dims n w
  recW : RecOK n w n 2000 gens GS RW cW EPW PLW POSW SMW SFW
  recE : RecOK n w n 40 ((GE.map (tabN n w)).toArray) GE RE cE EPE PLE POSE SME SFE
  roots : GE = RW.filter fun x => eqN n w (pmN n w x x) t
  cntW : cW = 1920
  cntE : cE = 32
  permT : permOK n (tabN n w t) = true
  permW : gens.all (fun x => permOK n x) = true
  permE : ((GE.map (tabN n w)).toArray).all (fun x => permOK n x) = true

section Recs

variable {gens : Array Table} {t : Nat} {GS RW : List Nat} {cW EPW PLW POSW : Nat}
  {SMW SFW GE RE : List Nat} {cE EPE PLE POSE : Nat} {SME SFE : List Nat}

theorem OmRecs.closureW (h : OmRecs n w gens t GS RW cW EPW PLW POSW SMW SFW GE RE cE EPE PLE POSE
    SME SFE) : (mulClosureS n n gens 2000).1 = (RW.map (tabN n w)).toArray :=
  h.recW.closure_fst h.dims.n_lt h.dims.n_succ h.dims.w_le (Nat.le_refl _)

theorem OmRecs.roots_eq (h : OmRecs n w gens t GS RW cW EPW PLW POSW SMW SFW GE RE cE EPE PLE POSE
    SME SFE) : wRoots n (tabN n w t) (mulClosureS n n gens 2000).1 = (GE.map (tabN n w)).toArray := by
  rw [h.closureW, wRoots_tabN h.dims, ← h.roots]

theorem OmRecs.closureE (h : OmRecs n w gens t GS RW cW EPW PLW POSW SMW SFW GE RE cE EPE PLE POSE
    SME SFE) : (mulClosureS n n ((GE.map (tabN n w)).toArray) 40).1 = (RE.map (tabN n w)).toArray :=
  h.recE.closure_fst h.dims.n_lt h.dims.n_succ h.dims.w_le (Nat.le_refl _)

theorem OmRecs.enumW (h : OmRecs n w gens t GS RW cW EPW PLW POSW SMW SFW GE RE cE EPE PLE POSE
    SME SFE) : enumOK n n gens (mulClosureS n n gens 2000) 1920 = true :=
  h.recW.enumOK h.dims.n_lt h.dims.n_succ h.dims.w_le (Nat.le_refl _) h.permW h.cntW

theorem OmRecs.enumE (h : OmRecs n w gens t GS RW cW EPW PLW POSW SMW SFW GE RE cE EPE PLE POSE
    SME SFE) : enumOK n n ((GE.map (tabN n w)).toArray)
      (mulClosureS n n ((GE.map (tabN n w)).toArray) 40) 32 = true :=
  h.recE.enumOK h.dims.n_lt h.dims.n_succ h.dims.w_le (Nat.le_refl _) h.permE h.cntE

theorem OmRecs.lenE (h : OmRecs n w gens t GS RW cW EPW PLW POSW SMW SFW GE RE cE EPE PLE POSE
    SME SFE) : RE.length = 32 := by
  have := h.enumE
  simp only [enumOK, Bool.and_eq_true, beq_iff_eq] at this
  rw [h.closureE] at this
  simpa using this.2

theorem wCheck_of (h : OmRecs n w gens t GS RW cW EPW PLW POSW SMW SFW GE RE cE EPE PLE POSE
    SME SFE) (hlen : GE.length = 20) (hcent : centEN n w t GE RW = true) {bk : Nat}
    (hbk : bk < RW.length) (hord : ordTest n 3 (tabN n w (RW.getD bk 0)) = true)
    (hbeta : betaN n w RE (RW.getD bk 0) = true) :
    wCheck n n 2000 (tabN n w t) gens = true := by
  have hWe := h.enumW
  have hEe := h.enumE
  have hr := h.roots_eq
  have hW1 := h.closureW
  have hE1 := h.closureE
  unfold wCheck
  simp only []
  rw [hWe, hr, hEe, hE1, hW1, h.permT, centEOK_tabN h.dims, hcent, List.any_toArray,
    any_map_tabN]
  simp only [Bool.true_and, Bool.and_true, List.size_toArray, List.length_map, hlen,
    beq_self_eq_true, List.any_eq_true]
  refine ⟨RW.getD bk 0, ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ hbk]
    exact List.getElem_mem hbk
  · rw [betaOK_tabN h.dims, hord, hbeta, Bool.and_self]

end Recs

end CFSG.KC.Fin76bOm

end
