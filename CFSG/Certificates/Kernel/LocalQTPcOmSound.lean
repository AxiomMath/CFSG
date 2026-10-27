module

public import Certificates.Data.Kernel.LocalQT.PcOm
public import CFSG.Certificates.Kernel.LocalQTPcWSound
import Mathlib.Data.List.Sort
import CFSG.Quasithin.EmptyFaithful.GoldschmidtThreeDLocKer

public section

namespace CFSG.KC.LQT.PcOm

open CFSG.KC.Enum CFSG.KS CFSG.KS.PF CFSG.KC.LQT.PcW
open CFSG.QuasithinUnique.Ch1.SporLat (ptAct sortN OmegaData OmegaSpec)

theorem insB_eq (a : Nat) : ∀ l : List Nat, insB a l = l.orderedInsert (· ≤ ·) a
  | [] => by
    rw [List.orderedInsert_nil]
    rfl
  | b :: t => by
    have e : insB a (b :: t) = Bool.rec (motive := fun _ => List Nat) (b :: insB a t)
        (a :: b :: t) (Nat.ble a b) := rfl
    rw [e, insB_eq a t, List.orderedInsert_cons]
    by_cases h : a ≤ b
    · have hb : Nat.ble a b = true := by simpa using h
      rw [hb, if_pos h]
    · have hb : Nat.ble a b = false := Bool.eq_false_iff.2 fun hh => h (by simpa using hh)
      rw [hb, if_neg h]

theorem srtB_eq : ∀ l : List Nat, srtB l = l.insertionSort (· ≤ ·)
  | [] => by
    rw [List.insertionSort_nil]
    rfl
  | a :: l => by
    have e : srtB (a :: l) = insB a (srtB l) := rfl
    rw [e, srtB_eq l, insB_eq, List.insertionSort_cons]

theorem sortN_eq_srtB (l : List Nat) : sortN l = srtB l := by
  rw [srtB_eq]
  unfold sortN
  have e : (fun a b : Nat => decide (a ≤ b)) = fun a b => decide ((· ≤ ·) a b) := rfl
  rw [e, List.mergeSort_eq_insertionSort]

theorem lstEqB_spec : ∀ {x y : List Nat}, lstEqB x y = true → x = y
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [lstEqB] at h
  | _ :: _, [], h => by simp [lstEqB] at h
  | a :: x, b :: y, h => by
    have e : lstEqB (a :: x) (b :: y) = bAnd(Nat.beq a b, lstEqB x y) := rfl
    rw [e] at h
    obtain ⟨h1, h2⟩ := bAnd_true h
    rw [Nat.eq_of_beq_eq_true h1, lstEqB_spec h2]

theorem nthL_eq : ∀ (l : List (List Nat)) (i : Nat), nthL l i = l.getD i []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | x :: l, i + 1 => by
    have e : nthL (x :: l) (i + 1) = nthL l i := rfl
    rw [e, nthL_eq l i]
    rfl

theorem nthN_eq : ∀ (l : List Nat) (i : Nat), nthN l i = l.getD i 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | x :: l, i + 1 => by
    have e : nthN (x :: l) (i + 1) = nthN l i := rfl
    rw [e, nthN_eq l i]
    rfl

theorem getD_toList_lbl (a : Array (List Nat)) (i : Nat) : a.toList.getD i [] = a[i]! := by
  rw [List.getD_eq_getElem?_getD, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_toList]
  rfl

theorem getD_toList_pn (a : Array (Array Nat)) (l : Nat) :
    (a.toList.map Array.toList).getD l [] = (a[l]!).toList := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem!_eq_getD,
    Array.getD_eq_getD_getElem?, Array.getElem?_toList]
  cases a[l]? <;> rfl

theorem getD_toList_row (a : Array Nat) (i : Nat) : a.toList.getD i 0 = a[i]! := by
  rw [List.getD_eq_getElem?_getD, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_toList]
  rfl

theorem omegaSpec_of_cp {n w : Nat} {Lc : Nat → Nat} {L : List (Array Nat)}
    (hL : ∀ l < L.length, Rep n w (Lc l) L[l]!) {Δ : List Nat} {O : OmegaData (List Nat)}
    (h0 : O.lbl[0]! = Δ) (hpos : 0 < O.lbl.size)
    (hom : omK n w (mask w) Lc L.length O.lbl.size O.lbl.toList (O.pn.toList.map Array.toList) =
      true)
    (htree : ∀ i < O.lbl.size, 0 < i → O.par[i]! < i ∧ O.via[i]! < L.length ∧
      (O.pn[O.via[i]!]!)[O.par[i]!]! = i)
    (hnd : O.lbl.toList.Nodup) : OmegaSpec ptAct L.toArray Δ O := by
  refine ⟨h0, hpos, fun l hl i hi => ?_, fun i hi hi0 => ?_,
    CFSG.Quasithin.GoldD3.distinctB_of_nodup hnd⟩
  · have hl' : l < L.length := by simpa using hl
    have h1 := allN_spec hom l hl'
    rw [strictB_eqP] at h1
    have h2 := allN_spec h1 i hi
    unfold omAt at h2
    beta_reduce at h2
    simp only [nthL_eq, nthN_eq, getD_toList_pn, getD_toList_row, getD_toList_lbl] at h2
    obtain ⟨ha, hbc⟩ := bAnd_true h2
    obtain ⟨hb, hc⟩ := bAnd_true hbc
    refine ⟨by simpa [Nat.blt_eq] using ha, ?_⟩
    have hall := allL_spec hb
    rw [← lstEqB_spec hc, imgsK_eq]
    have hLl : L.toArray[l]! = L[l]! := by
      rw [getElem!_pos _ l hl, getElem!_pos _ l hl', List.getElem_toArray]
    rw [hLl]
    unfold ptAct
    rw [sortN_eq_srtB]
    congr 1
    apply List.map_congr_left
    intro p hp
    have hpn : p < n := by simpa [Nat.blt_eq] using hall p hp
    rw [← rep_get (hL l hl') p hpn, Array.getElem!_eq_getD]
    rfl
  · obtain ⟨a, b, c⟩ := htree i hi hi0
    exact ⟨a, by simpa using b, c⟩

end CFSG.KC.LQT.PcOm

end
