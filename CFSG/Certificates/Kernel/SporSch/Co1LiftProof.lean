module

public import CFSG.Certificates.Kernel.SporSch.Co1LiftSound
public import CFSG.Certificates.Kernel.Spor.DistinctSound
public import CFSG.Certificates.Kernel.SporSch.Co1ActLemmas
public import CFSG.Certificates.Kernel.Spor.PackFld
public import Certificates.Data.Kernel.SporSch.Co1Lift

public section

namespace CFSG.KS.SporSch.Lift

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.M24 CFSG.KS.Co2Shape CFSG.KS.Mathieu
open CFSG.Sporadic.Co1Schreier.Native CFSG.KS.Raw

theorem lenN_eq_length : ∀ l : List Nat, lenN l = l.length
  | [] => rfl
  | _ :: l => congrArg Nat.succ (lenN_eq_length l)

theorem unpack_get_l {n w P i : Nat} (hi : i < n) : (unpack n w P)[i]! = pg w (mask w) P i := by
  rw [unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem blt_dec_l (a b : Nat) : Nat.blt a b = decide (a < b) := by
  rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_iff]

theorem nIf_dec_l (c : Prop) [Decidable c] (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t (decide c) = if c then t else e := by
  by_cases h : c <;> simp [h]

theorem strictB_l (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem bIf_l (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem repK_lt (PR m : Nat) : repK PR m < 2 ^ 24 := PackFld.pg_lt 24 PR m

theorem clsValS_eq {PR z m : Nat} (hm : m < 4600) :
    clsValS (unpack 2300 24 PR) z m = valK PR z m := by
  unfold clsValS valK
  rw [blt_dec_l, nIf_dec_l]
  by_cases h : m < 2300
  · rw [if_pos h, if_pos h, unpack_get_l h]
    rfl
  · rw [if_neg h, if_neg h, unpack_get_l (by omega)]
    rfl

theorem valK_lt {PR z : Nat} (hz : z < 2 ^ 24) (m : Nat) : valK PR z m < 2 ^ 24 := by
  unfold valK
  rw [blt_dec_l, nIf_dec_l]
  split
  · exact repK_lt PR m
  · exact Nat.xor_lt_two_pow hz (repK_lt PR _)

theorem incV_spec {PR z : Nat} : ∀ (l : List Nat) (p : Nat), incV PR z l p = true →
    (∀ v ∈ l.map (valK PR z), p ≤ v) ∧ (l.map (valK PR z)).Pairwise (· < ·)
  | [], _, _ => ⟨by simp, List.Pairwise.nil⟩
  | m :: l, p, h => by
    change strictB (valK PR z m) (fun v => bAnd(Nat.ble p v, incV PR z l (Nat.succ v))) = true at h
    rw [strictB_l] at h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    have hp := Nat.le_of_ble_eq_true h1
    obtain ⟨ih1, ih2⟩ := incV_spec l _ h2
    refine ⟨fun v hv => ?_, List.Pairwise.cons (fun v hv => ih1 v hv) ih2⟩
    rw [List.map_cons, List.mem_cons] at hv
    rcases hv with e | hv'
    · rw [e]
      exact hp
    · have := ih1 v hv'
      omega

theorem vSorted_of_pairwise : ∀ l : List Nat, l.Pairwise (· < ·) → vSorted l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: r, h => by
    have hab : a < b := List.rel_of_pairwise_cons h List.mem_cons_self
    have ih := vSorted_of_pairwise (b :: r) (List.Pairwise.of_cons h)
    simp only [vSorted, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hab, ih⟩

theorem liftK_proved {PR Q0 Q1 PH0 PH1 z : Nat} {Ms : List Nat}
    (h : liftK PR Q0 Q1 PH0 PH1 z Ms = true) :
    liftSpec (unpack 2300 24 PR) (unpack 2300 12 Q0) (unpack 2300 12 Q1) (unpack 24 24 PH0)
      (unpack 24 24 PH1) z = true := by
  unfold liftK at h
  obtain ⟨hz, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hl, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hd, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hi, hs⟩ := (bAnd_iff _ _).1 h
  have hz' : z < 2 ^ 24 := Nat.blt_eq.mp hz
  have hlen : Ms.length = 4600 := by rw [← lenN_eq_length]; exact Nat.eq_of_beq_eq_true hl
  obtain ⟨hnd, hlt⟩ := distinctL_sound hd
  obtain ⟨-, hinc⟩ := incV_spec Ms 0 hi
  have hperm : Ms.Perm (List.range 4600) :=
    List.Subperm.perm_of_length_le (List.Nodup.subperm hnd fun x hx =>
      List.mem_range.2 (hlt x hx).1) (by simp [hlen])
  have hmap : Ms.map (clsValS (unpack 2300 24 PR) z) = Ms.map (valK PR z) :=
    List.map_congr_left fun m hm => clsValS_eq (hlt m hm).1
  have hsort : ((List.range 4600).map (clsValS (unpack 2300 24 PR) z)).mergeSort
      (fun a b => decide (a ≤ b)) = Ms.map (valK PR z) := by
    refine List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (List.pairwise_mergeSort' (· ≤ ·) _)
      (hinc.imp Nat.le_of_lt) ?_
    refine (List.mergeSort_perm _ _).trans ?_
    rw [← hmap]
    exact (hperm.map _).symm
  unfold liftSpec
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  refine ⟨⟨⟨by simp [unpack], fun m hm => ?_⟩, ?_⟩, fun j hj => ?_⟩
  · rw [clsValS_eq hm]
    exact valK_lt hz' m
  · rw [hsort]
    exact vSorted_of_pairwise _ hinc
  · have hsj := allN_spec hs j hj
    obtain ⟨s0, s1⟩ := (bAnd_iff _ _).1 hsj
    have side : ∀ {H Q : Nat}, sideK PR z H Q j = true →
        inClsS (unpack 2300 24 PR) z (act (unpack 24 24 H) (unpack 2300 24 PR)[j]!)
          (unpack 2300 12 Q)[j]! = true := by
      intro H Q hk
      unfold sideK at hk
      rw [strictB_l, strictB_l] at hk
      obtain ⟨k1, k2⟩ := (bAnd_iff _ _).1 hk
      have hk1 : pg 12 4095 Q j < 2300 := Nat.blt_eq.mp k1
      have eQ : (unpack 2300 12 Q)[j]! = pg 12 4095 Q j := unpack_get_l hj
      rw [unpack_get_l (w := 24) hj, CFSG.KS.SporSch.M24.ActL.act_unpack, eQ]
      unfold inClsS
      rw [clsValS_eq (by omega), clsValS_eq (by omega)]
      change (actK H (repK PR j) == valK PR z (pg 12 4095 Q j) ||
        actK H (repK PR j) == valK PR z (pg 12 4095 Q j + 2300)) = true
      rw [bIf_l] at k2
      split at k2
      · rename_i e
        rw [Nat.beq_eq] at e
        simp [e]
      · rw [Nat.beq_eq] at k2
        simp only [Nat.add_eq] at k2
        simp [k2]
    exact ⟨side s0, side s1⟩

end CFSG.KS.SporSch.Lift

end
