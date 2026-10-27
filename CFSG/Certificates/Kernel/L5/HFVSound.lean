module

public import Certificates.Data.Kernel.L5.HFV
public import Certificates.Data.Kernel.L5.HFQ
public import CFSG.Certificates.Kernel.L5.HFCSound

public section

namespace CFSG.Certificates.Kernel.L5H

open Equiv Perm CFSG.Certificates.Kernel.PkCV CFSG.KC.Enum CFSG.Certificates.Kernel.L5S
  CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.L5.HF CFSG.GH74.GLS.C3.Layer2.Model

theorem nbeq (a b : Nat) : Nat.beq a b = (a == b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]

theorem nbeq_dec (a b : Nat) : Nat.beq a b = decide (a = b) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.beq_eq]

theorem nble_dec (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.ble_eq]

theorem memV_eq (a : Nat) : ∀ l : List Nat, memV a l = decide (a ∈ l)
  | [] => rfl
  | b :: t => by
    change Bool.rec (motive := fun _ => Bool) (memV a t) true (Nat.beq a b) = decide (a ∈ b :: t)
    rw [memV_eq a t, nbeq_dec]
    by_cases h : a = b
    · rw [decide_eq_true h, decide_eq_true (List.mem_cons.2 (Or.inl h))]
    · rw [decide_eq_false h]
      exact decide_eq_decide.2 (by simp [List.mem_cons, h])

theorem dedupV_eq : ∀ l : List Nat, dedupV l = l.dedup
  | [] => List.dedup_nil.symm
  | a :: t => by
    change Bool.rec (motive := fun _ => List Nat) (a :: dedupV t) (dedupV t) (memV a t) = _
    rw [memV_eq, dedupV_eq t]
    by_cases h : a ∈ t
    · rw [decide_eq_true h, List.dedup_cons_of_mem h]
    · rw [decide_eq_false h, List.dedup_cons_of_notMem h]

theorem rec_foldl (f : Nat → Nat → Nat) : ∀ n,
    Nat.rec (motive := fun _ => Nat) 0 (fun i acc => f i acc) n =
      (List.range n).foldl (fun acc i => f i acc) 0
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, ← rec_foldl f n]
    rfl

theorem img16_eq (p i : Nat) : img 16 p i = pg 5 31 p i := by
  unfold img
  rw [CFSG.Certificates.Kernel.L5Q.wC16q]
  rfl

theorem imgV_eq (g : CV 16) (M : Nat) : imgV g.1 M = imgN g M := by
  unfold imgV imgN
  refine (rec_foldl (fun i acc => Nat.lor acc (Nat.mul (Nat.land (Nat.shiftRight M i) 1)
    (Nat.shiftLeft 1 (pg 5 31 g.1 i)))) 16).trans ?_
  congr 1
  funext acc i
  change acc ||| (M >>> i &&& 1) * (1 <<< pg 5 31 g.1 i) = _
  rw [Nat.and_one_is_mod, Nat.one_shiftLeft, img16_eq]

theorem orbStepV_eq (gs : List (CV 16)) (l : List Nat) :
    orbStepV (gs.map Subtype.val) l = orbStepN gs l := by
  unfold orbStepV orbStepN
  rw [dedupV_eq]
  simp only [List.map_map, Function.comp_def, imgV_eq]

theorem pN_Qpl : pN Qpl = 15 := by decide

theorem pN_Ppl : pN Ppl = 4369 := by decide

theorem orbListV_eq (gs : List (CV 16)) (k : Nat) :
    orbListV (gs.map Subtype.val) k = orbListN gs k := by
  unfold orbListV orbListN
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply, Function.iterate_zero_apply, pN_Qpl]
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, orbStepV_eq]

theorem n24PreV_eq (x : CV 16) : n24PreV x.1 = n24PreC x := by
  unfold n24PreV n24PreC
  simp only [imgV_eq, pN_Qpl, pN_Ppl, nbeq]
  rfl

theorem fam0L_pN : fam0L.map pN = [18465, 9345, 15, 33345] := by decide

theorem fam1L_pN : fam1L.map pN = [10305, 17025, 33825, 15] := by decide

theorem all_pN_mem (L : List (Finset (Fin 16))) (o : List Nat) :
    (L.all fun F => decide (pN F ∈ o)) = (L.map pN).all fun n => memV n o := by
  rw [List.all_map]
  simp only [Function.comp_def, memV_eq]

theorem n24TailV_eq (GN : List Nat) (MP : Nat) (x : CV 16) (o : List Nat) :
    n24TailV GN MP x o = n24TailN GN MP x o := by
  unfold n24TailV n24TailN
  rw [all_pN_mem, all_pN_mem, fam0L_pN, fam1L_pN, imgV_eq, pN_Ppl, nbeq]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc]

theorem n24ChkV_eq (GN : List Nat) (MP : Nat) (x : CV 16) :
    n24ChkV GN MP x = n24ChkN GN MP x := by
  unfold n24ChkV n24ChkN
  have e : [yC.1, wC.1, x.1] = [yC, wC, x].map Subtype.val := rfl
  rw [e, orbListV_eq, orbListV_eq]
  simp only [dedupV_eq, n24TailV_eq, nbeq_dec, nble_dec]

theorem n24EntryV_eq (GN : List Nat) (MP : Nat) (x : CV 16) :
    n24EntryV GN MP x = n24EntryN GN MP x := by
  unfold n24EntryV n24EntryN
  rw [n24PreV_eq, n24ChkV_eq]

theorem fam0_of_chkN (c : CV 16) (h : fam0ChkN c = true) : ∀ V ∈ fam0, V.image (ev c) ∈ fam0 := by
  intro V hV
  rw [mem_fam0] at hV ⊢
  unfold fam0ChkN at h
  rw [List.all_eq_true] at h
  have := of_decide_eq_true (h V hV)
  rwa [← pN_image, List.mem_map_of_injective pN_injective] at this

theorem fam1_of_chkN (c : CV 16) (h : fam1ChkN c = true) : ∀ V ∈ fam1, V.image (ev c) ∈ fam1 := by
  intro V hV
  rw [mem_fam1] at hV ⊢
  unfold fam1ChkN at h
  rw [List.all_eq_true] at h
  have := of_decide_eq_true (h V hV)
  rwa [← pN_image, List.mem_map_of_injective pN_injective] at this

theorem planes0_map : planes0.map List.toFinset = fam0L := rfl

theorem planes1_map : planes1.map List.toFinset = fam1L := rfl

theorem planes0_fam0 : ∀ V ∈ planes0, V.toFinset ∈ fam0 := by
  intro V hV
  rw [mem_fam0, ← planes0_map]
  exact List.mem_map_of_mem hV

theorem fam0_planes0 : ∀ F ∈ fam0, ∃ W ∈ planes0, W.toFinset = F := by
  intro F hF
  rwa [mem_fam0, ← planes0_map, List.mem_map] at hF

theorem planes1_fam1 : ∀ V ∈ planes1, V.toFinset ∈ fam1 := by
  intro V hV
  rw [mem_fam1, ← planes1_map]
  exact List.mem_map_of_mem hV

theorem fam1_planes1 : ∀ F ∈ fam1, ∃ W ∈ planes1, W.toFinset = F := by
  intro F hF
  rwa [mem_fam1, ← planes1_map, List.mem_map] at hF

end CFSG.Certificates.Kernel.L5H

end
