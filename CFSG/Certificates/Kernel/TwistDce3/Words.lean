module

public import Certificates.Data.Kernel.TwistDce3.Defs
public import CFSG.Certificates.Kernel.TwistDce2.Words
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.Certificates.TwDce3.Words

open CFSG.KC.TwDce hiding evP isOne pathW wsK wsFail wsJ wsMk wsBad dKind dN1 dN2 isFact walkRun
  walkOK recOK nodesOK foldStep foldRange andB
open CFSG.KC (andB)
open CFSG.KC.TwDce3 CFSG.KC.YModel
open CFSG.Certificates.TwDce.Words hiding evP_eq isOne_spec wsMk_spec wsFail_lt dN1_lt dN2_lt
  andB_iff
open CFSG.Certificates.TwDce2.Words (kandB_iff)

theorem fld15 (x j : ℕ) : fld x (4 * j) 15 = x / 16 ^ j % 16 := by
  unfold fld
  change (x >>> (4 * j)) &&& (2 ^ 4 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

theorem lst_eq (w : ℕ) :
    lst w = (List.range (wLen w)).map (fun i => wStr w / 16 ^ i % 16) := by
  unfold lst
  exact List.map_congr_left fun i _ => fld15 (wStr w) i

theorem land15 (s : ℕ) : Nat.land s 15 = s % 16 := by
  change s &&& (2 ^ 4 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]

theorem shr4 (s : ℕ) : Nat.shiftRight s 4 = s / 16 := by
  rw [show Nat.shiftRight s 4 = s >>> 4 from rfl, Nat.shiftRight_eq_div_pow]

theorem digs_succ (s n : ℕ) : (List.range (n + 1)).map (fun i => s / 16 ^ i % 16) =
    s % 16 :: (List.range n).map (fun i => (s / 16) / 16 ^ i % 16) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp
  · apply List.map_congr_left
    intro i _
    change s / 16 ^ (i + 1) % 16 = _
    rw [pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem evP_loop (PB : ℕ) (F : ℕ → ℕ) : ∀ (n s x : ℕ),
    (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ x => x)
      (fun _ ih s x => sN (fieldAt PB (F (Nat.land s 15)) x) (fun y =>
        sN (Nat.shiftRight s 4) (fun s' => ih s' y))) n) s x =
    ((List.range n).map (fun i => s / 16 ^ i % 16)).foldl
      (fun p c => fieldAt PB (F c) p) x := by
  intro n
  induction n with
  | zero => intro s x; rfl
  | succ n ih =>
    intro s x
    rw [digs_succ, List.foldl_cons]
    simp only [Nat.rec_add_one, sN_eq] at ih ⊢
    rw [ih, land15, shr4]

theorem evP_eq (PB : ℕ) (F : ℕ → ℕ) (w x : ℕ) :
    evP PB F w x = (lst w).foldl (fun p c => fieldAt PB (F c) p) x := by
  rw [lst_eq]
  exact evP_loop PB F (wLen w) (wStr w) x

theorem isOne_loop (PB : ℕ) (F : ℕ → ℕ) (BS w : ℕ) : ∀ n,
    (Nat.rec (motive := fun _ => Bool) true
      (fun i acc => andB acc (sB (fld BS (Nat.mul 16 i) 65535) (fun b =>
        Nat.beq (evP PB F w b) b))) n) = true →
    ∀ i < n, evP PB F w (fld BS (16 * i) 65535) = fld BS (16 * i) 65535 := by
  intro n
  induction n with
  | zero => intro _ i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ n ih =>
    intro h i hi
    change andB _ (sB (fld BS (Nat.mul 16 n) 65535) (fun b => Nat.beq (evP PB F w b) b)) = true
      at h
    rw [kandB_iff, sB_eq] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact ih h.1 i hi
    · exact Nat.eq_of_beq_eq_true h.2

theorem isOne_spec {PB : ℕ} {F : ℕ → ℕ} {BS NB w : ℕ} (h : isOne PB F BS NB w = true) :
    ∀ i < NB, (lst w).foldl (fun p c => fieldAt PB (F c) p) (fld BS (16 * i) 65535) =
      fld BS (16 * i) 65535 := by
  unfold isOne at h
  rw [sB_eq] at h
  intro i hi
  rw [← evP_eq]
  exact isOne_loop PB F BS w NB h i hi

theorem thL_idMap {c : ℕ} (hc : c < 16) : thL idMap c = c := by
  unfold thL
  change fld idMap (4 * c) 15 = c
  rw [fld15]
  interval_cases c <;> rfl

end CFSG.Certificates.TwDce3.Words

end
