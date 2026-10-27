module

public import Certificates.Data.Kernel.S1277K7255
public import CFSG.Certificates.Kernel.S1277KGmSound
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

public section

namespace CFSG.KS.C7255

open CFSG.Quasithin.H13.S127.Mod CFSG.KC.S1277ML CFSG.KC.S1277Gm CFSG.KC.C7255 CFSG.KS.S1277Gm

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem cntL_eq (f : ℕ → Bool) : ∀ l : List ℕ, cntL f l = (l.filter f).length
  | [] => rfl
  | x :: xs => by
    change Bool.rec (motive := fun _ => ℕ) (cntL f xs) (Nat.succ (cntL f xs)) (f x) = _
    rw [List.filter_cons, cntL_eq f xs]
    cases f x <;> simp

theorem beq_nat (a b : ℕ) : Nat.beq a b = (a == b) :=
  Bool.eq_iff_iff.2 (by simp [Nat.beq_eq])

theorem stab_sound (Q : List ℕ) (hQ : nm6 = Q.map B6.ofP) (c : ℕ) (h : Nat.ble (stabK Q c) 8 = true) :
    (stabC1 c).length ≤ 8 := by
  rw [stabC1, hQ, List.filter_map, List.length_map]
  rw [stabK, cntL_eq] at h
  have e : Q.filter ((fun B => B.app c == c && B.app 1 == 1) ∘ B6.ofP) =
      Q.filter (fun p => andB (Nat.beq (appP p c) c) (Nat.beq (appP p 1) 1)) :=
    List.filter_congr fun p _ => by simp only [Function.comp, andB_eq, beq_nat, appP_eq]
  rw [e]
  exact Nat.le_of_ble_eq_true h

theorem fresh_iff (x : Fin 6) (L : List (Fin 6)) : fresh x L = true ↔ x ∉ L := by
  simp [fresh]

theorem mem_fins (x : Fin 6) : x ∈ fins := by
  revert x
  decide

theorem fins_eq : fins = List.finRange 6 := by decide

theorem cyc_sound (h : cycK = true) :
    ∀ l ∈ perms6, ∀ b < 7, cycOK b (fl l) = true → cycMoved b (fl l) = true →
      l = List.finRange 6 := by
  intro l hl b hb hok hmov
  have hp : l.Perm (List.finRange 6) := List.mem_permutations.1 hl
  have hlen : l.length = 6 := by rw [hp.length_eq, List.length_finRange]
  have hnd : l.Nodup := hp.nodup_iff.2 (List.nodup_finRange 6)
  obtain ⟨a0, a1, a2, a3, a4, a5, rfl⟩ :
      ∃ a0 a1 a2 a3 a4 a5, l = [a0, a1, a2, a3, a4, a5] := by
    match l, hlen with
    | [a0, a1, a2, a3, a4, a5], _ => exact ⟨a0, a1, a2, a3, a4, a5, rfl⟩
  have f1 : fresh a1 [a0] = true := by
    rw [fresh_iff]
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    subst hm
    simp at hnd
  have f2 : fresh a2 [a0, a1] = true := by
    rw [fresh_iff]
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp at hnd
  have f3 : fresh a3 [a0, a1, a2] = true := by
    rw [fresh_iff]
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp at hnd
  have f4 : fresh a4 [a0, a1, a2, a3] = true := by
    rw [fresh_iff]
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> simp at hnd
  have f5 : fresh a5 [a0, a1, a2, a3, a4] = true := by
    rw [fresh_iff]
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> simp at hnd
  unfold cycK at h
  rw [List.all_eq_true] at h
  have h0 := h a0 (mem_fins a0)
  rw [List.all_eq_true] at h0
  have h1 := h0 a1 (mem_fins a1)
  rw [f1, Bool.not_true, Bool.false_or, List.all_eq_true] at h1
  have h2 := h1 a2 (mem_fins a2)
  rw [f2, Bool.not_true, Bool.false_or, List.all_eq_true] at h2
  have h3 := h2 a3 (mem_fins a3)
  rw [f3, Bool.not_true, Bool.false_or, List.all_eq_true] at h3
  have h4 := h3 a4 (mem_fins a4)
  rw [f4, Bool.not_true, Bool.false_or, List.all_eq_true] at h4
  have h5 := h4 a5 (mem_fins a5)
  rw [f5, Bool.not_true, Bool.false_or] at h5
  unfold cycT at h5
  rw [List.all_eq_true] at h5
  have h6 := h5 b (List.mem_range.2 hb)
  rw [hok, hmov, Bool.not_true, Bool.false_or, Bool.false_or, beq_iff_eq] at h6
  rw [h6, fins_eq]

end CFSG.KS.C7255

end
