module

public import Mathlib.Data.Nat.Totient
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.L32MatK

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open Matrix

abbrev Mat3 := Matrix (Fin 3) (Fin 3) (ZMod 2)

abbrev centMat (t : Mat3) : Finset Mat3 := Finset.univ.filter (fun x => x * t = t * x ∧ x.det ≠ 0)

open L32K in
theorem card_centMat : ∀ t : Mat3, t * t = 1 → t ≠ 1 → (centMat t).card = 8 := by
  intro t h1 h2
  rw [← toM_ofM t] at h1 h2 ⊢
  have h := of_all chkCent_ok (ofM t)
  rw [(invB_iff _).2 ⟨h1, h2⟩, Bool.not_true, Bool.false_or, beq_iff_eq] at h
  rw [← h]
  exact card_filter_toM _ _ fun x => (centB_iff _ x).symm

set_option synthInstance.maxHeartbeats 400000 in
open L32K in
theorem eq_of_mem_center_centMat :
    ∀ t ∈ (Finset.univ.filter (fun t : Mat3 => t * t = 1 ∧ t ≠ 1)),
      ∀ x ∈ centMat t, (∀ y ∈ centMat t, x * y = y * x) → x = 1 ∨ x = t := by
  intro t ht x hx hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht hx
  rw [← toM_ofM t] at ht hx hc ⊢
  rw [← toM_ofM x] at hx hc ⊢
  have h := of_all chkCenter_ok (ofM t)
  rw [(invB_iff _).2 ht, Bool.not_true, Bool.false_or] at h
  have h' := List.all_eq_true.1 h (ofM x) (mem_all512 _)
  have hy : (all512.all fun y => !centB (ofM t) y ||
      eqB (mulB (ofM x) y) (mulB y (ofM x))) = true := by
    refine List.all_eq_true.2 fun y _ => ?_
    cases hcy : centB (ofM t) y
    · rfl
    · rw [Bool.not_true, Bool.false_or, eqB_iff, toM_mulB, toM_mulB]
      exact hc (toM y) (by simpa using (centB_iff _ _).1 hcy)
  simp only [(centB_iff _ _).2 hx, hy, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    eqB_iff, toM_oneB] at h'
  exact h'

open L32K in
theorem exists_invMat : ∀ c : Mat3, c * c * c = 1 → c ≠ 1 →
    ∃ y : Mat3, y * y = 1 ∧ y ≠ 1 ∧ y * c = c * c * y := by
  intro c h1 h2
  rw [← toM_ofM c] at h1 h2 ⊢
  have h := of_all chkInv_ok (ofM c)
  rw [(ord3B_iff _).2 ⟨h1, h2⟩, Bool.not_true, Bool.false_or, List.any_eq_true] at h
  obtain ⟨y, -, hy⟩ := h
  rw [Bool.and_eq_true, invB_iff, eqB_iff, toM_mulB, toM_mulB, toM_mulB] at hy
  exact ⟨toM y, hy.1.1, hy.1.2, hy.2⟩

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
