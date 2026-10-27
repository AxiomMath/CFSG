module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265BU8

open Matrix

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_perm_of_support {M : Matrix ι ι K} (hM : M.det ≠ 0) {α : Type} {a a' : ι → α}
    (h : ∀ l k, M l k ≠ 0 → a' l = a k) : ∃ π : Equiv.Perm ι, ∀ k, a' (π k) = a k := by
  rw [Matrix.det_apply] at hM
  obtain ⟨π, -, hπ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hM
  refine ⟨π, fun k => h (π k) k fun h0 => hπ ?_⟩
  rw [Finset.prod_eq_zero (f := fun i => M (π i) i) (Finset.mem_univ k) h0, smul_zero]

theorem card_fiber_eq_of_support {M : Matrix ι ι K} (hM : M.det ≠ 0) {α : Type} {a a' : ι → α}
    (h : ∀ l k, M l k ≠ 0 → a' l = a k) (x : α) :
    Nat.card {l // a' l = x} = Nat.card {k // a k = x} := by
  obtain ⟨π, hπ⟩ := exists_perm_of_support hM h
  exact (Nat.card_congr (π.subtypeEquiv fun k => by rw [hπ k])).symm

theorem eq_of_mul_diagonal_eq {M : Matrix ι ι K} {a a' : ι → K}
    (h : M * diagonal a = diagonal a' * M) {l k : ι} (hlk : M l k ≠ 0) : a' l = a k := by
  have e := congrFun (congrFun h l) k
  rw [mul_diagonal, diagonal_mul] at e
  apply mul_left_cancel₀ hlk
  calc M l k * a' l = a' l * M l k := mul_comm _ _
    _ = M l k * a k := e.symm

end CFSG.LocalAnalysis.GLTheoremA.S265BU8

end
