module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

theorem eq_of_transvection_rel (σ : K →+* K) {B B' : Matrix ι ι K} (hBB' : B' * B = 1)
    {a b : ι} (hab : a ≠ b)
    (h : ∀ t : K, B * (1 + Matrix.single a b (σ t)) = (1 + Matrix.single a b t) * B) :
    ∀ t : K, σ t = t := by
  have hc : ∀ t : K, B * Matrix.single a b (σ t) = Matrix.single a b t * B := fun t => by
    have h1 := h t
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul] at h1
    exact add_left_cancel h1
  have e1 : ∀ x, x ≠ a → B x a = 0 := by
    intro x hx
    have h3 := congrFun (congrFun (hc 1) x) b
    rw [map_one, Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne 1 a b x b hx] at h3
    simpa using h3
  have e2 : ∀ t : K, B a a * σ t = t * B b b := fun t => by
    have h3 := congrFun (congrFun (hc t) a) b
    rwa [Matrix.mul_single_apply_same, Matrix.single_mul_apply_same] at h3
  have hBaa : B a a ≠ 0 := by
    intro h0
    have h1 := congrFun (congrFun hBB' a) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a] at h1
    · rw [h0, mul_zero, Matrix.one_apply_eq] at h1
      exact zero_ne_one h1
    · intro x _ hx
      rw [e1 x hx, mul_zero]
    · intro hx
      exact absurd (Finset.mem_univ a) hx
  have hdiag : B a a = B b b := by
    have h3 := e2 1
    rwa [map_one, mul_one, one_mul] at h3
  intro t
  have h3 := e2 t
  rw [← hdiag] at h3
  exact mul_left_cancel₀ hBaa (h3.trans (mul_comm _ _))

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp
