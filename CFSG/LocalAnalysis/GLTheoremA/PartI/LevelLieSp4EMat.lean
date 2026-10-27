module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4E

open Matrix

abbrev Ix : Type := Fin 2 ⊕ Fin 2

@[expose] def plane : Ix → Fin 2
  | .inl i => i
  | .inr i => i

@[expose] def pos : Ix → Fin 2
  | .inl _ => 0
  | .inr _ => 1

@[expose] def planeMat {K : Type} [Field K] (M : Fin 2 → Matrix (Fin 2) (Fin 2) K) : Matrix Ix Ix K :=
  Matrix.of fun a b => if plane a = plane b then M (plane a) (pos a) (pos b) else 0

@[expose] def JJ (K : Type) [Field K] : Matrix Ix Ix K := Matrix.fromBlocks 0 1 (-1) 0

@[expose] def bf {K : Type} [Field K] (x y : Ix → K) : K := x ⬝ᵥ (JJ K *ᵥ y)

@[expose] def Pm {K : Type} [Field K] (A : Matrix Ix Ix K) : Matrix Ix Ix K := A * A + A + 1

@[expose] def Tmat {K : Type} [Field K] (c : K) : Matrix (Fin 2) (Fin 2) K := !![0, c⁻¹; c, 1]

section Char2

variable {K : Type} [Field K] [CharP K 2]

theorem add_self_mat (M : Matrix Ix Ix K) : M + M = 0 := CharTwo.add_self_eq_zero M

theorem add_self_vec (x : Ix → K) : x + x = 0 := funext fun i => CharTwo.add_self_eq_zero (x i)

theorem JJ_transpose : (JJ K)ᵀ = JJ K := by
  unfold JJ
  rw [Matrix.fromBlocks_transpose]
  simp only [Matrix.transpose_zero, Matrix.transpose_one, Matrix.transpose_neg, CharTwo.neg_eq]

theorem JJ_mul_JJ : JJ K * JJ K = 1 := by
  unfold JJ
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.one_mul, Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero,
    Matrix.neg_mul, Matrix.mul_neg, neg_neg, neg_zero, CharTwo.neg_eq]
  exact Matrix.fromBlocks_one

theorem bf_comm (x y : Ix → K) : bf x y = bf y x := by
  unfold bf
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, JJ_transpose, dotProduct_comm]

theorem bf_self_zero (x : Ix → K) : bf x x = 0 := by
  unfold bf JJ
  simp [dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.mulVec, Matrix.fromBlocks]
  ring

theorem bf_smul_right (x y : Ix → K) (c : K) : bf x (c • y) = c * bf x y := by
  unfold bf
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem bf_add_right (x y z : Ix → K) : bf x (y + z) = bf x y + bf x z := by
  unfold bf
  rw [Matrix.mulVec_add, dotProduct_add]

theorem bf_eq_zero_of_forall (x : Ix → K) (h : ∀ y, bf x y = 0) : x = 0 := by
  apply dotProduct_eq_zero
  intro z
  have h1 := h (JJ K *ᵥ z)
  unfold bf at h1
  rw [Matrix.mulVec_mulVec, JJ_mul_JJ, Matrix.one_mulVec] at h1
  exact h1

theorem no_root [Fintype K] (hcard : Fintype.card K = 8) (x : K) : x * x + x + 1 ≠ 0 := by
  intro h
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h3 : x ^ 3 = 1 := by
    have : x ^ 3 + 1 = 0 := by linear_combination (x + 1) * h - (x ^ 2 + x) * h2
    linear_combination this - h2
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at h
  have h7 : x ^ 7 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one x hx0
    rwa [hcard] at this
  have h1 : x ^ (Nat.gcd 3 7) = 1 := (pow_gcd_eq_one).2 ⟨h3, h7⟩
  have hx1 : x = 1 := by
    have : Nat.gcd 3 7 = 1 := by norm_num
    rw [this, pow_one] at h1
    exact h1
  rw [hx1] at h
  have h1' : (1 : K) = 0 := by
    linear_combination h - h2
  exact one_ne_zero h1'

end Char2

section Symp

variable {K : Type} [Field K] [CharP K 2]

theorem mulVec_dot_eq (M : Matrix Ix Ix K) (x z : Ix → K) :
    (M *ᵥ x) ⬝ᵥ z = x ⬝ᵥ (Mᵀ *ᵥ z) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose]

theorem vec_add_self_add (x y : Ix → K) : x + y + x = y := by
  rw [show x + y + x = y + (x + x) by abel, add_self_vec, add_zero]

theorem sp_T {A : Matrix Ix Ix K} (hsp : Aᵀ * JJ K * A = JJ K) (h3 : A * A * A = 1) :
    Aᵀ * JJ K = JJ K * (A * A) := by
  calc Aᵀ * JJ K = Aᵀ * JJ K * (A * A * A) := by rw [h3, mul_one]
    _ = (Aᵀ * JJ K * A) * (A * A) := by simp only [mul_assoc]
    _ = JJ K * (A * A) := by rw [hsp]

theorem A4_eq {A : Matrix Ix Ix K} (h3 : A * A * A = 1) : (A * A) * (A * A) = A := by
  calc (A * A) * (A * A) = (A * A * A) * A := by simp only [mul_assoc]
    _ = A := by rw [h3, one_mul]

theorem A3_right {A : Matrix Ix Ix K} (h3 : A * A * A = 1) : A * (A * A) = 1 := by
  rw [← mul_assoc, h3]

theorem Pm_adj {A : Matrix Ix Ix K} (hsp : Aᵀ * JJ K * A = JJ K) (h3 : A * A * A = 1) :
    (Pm A)ᵀ * JJ K = JJ K * Pm A := by
  have hT := sp_T hsp h3
  have h4 := A4_eq h3
  have h5 : Aᵀ * Aᵀ * JJ K = JJ K * (A * A) * (A * A) := by
    calc Aᵀ * Aᵀ * JJ K = Aᵀ * (Aᵀ * JJ K) := by rw [mul_assoc]
      _ = Aᵀ * (JJ K * (A * A)) := by rw [hT]
      _ = (Aᵀ * JJ K) * (A * A) := by rw [mul_assoc]
      _ = JJ K * (A * A) * (A * A) := by rw [hT]
  unfold Pm
  rw [Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_one,
    Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_one]
  rw [h5, hT, mul_assoc (JJ K) (A * A) (A * A), h4]
  abel

theorem Pm_idem {A : Matrix Ix Ix K} (h3 : A * A * A = 1) : Pm A * Pm A = Pm A := by
  have h4 := A4_eq h3
  have h2 := A3_right h3
  unfold Pm
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul, mul_assoc, h4, h2]
  calc _ = (A * A + A + 1) + (A * A + A * A) + (A + A) + (1 + 1) := by abel
    _ = A * A + A + 1 := by rw [add_self_mat, add_self_mat, add_self_mat, add_zero, add_zero,
        add_zero]

theorem Pm_comm (A : Matrix Ix Ix K) : A * Pm A = Pm A * A := by
  unfold Pm
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, mul_assoc]

theorem A_mul_Pm {A : Matrix Ix Ix K} (h3 : A * A * A = 1) : A * Pm A = Pm A := by
  unfold Pm
  rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_one, A3_right h3]
  abel

@[expose] def Wsp (A : Matrix Ix Ix K) : Submodule K (Ix → K) := LinearMap.ker (Matrix.mulVecLin (Pm A))

theorem mem_Wsp {A : Matrix Ix Ix K} {x : Ix → K} : x ∈ Wsp A ↔ Pm A *ᵥ x = 0 := by
  simp [Wsp, LinearMap.mem_ker]

theorem Pm_mulVec_Pm {A : Matrix Ix Ix K} (h3 : A * A * A = 1) (x : Ix → K) :
    Pm A *ᵥ (Pm A *ᵥ x) = Pm A *ᵥ x := by
  rw [Matrix.mulVec_mulVec, Pm_idem h3]

theorem A_mulVec_Pm {A : Matrix Ix Ix K} (h3 : A * A * A = 1) (x : Ix → K) :
    A *ᵥ (Pm A *ᵥ x) = Pm A *ᵥ x := by
  rw [Matrix.mulVec_mulVec, A_mul_Pm h3]

theorem Pm_mulVec_A {A : Matrix Ix Ix K} (h3 : A * A * A = 1) (x : Ix → K) :
    Pm A *ᵥ (A *ᵥ x) = A *ᵥ (Pm A *ᵥ x) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Pm_comm A]

theorem Wsp_A {A : Matrix Ix Ix K} (h3 : A * A * A = 1) {x : Ix → K} (hx : x ∈ Wsp A) :
    A *ᵥ x ∈ Wsp A := by
  rw [mem_Wsp] at hx ⊢
  rw [Pm_mulVec_A h3, hx, Matrix.mulVec_zero]

theorem Pm_fix_of_fixed {A : Matrix Ix Ix K} {x : Ix → K}
    (hx : A *ᵥ x = x) : Pm A *ᵥ x = x := by
  unfold Pm
  rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hx, hx,
    add_assoc, add_self_vec, add_zero]

theorem split_vec {A : Matrix Ix Ix K} (x : Ix → K) :
    x = Pm A *ᵥ x + (x + Pm A *ᵥ x) := by
  rw [show Pm A *ᵥ x + (x + Pm A *ᵥ x) = x + (Pm A *ᵥ x + Pm A *ᵥ x) by abel, add_self_vec,
    add_zero]

theorem Wsp_split {A : Matrix Ix Ix K} (h3 : A * A * A = 1) (x : Ix → K) :
    x + Pm A *ᵥ x ∈ Wsp A := by
  rw [mem_Wsp, Matrix.mulVec_add, Pm_mulVec_Pm h3, add_self_vec]

theorem bf_Pm_left {A : Matrix Ix Ix K} (hsp : Aᵀ * JJ K * A = JJ K) (h3 : A * A * A = 1)
    (x y : Ix → K) : bf (Pm A *ᵥ x) y = bf x (Pm A *ᵥ y) := by
  unfold bf
  rw [mulVec_dot_eq, Matrix.mulVec_mulVec, Pm_adj hsp h3, ← Matrix.mulVec_mulVec]

theorem bf_fix_W {A : Matrix Ix Ix K} (hsp : Aᵀ * JJ K * A = JJ K) (h3 : A * A * A = 1)
    {x y : Ix → K} (hx : Pm A *ᵥ x = x) (hy : Pm A *ᵥ y = 0) : bf x y = 0 := by
  calc bf x y = bf (Pm A *ᵥ x) y := by rw [hx]
    _ = bf x (Pm A *ᵥ y) := bf_Pm_left hsp h3 x y
    _ = 0 := by rw [hy]; unfold bf; simp

theorem bf_fix_W' {A : Matrix Ix Ix K} (hsp : Aᵀ * JJ K * A = JJ K) (h3 : A * A * A = 1)
    {x y : Ix → K} (hx : Pm A *ᵥ x = x) (hy : y ∈ Wsp A) : bf x y = 0 :=
  bf_fix_W hsp h3 hx (mem_Wsp.1 hy)

theorem bf_fix_W'' {A : Matrix Ix Ix K} (hsp : Aᵀ * JJ K * A = JJ K) (h3 : A * A * A = 1)
    {x y : Ix → K} (hx : Pm A *ᵥ x = x) (hy : y ∈ Wsp A) : bf y x = 0 := by
  rw [bf_comm]; exact bf_fix_W' hsp h3 hx hy

end Symp

end CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4E
