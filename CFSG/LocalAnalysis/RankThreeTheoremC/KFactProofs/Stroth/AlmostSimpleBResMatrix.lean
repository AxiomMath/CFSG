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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Matrix

theorem exists_vecMulVec_of_sq_zero {K : Type*} [Field K] {N : Matrix (Fin 3) (Fin 3) K}
    (hN2 : N * N = 0) (hN0 : N ≠ 0) :
    ∃ c ℓ : Fin 3 → K, N = vecMulVec c ℓ ∧ c ≠ 0 ∧ ℓ ≠ 0 ∧ ℓ ⬝ᵥ c = 0 := by
  classical
  set f : (Fin 3 → K) →ₗ[K] (Fin 3 → K) := Matrix.mulVecLin N with hf
  have hrk : LinearMap.range f ≤ LinearMap.ker f := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    simp only [hf, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hN2, Matrix.zero_mulVec]
  have h1 := Submodule.finrank_mono hrk
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fin_fun] at h2
  have hne : ∃ x, f x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hN0
    ext i j
    have := congrFun (hcon (Pi.single j 1)) i
    simpa [hf, Matrix.mulVec_single_one] using this
  have hpos : 0 < Module.finrank K (LinearMap.range f) := by
    obtain ⟨x, hx⟩ := hne
    rw [Module.finrank_pos_iff_exists_ne_zero]
    exact ⟨⟨f x, LinearMap.mem_range_self f x⟩, fun h => hx (by simpa using congrArg Subtype.val h)⟩
  have h3 : Module.finrank K (LinearMap.range f) = 1 := by omega
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.1 h3
  set c : Fin 3 → K := (v : Fin 3 → K) with hc
  have hc0 : c ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hcol : ∀ j, ∃ a : K, a • c = N *ᵥ Pi.single j 1 := fun j => by
    obtain ⟨a, ha⟩ := hv ⟨f (Pi.single j 1), LinearMap.mem_range_self f _⟩
    exact ⟨a, congrArg Subtype.val ha⟩
  choose ℓ hℓ using hcol
  have hN : N = vecMulVec c ℓ := by
    ext i j
    have := congrFun (hℓ j) i
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_single_one] at this
    rw [vecMulVec_apply]
    simp only [Matrix.col_apply] at this
    rw [mul_comm, this]
  have hℓ0 : ℓ ≠ 0 := by
    rintro rfl
    apply hN0
    rw [hN]
    simp
  refine ⟨c, ℓ, hN, hc0, hℓ0, ?_⟩
  have hsq : vecMulVec c ((ℓ ⬝ᵥ c) • ℓ) = 0 := by
    rw [← vecMulVec_mul_vecMulVec, ← hN, hN2]
  rw [vecMulVec_eq_zero] at hsq
  rcases hsq with h | h
  · exact absurd h hc0
  · rcases smul_eq_zero.1 h with h | h
    · exact h
    · exact absurd h hℓ0

theorem eigen_of_commute_vecMulVec {K : Type*} [Field K] {A : Matrix (Fin 3) (Fin 3) K}
    {c ℓ : Fin 3 → K} (hc0 : c ≠ 0) (hℓ0 : ℓ ≠ 0)
    (h : A * vecMulVec c ℓ = vecMulVec c ℓ * A) :
    ∃ β : K, A *ᵥ c = β • c ∧ ℓ ᵥ* A = β • ℓ := by
  obtain ⟨i, hi⟩ : ∃ i, ℓ i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hℓ0 (funext hcon)
  obtain ⟨k, hk⟩ : ∃ k, c k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hc0 (funext hcon)
  have hentry : ∀ a b, (A *ᵥ c) a * ℓ b = c a * (ℓ ᵥ* A) b := by
    intro a b
    have := congrFun₂ h a b
    rw [mul_vecMulVec, vecMulVec_mul] at this
    simpa [vecMulVec_apply] using this
  set β : K := (ℓ ᵥ* A) i * (ℓ i)⁻¹ with hβ
  have hAc : A *ᵥ c = β • c := by
    funext a
    have := hentry a i
    simp only [Pi.smul_apply, smul_eq_mul, hβ]
    field_simp
    linear_combination this
  refine ⟨β, hAc, ?_⟩
  funext b
  have := hentry k b
  rw [show (A *ᵥ c) k = β * c k by rw [hAc]; rfl] at this
  simp only [Pi.smul_apply, smul_eq_mul]
  apply mul_left_cancel₀ hk
  linear_combination -this

theorem exists_eigen_projection {K : Type*} [Field K] [CharP K 2] {A : Matrix (Fin 3) (Fin 3) K}
    {β : K} (hβ0 : β ≠ 0) (hA3 : A * A * A = (β ^ 3) • (1 : Matrix (Fin 3) (Fin 3) K)) :
    ∃ π : Matrix (Fin 3) (Fin 3) K, A * π = β • π ∧ π * A = β • π ∧
      (∀ w : Fin 3 → K, A *ᵥ w = β • w → π *ᵥ w = w) ∧
      (∀ u : Fin 3 → K, u ᵥ* A = β • u → u ᵥ* π = u) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  set P₀ : Matrix (Fin 3) (Fin 3) K := A * A + β • A + (β ^ 2) • (1 : Matrix (Fin 3) (Fin 3) K)
    with hP₀
  set π : Matrix (Fin 3) (Fin 3) K := (β ^ 2)⁻¹ • P₀ with hπ
  have hAP : A * P₀ = β • P₀ := by
    have e1 : A * P₀ = A * A * A + β • (A * A) + (β ^ 2) • A := by
      simp only [hP₀, mul_add, Matrix.mul_smul, mul_one, mul_assoc]
    have e2 : β • P₀ = β • (A * A) + (β ^ 2) • A + (β ^ 3) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      simp only [hP₀, smul_add, smul_smul]
      congr 2 <;> ring_nf
    rw [e1, e2, hA3]
    abel
  have hPA : P₀ * A = A * P₀ := by
    simp only [hP₀, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one,
      mul_assoc]
  have hβ2 : β ^ 2 + β ^ 2 + β ^ 2 = β ^ 2 := by linear_combination (β ^ 2) * h2
  refine ⟨π, ?_, ?_, ?_, ?_⟩
  · simp only [hπ, Matrix.mul_smul, hAP, smul_comm β]
  · simp only [hπ, Matrix.smul_mul, hPA, hAP, smul_comm β]
  · intro w hw
    have e : P₀ *ᵥ w = A *ᵥ (A *ᵥ w) + β • (A *ᵥ w) + (β ^ 2) • w := by
      simp only [hP₀, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        Matrix.mulVec_mulVec]
    have hPw : P₀ *ᵥ w = (β ^ 2) • w := by
      rw [e, hw, Matrix.mulVec_smul, hw, smul_smul, ← add_smul, ← add_smul, ← pow_two, hβ2]
    rw [hπ, Matrix.smul_mulVec, hPw, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hβ0), one_smul]
  · intro u hu
    have e : u ᵥ* P₀ = (u ᵥ* A) ᵥ* A + β • (u ᵥ* A) + (β ^ 2) • u := by
      simp only [hP₀, Matrix.vecMul_add, Matrix.vecMul_smul, Matrix.vecMul_one,
        Matrix.vecMul_vecMul]
    have hPu : u ᵥ* P₀ = (β ^ 2) • u := by
      rw [e, hu, Matrix.smul_vecMul, hu, smul_smul, ← add_smul, ← add_smul, ← pow_two, hβ2]
    rw [hπ, Matrix.vecMul_smul, hPu, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hβ0), one_smul]

theorem exists_opposite_nilpotent {K : Type*} [Field K] [CharP K 2]
    {A N : Matrix (Fin 3) (Fin 3) K} (hN2 : N * N = 0) (hN0 : N ≠ 0) (hAN : A * N = N * A)
    {lam : K} (hlam : lam ≠ 0) (hA3 : A * A * A = lam • (1 : Matrix (Fin 3) (Fin 3) K)) :
    ∃ N' : Matrix (Fin 3) (Fin 3) K, N' * N' = 0 ∧ N * N' * N = N ∧ N' * N * N' = N' ∧
      A * N' = N' * A := by
  classical
  obtain ⟨c, ℓ, hN, hc0, hℓ0, hℓc⟩ := exists_vecMulVec_of_sq_zero hN2 hN0
  obtain ⟨i, hi⟩ : ∃ i, ℓ i ≠ 0 := by
    by_contra h
    push Not at h
    exact hℓ0 (funext h)
  obtain ⟨k, hk⟩ : ∃ k, c k ≠ 0 := by
    by_contra h
    push Not at h
    exact hc0 (funext h)
  obtain ⟨β, hAc, hℓA⟩ := eigen_of_commute_vecMulVec hc0 hℓ0 (hN ▸ hAN)
  have hβ3 : β ^ 3 = lam := by
    have h1 : (A * A * A) *ᵥ c = lam • c := by
      rw [hA3, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h2' : (A * A * A) *ᵥ c = (β ^ 3) • c := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hAc]
      simp [Matrix.mulVec_smul, hAc, smul_smul, pow_succ, mul_assoc]
    have := congrFun (h2'.symm.trans h1) k
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hk this
  have hβ0 : β ≠ 0 := by
    intro h
    rw [h] at hβ3
    simp at hβ3
    exact hlam hβ3.symm
  obtain ⟨π, hAπ, hπA, hπw, hℓπ⟩ := exists_eigen_projection hβ0 (hβ3 ▸ hA3)
  set x₀ : Fin 3 → K := Pi.single i (ℓ i)⁻¹ with hx₀def
  have hx₀ : ℓ ⬝ᵥ x₀ = 1 := by
    simp [hx₀def, dotProduct_single, hi]
  set c' : Fin 3 → K := π *ᵥ x₀ with hc'
  have hAc' : A *ᵥ c' = β • c' := by
    rw [hc', Matrix.mulVec_mulVec, hAπ, Matrix.smul_mulVec]
  have hℓc' : ℓ ⬝ᵥ c' = 1 := by
    rw [hc', Matrix.dotProduct_mulVec, hℓπ ℓ hℓA, hx₀]
  set m₀ : Fin 3 → K := Pi.single k (c k)⁻¹ with hm₀def
  have hm₀c : m₀ ⬝ᵥ c = 1 := by
    simp [hm₀def, single_dotProduct, hk]
  set m : Fin 3 → K := m₀ - (m₀ ⬝ᵥ c') • ℓ with hm
  have hmc : m ⬝ᵥ c = 1 := by
    simp only [hm, sub_dotProduct, smul_dotProduct, hm₀c, hℓc]
    simp
  have hmc' : m ⬝ᵥ c' = 0 := by
    simp only [hm, sub_dotProduct, smul_dotProduct, hℓc', smul_eq_mul]
    ring
  set ℓ' : Fin 3 → K := m ᵥ* π with hℓ'
  have hℓ'c : ℓ' ⬝ᵥ c = 1 := by
    rw [hℓ', ← Matrix.dotProduct_mulVec, hπw c hAc, hmc]
  have hℓ'c' : ℓ' ⬝ᵥ c' = 0 := by
    rw [hℓ', ← Matrix.dotProduct_mulVec, hπw c' hAc', hmc']
  have hℓ'A : ℓ' ᵥ* A = β • ℓ' := by
    rw [hℓ', Matrix.vecMul_vecMul, hπA, Matrix.vecMul_smul]
  refine ⟨vecMulVec c' ℓ', ?_, ?_, ?_, ?_⟩
  · rw [vecMulVec_mul_vecMulVec, hℓ'c', zero_smul]
    simp
  · rw [hN, vecMulVec_mul_vecMulVec, hℓc', one_smul, vecMulVec_mul_vecMulVec, hℓ'c, one_smul]
  · rw [hN, vecMulVec_mul_vecMulVec, hℓ'c, one_smul, vecMulVec_mul_vecMulVec, hℓc', one_smul]
  · rw [mul_vecMulVec, vecMulVec_mul, hAc', hℓ'A, smul_vecMulVec, vecMulVec_smul]

section Braid

theorem braid_of_relations {R : Type*} [Ring R] [CharP R 2] {a b : R} (haa : a * a = 0)
    (hbb : b * b = 0) (haba : a * b * a = a) (hbab : b * a * b = b) :
    (1 + a) * (1 + b) * (1 + a) = (1 + b) * (1 + a) * (1 + b) := by
  have e1 : (1 + a) * (1 + b) * (1 + a) =
      1 + (a + a) + a * a + b + b * a + a * b + a * b * a := by noncomm_ring
  have e2 : (1 + b) * (1 + a) * (1 + b) =
      1 + (b + b) + b * b + a + a * b + b * a + b * a * b := by noncomm_ring
  rw [e1, e2, haa, hbb, haba, hbab, CharTwo.add_self_eq_zero a, CharTwo.add_self_eq_zero b]
  abel

end Braid

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
