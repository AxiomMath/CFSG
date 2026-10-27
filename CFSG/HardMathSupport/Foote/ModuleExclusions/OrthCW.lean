module

public import Mathlib.FieldTheory.ChevalleyWarning

public section

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

open Module

section

variable {V : Type} [AddCommGroup V] {K : Type} [Field K] [Module K V]

theorem bil_sum_sum (B : LinearMap.BilinForm K V) {m : ℕ} (x : Fin m → K) (z : Fin m → V) :
    B (∑ i, x i • z i) (∑ i, x i • z i) = ∑ i, ∑ j, B (z i) (z j) * (x i * x j) := by
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

noncomputable def quadPoly (B : LinearMap.BilinForm K V) {m : ℕ} (z : Fin m → V) :
    MvPolynomial (Fin m) K :=
  ∑ i, ∑ j, MvPolynomial.C (B (z i) (z j)) * (MvPolynomial.X i * MvPolynomial.X j)

theorem eval_quadPoly (B : LinearMap.BilinForm K V) {m : ℕ} (z : Fin m → V) (x : Fin m → K) :
    MvPolynomial.eval x (quadPoly B z) = B (∑ i, x i • z i) (∑ i, x i • z i) := by
  rw [bil_sum_sum]
  simp only [quadPoly, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]

theorem totalDegree_quadPoly_le (B : LinearMap.BilinForm K V) {m : ℕ} (z : Fin m → V) :
    (quadPoly B z).totalDegree ≤ 2 := by
  unfold quadPoly
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
  have h1 : (MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin m) K).totalDegree ≤ 2 := by
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact h1

variable [Finite K]

theorem exists_singular_comb (B : LinearMap.BilinForm K V) {m : ℕ} (hm : 3 ≤ m) (z : Fin m → V) :
    ∃ x : Fin m → K, x ≠ 0 ∧ B (∑ i, x i • z i) (∑ i, x i • z i) = 0 := by
  classical
  have := Fintype.ofFinite K
  have hdeg : (quadPoly B z).totalDegree < Fintype.card (Fin m) := by
    have := totalDegree_quadPoly_le B z
    simp only [Fintype.card_fin]
    omega
  have hdvd := char_dvd_card_solutions (ringChar K) hdeg
  by_contra hcon
  have hcon' : ∀ x : Fin m → K, B (∑ i, x i • z i) (∑ i, x i • z i) = 0 → x = 0 := fun x hx => by
    by_contra hne
    exact hcon ⟨x, hne, hx⟩
  have h0 : MvPolynomial.eval (0 : Fin m → K) (quadPoly B z) = 0 := by
    rw [eval_quadPoly]
    simp
  have hpos : 0 < Fintype.card {x : Fin m → K // MvPolynomial.eval x (quadPoly B z) = 0} :=
    Fintype.card_pos_iff.mpr ⟨⟨0, h0⟩⟩
  have hone : Fintype.card {x : Fin m → K // MvPolynomial.eval x (quadPoly B z) = 0} ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    rw [eval_quadPoly] at hx hy
    exact Subtype.ext ((hcon' x hx).trans (hcon' y hy).symm)
  have hle := Nat.le_of_dvd hpos hdvd
  have h1 := CharP.ringChar_ne_one (R := K)
  have h2 := CharP.ringChar_ne_zero_of_finite K
  omega

theorem exists_singular_of_injective (B : LinearMap.BilinForm K V) {P : Type} [AddCommGroup P]
    [Module K P] [FiniteDimensional K P] (F : P →ₗ[K] V)
    (hP : 3 ≤ finrank K P) : ∃ p : P, p ≠ 0 ∧ B (F p) (F p) = 0 := by
  let b : Basis (Fin (finrank K P)) K P := finBasis K P
  obtain ⟨x, hx0, hx⟩ := exists_singular_comb B hP (fun i => F (b i))
  refine ⟨∑ i, x i • b i, ?_, ?_⟩
  · intro h
    apply hx0
    have := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at this
    funext i
    exact this x h i
  · rw [map_sum]
    simpa [map_smul] using hx

end

end CFSG.HardMathSupport.Foote.ModuleExclusions
