module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.Algebra.Polynomial.SpecificDegree

public section

namespace CFSG.AGLEmbedding.U62ThreeCent

open Polynomial Module

variable {K : Type*} [Field K] {c : K}

theorem irreducible_X_pow_three_sub_C (hc : ∀ x : K, x ^ 3 ≠ c) :
    Irreducible (X ^ 3 - C c : K[X]) := by
  refine irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [natDegree_X_pow_sub_C]
    simp
  · intro x hx
    apply hc x
    simpa [IsRoot, sub_eq_zero] using hx

theorem monic_X_pow_three_sub_C : (X ^ 3 - C c : K[X]).Monic :=
  monic_X_pow_sub_C c (by norm_num)

theorem natDegree_X_pow_three_sub_C : (X ^ 3 - C c : K[X]).natDegree = 3 :=
  natDegree_X_pow_sub_C

section Endomorphism

variable {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M]
  {g : M →ₗ[K] M}

omit [FiniteDimensional K M] in
theorem aeval_X_pow_three_sub_C (hg : g ^ 3 = c • 1) : aeval g (X ^ 3 - C c : K[X]) = 0 := by
  simp [hg, Algebra.algebraMap_eq_smul_one]

theorem X_pow_three_sub_C_dvd_charpoly [Nontrivial M] (hc : ∀ x : K, x ^ 3 ≠ c)
    (hg : g ^ 3 = c • 1) : (X ^ 3 - C c : K[X]) ∣ g.charpoly := by
  have h := minpoly.eq_of_irreducible_of_monic (A := K) (x := g) (irreducible_X_pow_three_sub_C hc)
    (aeval_X_pow_three_sub_C hg) monic_X_pow_three_sub_C
  rw [h]
  exact LinearMap.minpoly_dvd_charpoly g

theorem three_le_finrank [Nontrivial M] (hc : ∀ x : K, x ^ 3 ≠ c) (hg : g ^ 3 = c • 1) :
    3 ≤ finrank K M := by
  have h := natDegree_le_of_dvd (X_pow_three_sub_C_dvd_charpoly hc hg)
    (LinearMap.charpoly_monic g).ne_zero
  rwa [natDegree_X_pow_three_sub_C, LinearMap.charpoly_natDegree] at h

theorem det_eq_of_finrank_three (hc : ∀ x : K, x ^ 3 ≠ c) (hg : g ^ 3 = c • 1)
    (hd : finrank K M = 3) : LinearMap.det g = c := by
  have : Nontrivial M := Module.nontrivial_of_finrank_pos (R := K) (by rw [hd]; norm_num)
  have hdvd := X_pow_three_sub_C_dvd_charpoly hc hg
  have heq : g.charpoly = (X ^ 3 - C c : K[X]) :=
    eq_of_monic_of_dvd_of_natDegree_le monic_X_pow_three_sub_C (LinearMap.charpoly_monic g) hdvd
      (by rw [LinearMap.charpoly_natDegree, natDegree_X_pow_three_sub_C, hd])
  have h0 : (X ^ 3 - C c : K[X]).coeff 0 = -c := by
    rw [coeff_sub, coeff_X_pow, coeff_C_zero]
    norm_num
  rw [LinearMap.det_eq_sign_charpoly_coeff, heq, hd, h0]
  ring

end Endomorphism

section SixDimensional

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem det_eq_sq_of_finrank_six (hc : ∀ x : K, x ^ 3 ≠ c) {f : V →ₗ[K] V} (hf : f ^ 3 = c • 1)
    (hd : finrank K V = 6) : LinearMap.det f = c ^ 2 := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by rw [hd]; norm_num)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  set W : Submodule K V := Submodule.span K (Set.range ![v, f v, f (f v)]) with hW
  have hv3 : f (f (f v)) = c • v := by
    have := congrArg (fun g : V →ₗ[K] V => g v) hf
    simpa [pow_succ] using this
  have hmem : ∀ i, ![v, f v, f (f v)] i ∈ W := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hinv : W ≤ W.comap f := by
    rw [hW, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hmem 1
    · exact hmem 2
    · show f (f (f v)) ∈ W
      rw [hv3]
      exact W.smul_mem c (hmem 0)
  have hvW : v ∈ W := hmem 0
  have hW3 : finrank K W ≤ 3 := by
    have := finrank_range_le_card (R := K) ![v, f v, f (f v)]
    exact this.trans (by simp)
  have hinv' : ∀ x ∈ W, f x ∈ W := fun x hx => hinv hx
  have hres : (f.restrict hinv') ^ 3 = c • 1 := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    have := congrArg (fun g : V →ₗ[K] V => g (w : V)) hf
    simpa [pow_succ] using this
  have : Nontrivial W := ⟨⟨⟨v, hvW⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  have hW3' : finrank K W = 3 := le_antisymm hW3 (three_le_finrank hc hres)
  have hQ : finrank K (V ⧸ W) = 3 := by
    have := Submodule.finrank_quotient_add_finrank W
    omega
  have hqpow : (W.mapQ W f hinv) ^ 3 = c • 1 := by
    refine LinearMap.ext fun q => ?_
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      have h3 : f (f (f x)) = c • x := by
        have := congrArg (fun g : V →ₗ[K] V => g x) hf
        simpa [pow_succ] using this
      simp only [pow_succ, pow_zero, one_mul, Module.End.mul_apply, Submodule.mapQ_apply,
        LinearMap.smul_apply, Module.End.one_apply]
      rw [h3]
      rfl
  rw [LinearMap.det_eq_det_mul_det W f hinv, det_eq_of_finrank_three hc hres hW3',
    det_eq_of_finrank_three hc hqpow hQ]
  ring

end SixDimensional

theorem det_eq_sq (hc : ∀ x : K, x ^ 3 ≠ c) {A : Matrix (Fin 6) (Fin 6) K} (hA : A ^ 3 = c • 1) :
    A.det = c ^ 2 := by
  have hf : (Matrix.toLinAlgEquiv' A) ^ 3 = c • 1 := by
    rw [← map_pow, hA, map_smul, map_one]
  have hdet : LinearMap.det (Matrix.toLinAlgEquiv' A) = A.det := LinearMap.det_toLin' A
  rw [← hdet]
  exact det_eq_sq_of_finrank_six hc hf (by simp)

theorem exists_cube_of_det_eq_one_of_pow_three_eq_smul
    {M : Matrix (Fin 6) (Fin 6) K} (hdet : M.det = 1)
    (hM : M ^ 3 = c • (1 : Matrix (Fin 6) (Fin 6) K)) :
    ∃ a : K, a ^ 3 = c := by
  by_contra h
  have hnc : ∀ x : K, x ^ 3 ≠ c := fun x hx => h ⟨x, hx⟩
  have hsq := det_eq_sq hnc hM
  rw [hdet] at hsq
  refine h ⟨c, ?_⟩
  calc c ^ 3 = c * c ^ 2 := by ring
    _ = c * 1 := by rw [← hsq]
    _ = c := by rw [mul_one]

theorem eq_one_of_det_eq_one_of_pow_three_eq_smul_of_char_two_of_not_nine_dvd
    [Finite K] [CharP K 2] (h9 : ¬ 9 ∣ Nat.card Kˣ)
    {M : Matrix (Fin 6) (Fin 6) K} (hdet : M.det = 1)
    (hM : M ^ 3 = c • (1 : Matrix (Fin 6) (Fin 6) K)) : c = 1 := by
  obtain ⟨a, ha⟩ := exists_cube_of_det_eq_one_of_pow_three_eq_smul hdet hM
  have h6 : c ^ 6 = 1 := by
    have h := congrArg Matrix.det hM
    rw [Matrix.det_pow, hdet, one_pow, Matrix.det_smul, Matrix.det_one, mul_one,
      Fintype.card_fin] at h
    exact h.symm
  have hc3 : c ^ 3 = 1 := by
    have h2 : (c ^ 3) ^ 2 = (1 : K) ^ 2 := by
      rw [← pow_mul, show 3 * 2 = 6 by norm_num, h6, one_pow]
    exact CharTwo.sq_inj.mp h2
  have ha9 : a ^ 9 = 1 := by
    rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, ha, hc3]
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at ha
    rw [← ha] at h6
    have h01 : (0 : K) = 1 := by simpa using h6
    exact zero_ne_one h01
  set u : Kˣ := Units.mk0 a ha0 with hu
  have hu9 : u ^ 9 = 1 := by
    rw [hu]
    apply Units.ext
    simp [ha9]
  have hdvd9 : orderOf u ∣ 9 := orderOf_dvd_of_pow_eq_one hu9
  have hdvdN : orderOf u ∣ Nat.card Kˣ := orderOf_dvd_natCard u
  have hdvd : orderOf u ∣ 3 ^ 2 := by
    rw [show 3 ^ 2 = 9 by norm_num]
    exact hdvd9
  obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases k
  · have hk1 : orderOf u = 1 := by simpa using hk
    have hu1 : u = 1 := orderOf_eq_one_iff.mp hk1
    have ha1 : a = 1 := by
      have := congrArg Units.val hu1
      simpa [hu] using this
    rw [← ha, ha1, one_pow]
  · have hk3 : orderOf u = 3 := by simpa using hk
    have hu3 : u ^ 3 = 1 := by simpa [hk3] using pow_orderOf_eq_one u
    have ha3 : a ^ 3 = 1 := by
      have := congrArg Units.val hu3
      simpa [hu] using this
    rw [← ha, ha3]
  · exfalso
    have hk9 : orderOf u = 9 := by simpa using hk
    exact h9 (by rw [← hk9]; exact hdvdN)

end CFSG.AGLEmbedding.U62ThreeCent
