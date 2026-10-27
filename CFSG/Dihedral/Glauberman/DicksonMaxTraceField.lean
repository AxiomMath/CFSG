module

public import Mathlib.Algebra.QuaternionBasis
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.Glauberman.Dickson.TraceField

open Matrix
open scoped Quaternion

variable {F : Type*} [Field F]

theorem sq_eq_trace_smul_sub (A : Matrix (Fin 2) (Fin 2) F) :
    A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two,
      ] <;> ring

theorem trace_eq_zero_of_sq {A : Matrix (Fin 2) (Fin 2) F}
    (hdet : A.det = 1) (hA : A * A = -1) : A.trace = 0 := by
  have h := sq_eq_trace_smul_sub A
  rw [hA, hdet, one_smul] at h
  have h' : A.trace • A = 0 := by
    have := congrArg (· + (1 : Matrix (Fin 2) (Fin 2) F)) h
    simpa using this.symm
  by_contra ht
  have hA0 : A = 0 := by
    have := congrArg (A.trace⁻¹ • ·) h'
    simpa [smul_smul, inv_mul_cancel₀ ht] using this
  rw [hA0, Matrix.det_zero] at hdet
  exact zero_ne_one hdet

theorem exists_conj_entries_mem_subfield [Finite F] (h2 : (2 : F) ≠ 0) (K₀ : Subfield F)
    (M : Set (Matrix (Fin 2) (Fin 2) F)) (hM1 : 1 ∈ M)
    (hMmul : ∀ x ∈ M, ∀ y ∈ M, x * y ∈ M) (htr : ∀ x ∈ M, x.trace ∈ K₀)
    {g h : Matrix (Fin 2) (Fin 2) F} (hg : g ∈ M) (hh : h ∈ M) (hgdet : g.det = 1)
    (hhdet : h.det = 1) (hg2 : g * g = -1) (hh2 : h * h = -1) (hgh : h * g = -(g * h)) :
    ∃ P Q : Matrix (Fin 2) (Fin 2) F, P * Q = 1 ∧ Q * P = 1 ∧
      ∀ x ∈ M, ∀ i j, (Q * x * P) i j ∈ K₀ := by
  classical
  have : NeZero (ringChar F) := ⟨CharP.char_ne_zero_of_finite F (ringChar F)⟩
  obtain ⟨a, b, hab, haK, hbK⟩ : ∃ a b : F, a ^ 2 + b ^ 2 = -1 ∧ a ∈ K₀ ∧ b ∈ K₀ := by
    obtain ⟨na, nb, hnab⟩ := CharP.sq_add_sq F (ringChar F) (-1)
    exact ⟨na, nb, by simpa using hnab, natCast_mem K₀ na, natCast_mem K₀ nb⟩
  obtain ⟨t, ht, htK⟩ : ∃ t : F, 2 * t = 1 ∧ t ∈ K₀ :=
    ⟨2⁻¹, mul_inv_cancel₀ h2, K₀.inv_mem (by simp)⟩
  set A₀ : Submodule K₀ (Matrix (Fin 2) (Fin 2) F) := Submodule.span K₀ M
  have hsmulK : ∀ (c : F), c ∈ K₀ → ∀ x ∈ A₀, c • x ∈ A₀ := by
    intro c hc x hx
    exact A₀.smul_mem (⟨c, hc⟩ : K₀) hx
  have hmulA : ∀ x ∈ A₀, ∀ y ∈ A₀, x * y ∈ A₀ := by
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
      induction hy using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span (hMmul x hx y hy)
      | zero => simp
      | add y₁ y₂ _ _ h₁ h₂ => rw [mul_add]; exact A₀.add_mem h₁ h₂
      | smul c y _ hy' => rw [mul_smul_comm]; exact A₀.smul_mem c hy'
    | zero => simp
    | add x₁ x₂ _ _ h₁ h₂ => rw [add_mul]; exact A₀.add_mem h₁ h₂
    | smul c x _ hx' => rw [smul_mul_assoc]; exact A₀.smul_mem c hx'
  have htrA : ∀ x ∈ A₀, x.trace ∈ K₀ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact htr x hx
    | zero => simp
    | add x₁ x₂ _ _ h₁ h₂ => rw [Matrix.trace_add]; exact K₀.add_mem h₁ h₂
    | smul c x _ hx' =>
      rw [Matrix.trace_smul]
      exact K₀.mul_mem c.2 hx'
  have hMA : ∀ x ∈ M, x ∈ A₀ := fun x hx => Submodule.subset_span hx
  let B : QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) F) (-1 : F) 0 (-1) :=
    { i := g
      j := h
      k := g * h
      i_mul_i := by rw [hg2]; simp
      j_mul_j := by rw [hh2]; simp
      i_mul_j := rfl
      j_mul_i := by rw [hgh]; simp }
  let ρ : ℍ[F] →ₐ[F] Matrix (Fin 2) (Fin 2) F := B.liftHom
  have hρ : ∀ q : ℍ[F], ρ q = q.re • (1 : Matrix (Fin 2) (Fin 2) F) + q.imI • g + q.imJ • h +
      q.imK • (g * h) := by
    intro q
    change B.lift q = _
    rw [QuaternionAlgebra.Basis.lift, Algebra.algebraMap_eq_smul_one]
  have hρA : ∀ q : ℍ[F], q.re ∈ K₀ → q.imI ∈ K₀ → q.imJ ∈ K₀ → q.imK ∈ K₀ → ρ q ∈ A₀ := by
    intro q h0 h1 h2' h3
    rw [hρ]
    refine A₀.add_mem (A₀.add_mem (A₀.add_mem ?_ ?_) ?_) ?_
    · exact hsmulK _ h0 _ (hMA _ hM1)
    · exact hsmulK _ h1 _ (hMA _ hg)
    · exact hsmulK _ h2' _ (hMA _ hh)
    · exact hsmulK _ h3 _ (hMA _ (hMmul _ hg _ hh))
  have htrg : g.trace = 0 := trace_eq_zero_of_sq hgdet hg2
  have htrh : h.trace = 0 := trace_eq_zero_of_sq hhdet hh2
  have htrgh : (g * h).trace = 0 := by
    apply trace_eq_zero_of_sq (by rw [Matrix.det_mul, hgdet, hhdet, one_mul])
    calc g * h * (g * h) = g * (h * g) * h := by simp only [mul_assoc]
      _ = -(g * g * (h * h)) := by rw [hgh]; simp only [mul_neg, neg_mul, mul_assoc]
      _ = -1 := by rw [hg2, hh2]; simp
  let e11 : ℍ[F] := ⟨t, a * t, b * t, 0⟩
  let e22 : ℍ[F] := ⟨t, -(a * t), -(b * t), 0⟩
  let e12 : ℍ[F] := ⟨0, b * t, -(a * t), t⟩
  let e21 : ℍ[F] := ⟨0, b * t, -(a * t), -t⟩
  have q1 : e11 * e11 = e11 := by
    refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
    · simp [e11]
      linear_combination (-(t ^ 2)) * hab + (t) * ht
    · simp [e11]
      linear_combination (a * t) * ht
    · simp [e11]
      linear_combination (b * t) * ht
    · simp [e11]
      ring
  have q2 : e11 * e21 = 0 := by
    refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
    · simp [e11, e21]
      ring
    · simp [e11, e21]
      ring
    · simp [e11, e21]
      ring
    · simp [e11, e21]
      linear_combination (-(t ^ 2)) * hab
  have q3 : e21 * e11 = e21 := by
    refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
    · simp [e11, e21]
      ring
    · simp [e11, e21]
      linear_combination (b * t) * ht
    · simp [e11, e21]
      linear_combination (-(a * t)) * ht
    · simp [e11, e21]
      linear_combination (t ^ 2) * hab + (-t) * ht
  have q4 : e21 * e21 = 0 := by
    refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
    · simp [e21]
      linear_combination (-(t ^ 2)) * hab
    · simp [e21]
      ring
    · simp [e21]
      ring
    · simp [e21]
      ring
  have q5 : e12 * e11 = 0 := by
    refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
    · simp [e11, e12]
      ring
    · simp [e11, e12]
      ring
    · simp [e11, e12]
      ring
    · simp [e11, e12]
      linear_combination (t ^ 2) * hab
  have q6 : e12 * e21 = e11 := by
    refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
    · simp [e11, e12, e21]
      linear_combination (-(t ^ 2)) * hab + (t) * ht
    · simp [e11, e12, e21]
      linear_combination (a * t) * ht
    · simp [e11, e12, e21]
      linear_combination (b * t) * ht
    · simp [e11, e12, e21]
      ring
  have q7 : e22 * e11 = 0 := by
    refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
    · simp [e11, e22]
      linear_combination (t ^ 2) * hab
    · simp [e11, e22]
      ring
    · simp [e11, e22]
      ring
    · simp [e11, e22]
      ring
  have q8 : e22 * e21 = e21 := by
    refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
    · simp [e21, e22]
      ring
    · simp [e21, e22]
      linear_combination (b * t) * ht
    · simp [e21, e22]
      linear_combination (-(a * t)) * ht
    · simp [e21, e22]
      linear_combination (t ^ 2) * hab + (-t) * ht
  have q9 : e11 + e22 = 1 := by
    refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
    · simp [e11, e22]
      linear_combination (1) * ht
    · simp [e11, e22]
    · simp [e11, e22]
    · simp [e11, e22]
  set E11 := ρ e11
  set E22 := ρ e22
  set E12 := ρ e12
  set E21 := ρ e21
  have hE11 : E11 ∈ A₀ := hρA _ htK (K₀.mul_mem haK htK) (K₀.mul_mem hbK htK) K₀.zero_mem
  have hE22 : E22 ∈ A₀ := hρA _ htK (K₀.neg_mem (K₀.mul_mem haK htK))
    (K₀.neg_mem (K₀.mul_mem hbK htK)) K₀.zero_mem
  have hE12 : E12 ∈ A₀ := hρA _ K₀.zero_mem (K₀.mul_mem hbK htK)
    (K₀.neg_mem (K₀.mul_mem haK htK)) htK
  have hE21 : E21 ∈ A₀ := hρA _ K₀.zero_mem (K₀.mul_mem hbK htK)
    (K₀.neg_mem (K₀.mul_mem haK htK)) (K₀.neg_mem htK)
  have r1 : E11 * E11 = E11 := by rw [← map_mul, q1]
  have r2 : E11 * E21 = 0 := by rw [← map_mul, q2, map_zero]
  have r3 : E21 * E11 = E21 := by rw [← map_mul, q3]
  have r4 : E21 * E21 = 0 := by rw [← map_mul, q4, map_zero]
  have r5 : E12 * E11 = 0 := by rw [← map_mul, q5, map_zero]
  have r6 : E12 * E21 = E11 := by rw [← map_mul, q6]
  have r7 : E22 * E11 = 0 := by rw [← map_mul, q7, map_zero]
  have r8 : E22 * E21 = E21 := by rw [← map_mul, q8]
  have r9 : E11 + E22 = 1 := by rw [← map_add, q9, map_one]
  have htrE11 : E11.trace = 1 := by
    simp only [E11, hρ, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, htrg, htrh,
      htrgh, e11, Fintype.card_fin, smul_eq_mul, mul_zero, add_zero]
    rw [← ht]
    push_cast
    ring
  have hE11ne : E11 ≠ 0 := by
    intro h0
    rw [h0, Matrix.trace_zero] at htrE11
    exact zero_ne_one htrE11
  clear_value E11 E22 E12 E21
  obtain ⟨c, hc⟩ : ∃ c : Fin 2, E11 *ᵥ Pi.single c 1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hE11ne
    ext i j
    have := congrFun (hcon j) i
    simpa [Matrix.mulVec_single] using this
  set v₁ : Fin 2 → F := E11 *ᵥ Pi.single c 1
  set v₂ : Fin 2 → F := E21 *ᵥ v₁
  have hv₁ : E11 *ᵥ v₁ = v₁ := by rw [Matrix.mulVec_mulVec, r1]
  have a21v1 : E21 *ᵥ v₁ = v₂ := rfl
  have hv₁ne : v₁ ≠ 0 := hc
  clear_value v₁ v₂
  set P : Matrix (Fin 2) (Fin 2) F := Matrix.of fun i j => if j = 0 then v₁ i else v₂ i
  have hPcol : ∀ x : Fin 2 → F, P *ᵥ x = x 0 • v₁ + x 1 • v₂ := by
    intro x
    ext i
    simp [P, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
  have a11 : E11 *ᵥ v₂ = 0 := by rw [← a21v1, Matrix.mulVec_mulVec, r2, Matrix.zero_mulVec]
  have a21 : E21 *ᵥ v₂ = 0 := by rw [← a21v1, Matrix.mulVec_mulVec, r4, Matrix.zero_mulVec]
  have a12v1 : E12 *ᵥ v₁ = 0 := by
    rw [← hv₁, Matrix.mulVec_mulVec, r5, Matrix.zero_mulVec]
  have a12v2 : E12 *ᵥ v₂ = v₁ := by rw [← a21v1, Matrix.mulVec_mulVec, r6, hv₁]
  have a22v1 : E22 *ᵥ v₁ = 0 := by
    rw [← hv₁, Matrix.mulVec_mulVec, r7, Matrix.zero_mulVec]
  have a22v2 : E22 *ᵥ v₂ = v₂ := by rw [← a21v1, Matrix.mulVec_mulVec, r8]
  have hPdet : P.det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    rw [hPcol] at hx
    have h11 := congrArg (E11 *ᵥ ·) hx
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hv₁, a11, smul_zero, add_zero,
      Matrix.mulVec_zero] at h11
    have h12 := congrArg (E12 *ᵥ ·) hx
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, a12v1, a12v2, smul_zero, zero_add,
      Matrix.mulVec_zero] at h12
    have hx0' : x 0 = 0 := by
      by_contra hne
      exact hv₁ne ((smul_eq_zero.mp h11).resolve_left hne)
    have hx1' : x 1 = 0 := by
      by_contra hne
      exact hv₁ne ((smul_eq_zero.mp h12).resolve_left hne)
    apply hx0
    ext i
    fin_cases i
    · exact hx0'
    · exact hx1'
  have hPunit : IsUnit P.det := isUnit_iff_ne_zero.mpr hPdet
  refine ⟨P, P⁻¹, Matrix.mul_nonsing_inv P hPunit, Matrix.nonsing_inv_mul P hPunit, ?_⟩
  have hcol0 : ∀ (E : Matrix (Fin 2) (Fin 2) F) (i : Fin 2), (E * P) i 0 = (E *ᵥ v₁) i := by
    intro E i
    simp [P, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hcol1 : ∀ (E : Matrix (Fin 2) (Fin 2) F) (i : Fin 2), (E * P) i 1 = (E *ᵥ v₂) i := by
    intro E i
    simp [P, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hEP : ∀ (E : Matrix (Fin 2) (Fin 2) F) (k l : Fin 2),
      (∀ i, (E *ᵥ v₁) i = (P * Matrix.single k l (1 : F) : Matrix (Fin 2) (Fin 2) F) i 0) →
      (∀ i, (E *ᵥ v₂) i = (P * Matrix.single k l (1 : F) : Matrix (Fin 2) (Fin 2) F) i 1) →
      E * P = P * Matrix.single k l 1 := by
    intro E k l h1 h2
    ext i j
    fin_cases j
    · exact (hcol0 E i).trans (h1 i)
    · exact (hcol1 E i).trans (h2 i)
  have hP11 : E11 * P = P * Matrix.single 0 0 1 := hEP E11 0 0
    (fun i => by rw [hv₁]; simp [P, Matrix.mul_apply, Matrix.single_apply])
    (fun i => by rw [a11]; simp [P, Matrix.mul_apply])
  have hP21 : E21 * P = P * Matrix.single 1 0 1 := hEP E21 1 0
    (fun i => by rw [a21v1]; simp [P, Matrix.mul_apply, Matrix.single_apply])
    (fun i => by rw [a21]; simp [P, Matrix.mul_apply])
  have hP12 : E12 * P = P * Matrix.single 0 1 1 := hEP E12 0 1
    (fun i => by rw [a12v1]; simp [P, Matrix.mul_apply])
    (fun i => by rw [a12v2]; simp [P, Matrix.mul_apply, Matrix.single_apply])
  have hP22 : E22 * P = P * Matrix.single 1 1 1 := hEP E22 1 1
    (fun i => by rw [a22v1]; simp [P, Matrix.mul_apply])
    (fun i => by rw [a22v2]; simp [P, Matrix.mul_apply, Matrix.single_apply])
  have hconj : ∀ (E : Matrix (Fin 2) (Fin 2) F) (k l : Fin 2), E * P = P * Matrix.single k l 1 →
      P * Matrix.single k l 1 * P⁻¹ = E := by
    intro E k l hE
    rw [← hE, Matrix.mul_assoc, Matrix.mul_nonsing_inv P hPunit, Matrix.mul_one]
  intro x hx i j
  have hentry : (P⁻¹ * x * P) i j = (x * (P * Matrix.single j i 1 * P⁻¹)).trace := by
    have hc : (x * (P * Matrix.single j i 1 * P⁻¹)).trace =
        ((P⁻¹ * x * P) * Matrix.single j i 1).trace := by
      calc (x * (P * Matrix.single j i 1 * P⁻¹)).trace =
            ((x * P * Matrix.single j i 1) * P⁻¹).trace := by simp only [Matrix.mul_assoc]
        _ = (P⁻¹ * (x * P * Matrix.single j i 1)).trace := Matrix.trace_mul_comm _ _
        _ = ((P⁻¹ * x * P) * Matrix.single j i 1).trace := by simp only [Matrix.mul_assoc]
    rw [hc]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_two]
  rw [hentry]
  have hunit : P * Matrix.single j i 1 * P⁻¹ ∈ A₀ := by
    fin_cases i <;> fin_cases j
    · change P * Matrix.single 0 0 1 * P⁻¹ ∈ A₀
      rw [hconj E11 0 0 hP11]; exact hE11
    · change P * Matrix.single 1 0 1 * P⁻¹ ∈ A₀
      rw [hconj E21 1 0 hP21]; exact hE21
    · change P * Matrix.single 0 1 1 * P⁻¹ ∈ A₀
      rw [hconj E12 0 1 hP12]; exact hE12
    · change P * Matrix.single 1 1 1 * P⁻¹ ∈ A₀
      rw [hconj E22 1 1 hP22]; exact hE22
  exact htrA _ (hmulA _ (hMA _ hx) _ hunit)

end CFSG.Glauberman.Dickson.TraceField
