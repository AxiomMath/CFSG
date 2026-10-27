module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2LWit

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {K : Type} [Field K]

abbrev eij (i j : Fin n) : Matrix (Fin n) (Fin n) K := Matrix.single i j 1

theorem eij_mul_eij (i j k l : Fin n) :
    (eij i j : Matrix (Fin n) (Fin n) K) * eij k l = if j = k then eij i l else 0 := by
  unfold eij
  split_ifs with h
  · rw [h, single_mul_single_same, one_mul]
  · ext x y
    simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases h1 : i = x ∧ j = z <;> by_cases h2 : k = z ∧ l = y <;> simp_all

theorem mapMatrix_eij (σ : K ≃+* K) (i j : Fin n) :
    (σ : K →+* K).mapMatrix (eij i j : Matrix (Fin n) (Fin n) K) = eij i j := by
  ext k l
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, eij, Matrix.single_apply]
  split_ifs <;> simp

theorem hasWit_fieldAut (h2 : (2 : K) = 0) (hn : 3 ≤ n) (σ : K ≃+* K) :
    HasWit (fieldAut n K σ) := by
  set i0 : Fin n := ⟨0, by omega⟩
  set i1 : Fin n := ⟨1, by omega⟩
  set i2 : Fin n := ⟨2, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  set a : Matrix (Fin n) (Fin n) K := eij i0 i1 with ha
  set b : Matrix (Fin n) (Fin n) K := eij i1 i0 with hb
  set E : Matrix (Fin n) (Fin n) K := eij i1 i2 with hE
  have haa : a * a = 0 := by rw [ha, eij_mul_eij]; simp [h01.symm]
  have hbb : b * b = 0 := by rw [hb, eij_mul_eij]; simp [h01]
  have haba : a * b * a = a := by
    rw [ha, hb, eij_mul_eij]; simp only [ite_true]; rw [eij_mul_eij]; simp
  have hbab : b * a * b = b := by
    rw [ha, hb, eij_mul_eij]; simp only [ite_true]; rw [eij_mul_eij]; simp
  have hEE : E * E = 0 := by rw [hE, eij_mul_eij]; simp [h12.symm]
  have hEa : E * a = 0 := by rw [hE, ha, eij_mul_eij]; simp [h02.symm]
  have hEb : E * b = 0 := by rw [hE, hb, eij_mul_eij]; simp [h12.symm]
  have haE : a * E = eij i0 i2 := by rw [hE, ha, eij_mul_eij]; simp
  have hbE : b * E = 0 := by rw [hE, hb, eij_mul_eij]; simp [h01]
  set h := unipOf h2 a haa * unipOf h2 b hbb with hh
  have hH : (h : Matrix (Fin n) (Fin n) K) = (1 + a) * (1 + b) := by
    rw [hh, Matrix.SpecialLinearGroup.coe_mul, coe_unipOf, coe_unipOf]
  have hinv : h⁻¹ = unipOf h2 b hbb * unipOf h2 a haa := by
    have hu : ∀ (X : Matrix (Fin n) (Fin n) K) (hX : X * X = 0),
        unipOf h2 X hX * unipOf h2 X hX = 1 := fun X hX => by
      ext i j
      rw [Matrix.SpecialLinearGroup.coe_mul, coe_unipOf, one_add_mul_self h2 hX]
      rfl
    rw [hh, _root_.mul_inv_rev, inv_eq_of_mul_eq_one_right (hu b hbb),
      inv_eq_of_mul_eq_one_right (hu a haa)]
  have h3 : h ^ 3 = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow, hH,
      pow_three_of_rel (add_self_eq_zero_of_two h2) haa hbb haba hbab]
    rfl
  have hEh : E * (h : Matrix (Fin n) (Fin n) K) = E := by
    simp only [hH, mul_add, add_mul, mul_one, one_mul, ← mul_assoc, hEa, hEb, zero_mul,
      add_zero]
  have hEh' : E * ((h⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = E := by
    simp only [hinv, Matrix.SpecialLinearGroup.coe_mul, coe_unipOf, mul_add, add_mul, mul_one,
      one_mul, ← mul_assoc, hEa, hEb, zero_mul, add_zero]
  have hne : (h : Matrix (Fin n) (Fin n) K) * E ≠ E * h := by
    rw [hEh, hH]
    intro heq
    have h1 : (1 + a) * (1 + b) * E = E + eij i0 i2 := by
      simp only [mul_assoc, add_mul, one_mul, hbE, add_zero, haE]
    rw [h1] at heq
    have := congrFun (congrFun heq i0) i2
    simp [eij, Matrix.single_apply, hE] at this
  have hfix : ∀ g : SpecialLinearGroup (Fin n) K,
      (σ : K →+* K).mapMatrix (g : Matrix (Fin n) (Fin n) K) = g →
        fieldAut n K σ (proj n K g) = proj n K g := by
    intro g hg
    rw [fieldAut_proj]
    congr 1
    ext i j
    exact congrFun (congrFun hg i) j
  refine hasWit_of_sl h2 h (m := 3) ⟨1, rfl⟩ h3 hEE (by rw [hEh, hEE]) (by rw [hEh', hEE]) hne
    (hfix h ?_) (hfix _ ?_)
  · rw [hH, map_mul, map_add, map_add, map_one, ha, hb, mapMatrix_eij, mapMatrix_eij]
  · rw [coe_unipOf, map_add, map_one, hE, mapMatrix_eij]

end CFSG.ComponentClassification.HarrisLit.L33.C2
