module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private def heisD {K : Type} [Field K] (ω : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2]

private def heisC (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 1; 1, 0, 0; 0, 1, 0]

private theorem heisD_det {K : Type} [Field K] {ω : K} (h3 : ω ^ 3 = 1) :
    (heisD ω).det = 1 := by
  rw [heisD, Matrix.det_fin_three]
  simp
  linear_combination h3

private theorem heisC_det (K : Type) [Field K] : (heisC K).det = 1 := by
  rw [heisC, Matrix.det_fin_three]
  simp

private theorem heisD_pow_three {K : Type} [Field K] {ω : K} (h3 : ω ^ 3 = 1) :
    heisD ω ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisD, pow_succ, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first
      | linear_combination h3
      | linear_combination (ω ^ 3 + 1) * h3

private theorem heisC_pow_three (K : Type) [Field K] : heisC K ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisC, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

private theorem heisC_mul_heisD {K : Type} [Field K] {ω : K} (h3 : ω ^ 3 = 1) :
    heisC K * heisD ω = heisD ω * heisC K * scalar (Fin 3) (ω ^ 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisC, heisD, Matrix.mul_apply, Fin.sum_univ_three, scalar_apply, diagonal_apply] <;>
    first
      | linear_combination (-1 : K) * h3
      | linear_combination (-ω) * h3

private theorem heisD_fixed {K : Type} [Field K] {ω : K} (σ : K ≃+* K) (hσω : σ ω = ω)
    (i j : Fin 3) : σ (heisD ω i j) = heisD ω i j := by
  fin_cases i <;> fin_cases j <;> simp [heisD, hσω]

private theorem heisC_fixed {K : Type} [Field K] (σ : K ≃+* K) (i j : Fin 3) :
    σ (heisC K i j) = heisC K i j := by
  fin_cases i <;> fin_cases j <;> simp [heisC]

private theorem map_eq_self_of_fixed {K : Type} [Field K] (σ : K ≃+* K)
    (g : SpecialLinearGroup (Fin 3) K) (h : ∀ i j, σ (g i j) = g i j) :
    Matrix.SpecialLinearGroup.map σ.toRingHom g = g := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp [h i j]

private theorem zpow_eq_zpow_mod_three {G : Type*} [Group G] {x : G} (hx : x ^ 3 = 1)
    (k : ℤ) : x ^ k = x ^ (k % 3) := by
  have h3z : x ^ (3 : ℤ) = 1 := by simpa using hx
  have hk : k = k % 3 + 3 * (k / 3) := by omega
  calc x ^ k = x ^ (k % 3 + 3 * (k / 3)) := by rw [← hk]
    _ = x ^ (k % 3) * (x ^ (3 : ℤ)) ^ (k / 3) := by rw [_root_.zpow_add, _root_.zpow_mul]
    _ = x ^ (k % 3) := by rw [h3z, _root_.one_zpow, mul_one]

theorem exists_heisenberg_pair_linear {K : Type} [Field K] [Finite K] [CharP K 2] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) (σ : K ≃+* K) (hσω : σ ω = ω) :
    ∃ x₁ x₂ : projectiveSL 3 K, Commute x₁ x₂ ∧ x₁ ^ 3 = 1 ∧ x₂ ^ 3 = 1 ∧
      (∀ i j : ℤ, x₁ ^ i * x₂ ^ j = 1 → (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ j) ∧
      fieldAut 3 K σ x₁ = x₁ ∧ fieldAut 3 K σ x₂ = x₂ := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have h3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω0 : ω ≠ 0 := by
    intro h
    rw [h] at h3
    norm_num at h3
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h] at hω
    have h10 : (1 : K) = 0 := by linear_combination hω - h2
    exact one_ne_zero h10
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h
    have h0 : ω = 0 := by linear_combination hω - h - h2
    exact hω0 h0
  obtain ⟨d, hd⟩ : ∃ d : SpecialLinearGroup (Fin 3) K,
      (d : Matrix (Fin 3) (Fin 3) K) = heisD ω :=
    ⟨⟨heisD ω, heisD_det h3⟩, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : SpecialLinearGroup (Fin 3) K,
      (c : Matrix (Fin 3) (Fin 3) K) = heisC K :=
    ⟨⟨heisC K, heisC_det K⟩, rfl⟩
  have hd3 : d ^ 3 = 1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hd,
      heisD_pow_three h3]
  have hc3 : c ^ 3 = 1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hc, heisC_pow_three K]
  have hx1 : proj 3 K d ^ 3 = 1 := by rw [← map_pow, hd3, map_one]
  have hx2 : proj 3 K c ^ 3 = 1 := by rw [← map_pow, hc3, map_one]
  obtain ⟨u, hu_val⟩ : ∃ u : Kˣ, (u : K) = ω ^ 2 :=
    ⟨Units.mk0 (ω ^ 2) (pow_ne_zero 2 hω0), rfl⟩
  have hu3 : u ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hu_val, Units.val_one]
    linear_combination (ω ^ 3 + 1) * h3
  have hcd : c * d = d * c * scalarElement u hu3 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement, hc, hd, hu_val]
    exact congrFun (congrFun (heisC_mul_heisD h3) i) j
  have hcomm : Commute (proj 3 K d) (proj 3 K c) := by
    show proj 3 K d * proj 3 K c = proj 3 K c * proj 3 K d
    rw [← map_mul, ← map_mul, proj_eq_proj_iff, hcd, inv_mul_cancel_left]
    exact scalarElement_mem_scalars u hu3
  have hfix_d : fieldAut 3 K σ (proj 3 K d) = proj 3 K d := by
    have hm : Matrix.SpecialLinearGroup.map σ.toRingHom d = d := by
      apply map_eq_self_of_fixed
      intro i j
      rw [congrFun (congrFun hd i) j]
      exact heisD_fixed σ hσω i j
    rw [fieldAut_proj, hm]
  have hfix_c : fieldAut 3 K σ (proj 3 K c) = proj 3 K c := by
    have hm : Matrix.SpecialLinearGroup.map σ.toRingHom c = c := by
      apply map_eq_self_of_fixed
      intro i j
      rw [congrFun (congrFun hc i) j]
      exact heisC_fixed σ i j
    rw [fieldAut_proj, hm]
  have key : ∀ a b : ℕ, a < 3 → b < 3 → proj 3 K d ^ a * proj 3 K c ^ b = 1 →
      a = 0 ∧ b = 0 := by
    intro a b ha hb h
    rw [← map_pow, ← map_pow, ← map_mul, proj_eq_one_iff, mem_scalars] at h
    obtain ⟨v, -, hv⟩ := h
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow, hc, hd] at hv
    interval_cases a <;> interval_cases b
    · exact ⟨rfl, rfl⟩
    · exfalso
      have e := congrFun (congrFun hv 0) 0
      simp [heisC, heisD, scalar_apply, diagonal_apply] at e
      exact v.ne_zero (by linear_combination -e)
    · exfalso
      have e := congrFun (congrFun hv 0) 0
      simp [heisC, heisD, pow_two, Matrix.mul_apply, Fin.sum_univ_three, scalar_apply,
        diagonal_apply] at e
      exact v.ne_zero (by linear_combination -e)
    · exfalso
      have e00 := congrFun (congrFun hv 0) 0
      have e11 := congrFun (congrFun hv 1) 1
      simp [heisD, scalar_apply, diagonal_apply] at e00 e11
      exact hω1 (by linear_combination e11 - e00)
    · exfalso
      have e := congrFun (congrFun hv 0) 0
      simp [heisC, heisD, scalar_apply, diagonal_apply] at e
      exact v.ne_zero (by linear_combination -e)
    · exfalso
      have e := congrFun (congrFun hv 0) 0
      simp [heisC, heisD, pow_two, Matrix.mul_apply, Fin.sum_univ_three, scalar_apply,
        diagonal_apply] at e
      exact v.ne_zero (by linear_combination -e)
    · exfalso
      have e00 := congrFun (congrFun hv 0) 0
      have e11 := congrFun (congrFun hv 1) 1
      simp [heisD, pow_two, scalar_apply, diagonal_apply] at e00 e11
      exact hω2 (by linear_combination e11 - e00)
    · exfalso
      have e := congrFun (congrFun hv 0) 0
      simp [heisC, heisD, pow_two, Matrix.mul_apply, Fin.sum_univ_three, scalar_apply,
        diagonal_apply] at e
      exact v.ne_zero (by linear_combination -e)
    · exfalso
      have e := congrFun (congrFun hv 0) 0
      simp [heisC, heisD, pow_two, Matrix.mul_apply, Fin.sum_univ_three, scalar_apply,
        diagonal_apply] at e
      exact v.ne_zero (by linear_combination -e)
  have hind : ∀ i j : ℤ, proj 3 K d ^ i * proj 3 K c ^ j = 1 → (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ j := by
    intro i j hij
    rw [zpow_eq_zpow_mod_three hx1 i, zpow_eq_zpow_mod_three hx2 j] at hij
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ i % 3)
    obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ j % 3)
    have ha3 : a < 3 := by omega
    have hb3 : b < 3 := by omega
    rw [ha, hb, _root_.zpow_natCast, _root_.zpow_natCast] at hij
    obtain ⟨rfl, rfl⟩ := key a b ha3 hb3 hij
    exact ⟨by omega, by omega⟩
  exact ⟨proj 3 K d, proj 3 K c, hcomm, hx1, hx2, hind, hfix_d, hfix_c⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
