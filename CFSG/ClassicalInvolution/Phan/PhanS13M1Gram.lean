module

public import CFSG.ClassicalInvolution.Phan.PhanS11Adj

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap

section Gram

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K)

theorem det3_7_smul_left (c : K) (a b d : W7 K) :
    det3_7 D (c • a) b d = c * D.τ c * det3_7 D a b d := by
  simp only [det3_7, hrm_smul_left, hrm_smul_right]
  ring

theorem det3_7_add_smul_snd (s : K) (a b d : W7 K) :
    det3_7 D a (b + s • a) d = det3_7 D a b d := by
  simp only [det3_7, hrm_add_left, hrm_add_right, hrm_smul_left, hrm_smul_right]
  ring

theorem det3_7_add_smul_third_fst (s : K) (a b d : W7 K) :
    det3_7 D a b (d + s • a) = det3_7 D a b d := by
  simp only [det3_7, hrm_add_left, hrm_add_right, hrm_smul_left, hrm_smul_right]
  ring

theorem det3_7_add_smul_third_snd (s : K) (a b d : W7 K) :
    det3_7 D a b (d + s • b) = det3_7 D a b d := by
  simp only [det3_7, hrm_add_left, hrm_add_right, hrm_smul_left, hrm_smul_right]
  ring

theorem hrm_eq_zero_symm {x y : W7 K} (h : hrm D x y = 0) : hrm D y x = 0 := by
  rw [hrm_conj_symm D y x, h, map_zero]

theorem det3_7_of_orth {a b d : W7 K} (hab : hrm D a b = 0) (had : hrm D a d = 0)
    (hbd : hrm D b d = 0) :
    det3_7 D a b d = hrm D a a * hrm D b b * hrm D d d := by
  have hba : hrm D b a = 0 := hrm_eq_zero_symm D hab
  have hda : hrm D d a = 0 := hrm_eq_zero_symm D had
  have hdb : hrm D d b = 0 := hrm_eq_zero_symm D hbd
  simp only [det3_7, hab, hba, had, hda, hbd, hdb]
  ring

end Gram

section Orth

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K)

theorem exists_orth_triple (h2K : (2 : K) ≠ 0) {y z : W7 K} (hy : IsFF7 D y) (hz : IsFF7 D z)
    (h1 : Col7 D (vXi D) y) (h2 : polar (quadOdd 3 K) y z = 0)
    (h3 : polar (quadOdd 3 K) z (vXi D) = 0) (hdet : det3_7 D (vXi D) y z ≠ 0) :
    ∃ (ly lz μ : K) (y₂ z₃ : W7 K), y = y₂ + ly • vXi D ∧ z = z₃ + μ • y₂ + lz • vXi D ∧
      IsFF7 D y₂ ∧ IsFF7 D z₃ ∧ polar (quadOdd 3 K) y₂ (vXi D) = 0 ∧ hrm D y₂ (vXi D) = 0 ∧
      polar (quadOdd 3 K) z₃ (vXi D) = 0 ∧ hrm D z₃ (vXi D) = 0 ∧
      polar (quadOdd 3 K) z₃ y₂ = 0 ∧ hrm D z₃ y₂ = 0 := by
  have h4 : (4 : K) ≠ 0 := four_ne_zero_of h2K
  have hτ4 : D.τ (4 : K) = 4 := map_ofNat D.τ 4
  have hξξ : polar (quadOdd 3 K) (vXi D) (vXi D) = 0 := polar_vXi_vXi D
  have hξy : polar (quadOdd 3 K) (vXi D) y = 0 := h1.1
  have hyξ : polar (quadOdd 3 K) y (vXi D) = 0 := by rw [QuadraticMap.polar_comm]; exact hξy
  have hzξ : polar (quadOdd 3 K) z (vXi D) = 0 := h3
  have hξz : polar (quadOdd 3 K) (vXi D) z = 0 := by rw [QuadraticMap.polar_comm]; exact hzξ
  have hyy : polar (quadOdd 3 K) y y = 0 := by
    rw [QuadraticMap.polar_self, hy.1]
    simp
  have hzz : polar (quadOdd 3 K) z z = 0 := by
    rw [QuadraticMap.polar_self, hz.1]
    simp
  obtain ⟨ly, hly⟩ : ∃ ly : K, ly = hrm D y (vXi D) / 4 := ⟨_, rfl⟩
  obtain ⟨lz, hlz⟩ : ∃ lz : K, lz = hrm D z (vXi D) / 4 := ⟨_, rfl⟩
  obtain ⟨y₂, hy₂⟩ : ∃ y₂ : W7 K, y₂ = y + (-ly) • vXi D := ⟨_, rfl⟩
  obtain ⟨z₂, hz₂⟩ : ∃ z₂ : W7 K, z₂ = z + (-lz) • vXi D := ⟨_, rfl⟩
  have hy₂ξ : polar (quadOdd 3 K) y₂ (vXi D) = 0 := by
    rw [hy₂, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, hyξ, hξξ]
    simp
  have hy₂ξ' : hrm D y₂ (vXi D) = 0 := by
    rw [hy₂, hrm_add_left, hrm_smul_left, hrm_vXi_vXi, neg_mul, hly, div_mul_cancel₀ _ h4,
      add_neg_cancel]
  have hy₂y₂ : polar (quadOdd 3 K) y₂ y₂ = 0 := by
    rw [hy₂, QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
      QuadraticMap.polar_add_right, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right, hyy, hyξ, hξy, hξξ]
    simp
  have hy₂ne : hrm D y₂ y₂ ≠ 0 := by
    have key : hrm D y₂ y₂ = gram7 D (vXi D) y / 4 := by
      have hs : hrm D (vXi D) y = D.τ (hrm D y (vXi D)) := hrm_conj_symm D _ _
      rw [hy₂, hrm_add_left, hrm_add_right, hrm_add_right, hrm_smul_left, hrm_smul_left,
        hrm_smul_right, hrm_smul_right, hrm_vXi_vXi, gram7, hrm_vXi_vXi, hs, hly, map_neg,
        map_div₀, hτ4]
      field_simp
      ring
    rw [key]
    exact div_ne_zero h1.2 h4
  have hz₂ξ : polar (quadOdd 3 K) z₂ (vXi D) = 0 := by
    rw [hz₂, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, hzξ, hξξ]
    simp
  have hz₂ξ' : hrm D z₂ (vXi D) = 0 := by
    rw [hz₂, hrm_add_left, hrm_smul_left, hrm_vXi_vXi, neg_mul, hlz, div_mul_cancel₀ _ h4,
      add_neg_cancel]
  have hz₂z₂ : polar (quadOdd 3 K) z₂ z₂ = 0 := by
    rw [hz₂, QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
      QuadraticMap.polar_add_right, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right, hzz, hzξ, hξz, hξξ]
    simp
  have hy₂z₂ : polar (quadOdd 3 K) y₂ z₂ = 0 := by
    rw [hy₂, hz₂, QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
      QuadraticMap.polar_add_right, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right, h2, hyξ, hξz, hξξ]
    simp
  have hz₂y₂ : polar (quadOdd 3 K) z₂ y₂ = 0 := by rw [QuadraticMap.polar_comm]; exact hy₂z₂
  obtain ⟨μ, hμ⟩ : ∃ μ : K, μ = hrm D z₂ y₂ / hrm D y₂ y₂ := ⟨_, rfl⟩
  obtain ⟨z₃, hz₃⟩ : ∃ z₃ : W7 K, z₃ = z₂ + (-μ) • y₂ := ⟨_, rfl⟩
  have hz₃ξ : polar (quadOdd 3 K) z₃ (vXi D) = 0 := by
    rw [hz₃, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, hz₂ξ, hy₂ξ]
    simp
  have hz₃ξ' : hrm D z₃ (vXi D) = 0 := by
    rw [hz₃, hrm_add_left, hrm_smul_left, hz₂ξ', hy₂ξ']
    simp
  have hz₃y₂ : polar (quadOdd 3 K) z₃ y₂ = 0 := by
    rw [hz₃, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, hz₂y₂, hy₂y₂]
    simp
  have hz₃y₂' : hrm D z₃ y₂ = 0 := by
    rw [hz₃, hrm_add_left, hrm_smul_left, hμ, neg_mul, div_mul_cancel₀ _ hy₂ne, add_neg_cancel]
  have hz₃z₃ : polar (quadOdd 3 K) z₃ z₃ = 0 := by
    rw [hz₃, QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
      QuadraticMap.polar_add_right, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right, hz₂z₂, hz₂y₂, hy₂z₂, hy₂y₂]
    simp
  have hdet₃ : det3_7 D (vXi D) y₂ z₃ = det3_7 D (vXi D) y z := by
    rw [hz₃, det3_7_add_smul_third_snd, hz₂, det3_7_add_smul_third_fst, hy₂,
      det3_7_add_smul_snd]
  have hz₃ne : hrm D z₃ z₃ ≠ 0 := by
    have hne : det3_7 D (vXi D) y₂ z₃ ≠ 0 := by rw [hdet₃]; exact hdet
    rw [det3_7_of_orth D (hrm_eq_zero_symm D hy₂ξ') (hrm_eq_zero_symm D hz₃ξ')
      (hrm_eq_zero_symm D hz₃y₂'), hrm_vXi_vXi] at hne
    intro h
    exact hne (by rw [h, mul_zero])
  refine ⟨ly, lz, μ, y₂, z₃, ?_, ?_, ⟨quad_eq_zero_of_polar_self h2K hy₂y₂, hy₂ne⟩,
    ⟨quad_eq_zero_of_polar_self h2K hz₃z₃, hz₃ne⟩, hy₂ξ, hy₂ξ', hz₃ξ, hz₃ξ', hz₃y₂, hz₃y₂'⟩
  · rw [hy₂]
    module
  · rw [hz₃, hz₂, hy₂]
    module

end Orth

end CFSG.ClassicalInvolution.PhanB3.S
