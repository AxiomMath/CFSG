module

public import CFSG.ClassicalInvolution.ModelFacts.L6CUBase
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian

public section

namespace CFSG.ClassicalInvolution.ModelFacts.L6C

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
open scoped MatrixGroups

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

local notation "𝕄₄" => Matrix (Fin 4) (Fin 4) K

theorem sh_smul_left (c : K) (x y : Fin 4 → K) :
    stdHermForm h 4 (c • x) y = h.bar c * stdHermForm h 4 x y := by
  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]

theorem sh_smul_right (c : K) (x y : Fin 4 → K) :
    stdHermForm h 4 x (c • y) = c * stdHermForm h 4 x y := by
  rw [map_smul, smul_eq_mul]

theorem sh_add_left (x x' y : Fin 4 → K) :
    stdHermForm h 4 (x + x') y = stdHermForm h 4 x y + stdHermForm h 4 x' y := by
  rw [map_add, LinearMap.add_apply]

theorem sh_symm_zero {x y : Fin 4 → K} (hxy : stdHermForm h 4 x y = 0) :
    stdHermForm h 4 y x = 0 := by
  rw [← (stdHermForm_isSymm h 4).eq x y, hxy, map_zero]

theorem sh_symm_one {x y : Fin 4 → K} (hxy : stdHermForm h 4 x y = 1) :
    stdHermForm h 4 y x = 1 := by
  rw [← (stdHermForm_isSymm h 4).eq x y, hxy, map_one]

theorem uadj_colMat_mul_colMat (v w : Fin 4 → Fin 4 → K) (i j : Fin 4) :
    (uadj h (colMat v) * colMat w) i j = stdHermForm h 4 (v i) (w j) := by
  simp [uadj, colMat, Matrix.mul_apply, stdHermForm_apply]

theorem uadj_colMat_mul_mul_colMat (M : 𝕄₄) (v w : Fin 4 → Fin 4 → K) (i j : Fin 4) :
    (uadj h (colMat v) * M * colMat w) i j = stdHermForm h 4 (v i) (M *ᵥ w j) := by
  rw [Matrix.mul_assoc, mul_colMat, uadj_colMat_mul_colMat]

theorem stdHermForm_mulVec_left (A : 𝕄₄) (x y : Fin 4 → K) :
    stdHermForm h 4 (A *ᵥ x) y = stdHermForm h 4 x (uadj h A *ᵥ y) := by
  simp only [stdHermForm_apply, Matrix.mulVec, dotProduct, uadj_apply, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem stdHermForm_mulVec_mulVec {M : 𝕄₄} (hM : uadj h M * M = 1) (x y : Fin 4 → K) :
    stdHermForm h 4 (M *ᵥ x) (M *ᵥ y) = stdHermForm h 4 x y := by
  rw [stdHermForm_mulVec_left, Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]

section Ext

theorem exists_unit_perp {r : ℕ} (hr : r < 4) (b : Fin r → Fin 4 → K)
    (hb : ∀ i j, stdHermForm h 4 (b i) (b j) = if i = j then 1 else 0) :
    ∃ v, stdHermForm h 4 v v = 1 ∧ ∀ i, stdHermForm h 4 (b i) v = 0 := by
  obtain ⟨c₀, hc₀⟩ := h.exists_bar_ne
  refine exists_norm_one_perp_of_lt (stdHermForm_isSymm h 4) (stdHermForm_separatingLeft h 4)
    hc₀ ?_ (by simpa [Module.finrank_fin_fun] using hr) b hb
  intro d hd _
  obtain ⟨c, hc⟩ := h.normHom_surjective ⟨d, hd⟩
  exact ⟨c, by rw [mul_comm]; exact congrArg Subtype.val hc⟩

end Ext

theorem exists_frame_of_plane {M : 𝕄₄} (hM : uadj h M * M = 1) {u₁ u₂ : Fin 4 → K}
    (h11 : stdHermForm h 4 u₁ u₁ = 1) (h22 : stdHermForm h 4 u₂ u₂ = 1)
    (h12 : stdHermForm h 4 u₁ u₂ = 0) {a b : K} (hdet : a * a + b * b ≠ 0)
    (hM1 : M *ᵥ u₁ = a • u₁ - b • u₂) (hM2 : M *ᵥ u₂ = b • u₁ + a • u₂) :
    ∃ Q : 𝕄₄, uadj h Q * Q = 1 ∧
      M * (Q * (rot4 K : 𝕄₄) * uadj h Q) = Q * (rot4 K : 𝕄₄) * uadj h Q * M := by
  have h21 : stdHermForm h 4 u₂ u₁ = 0 := sh_symm_zero h h12
  have hb2 : ∀ i j : Fin 2, stdHermForm h 4 (![u₁, u₂] i) (![u₁, u₂] j) =
      if i = j then 1 else 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [h11, h22, h12, h21]
  obtain ⟨u₃, h33, h3⟩ := exists_unit_perp h (r := 2) (by norm_num) ![u₁, u₂] hb2
  have h13 : stdHermForm h 4 u₁ u₃ = 0 := h3 0
  have h23 : stdHermForm h 4 u₂ u₃ = 0 := h3 1
  have h31 : stdHermForm h 4 u₃ u₁ = 0 := sh_symm_zero h h13
  have h32 : stdHermForm h 4 u₃ u₂ = 0 := sh_symm_zero h h23
  have hb3 : ∀ i j : Fin 3, stdHermForm h 4 (![u₁, u₂, u₃] i) (![u₁, u₂, u₃] j) =
      if i = j then 1 else 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [h11, h22, h33, h12, h21, h13, h23, h31, h32]
  obtain ⟨u₄, h44, h4⟩ := exists_unit_perp h (r := 3) (by norm_num) ![u₁, u₂, u₃] hb3
  have h14 : stdHermForm h 4 u₁ u₄ = 0 := h4 0
  have h24 : stdHermForm h 4 u₂ u₄ = 0 := h4 1
  have h34 : stdHermForm h 4 u₃ u₄ = 0 := h4 2
  have h41 : stdHermForm h 4 u₄ u₁ = 0 := sh_symm_zero h h14
  have h42 : stdHermForm h 4 u₄ u₂ = 0 := sh_symm_zero h h24
  have h43 : stdHermForm h 4 u₄ u₃ = 0 := sh_symm_zero h h34
  set v : Fin 4 → Fin 4 → K := ![u₁, u₂, u₃, u₄] with hv
  have hQ : uadj h (colMat v) * colMat v = 1 := by
    ext i j
    rw [uadj_colMat_mul_colMat]
    fin_cases i <;> fin_cases j <;>
      simp [hv, h11, h22, h33, h44, h12, h21, h13, h23, h31, h32, h14, h24, h34, h41, h42, h43]
  refine ⟨colMat v, hQ, ?_⟩
  have hpre1 : M *ᵥ ((a * a + b * b)⁻¹ • (a • u₁ + b • u₂)) = u₁ := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hM1, hM2]
    ext r
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    rw [show a * (a * u₁ r - b * u₂ r) + b * (b * u₁ r + a * u₂ r) = (a * a + b * b) * u₁ r by
      ring, ← mul_assoc, inv_mul_cancel₀ hdet, one_mul]
  have hpre2 : M *ᵥ ((a * a + b * b)⁻¹ • (-b • u₁ + a • u₂)) = u₂ := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hM1, hM2]
    ext r
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    rw [show -b * (a * u₁ r - b * u₂ r) + a * (b * u₁ r + a * u₂ r) = (a * a + b * b) * u₂ r by
      ring, ← mul_assoc, inv_mul_cancel₀ hdet, one_mul]
  have hmix : ∀ w : Fin 4 → K, stdHermForm h 4 u₁ w = 0 → stdHermForm h 4 u₂ w = 0 →
      stdHermForm h 4 u₁ (M *ᵥ w) = 0 ∧ stdHermForm h 4 u₂ (M *ᵥ w) = 0 := by
    intro w hw1 hw2
    constructor
    · have := stdHermForm_mulVec_mulVec h hM ((a * a + b * b)⁻¹ • (a • u₁ + b • u₂)) w
      rw [hpre1] at this
      rw [this]
      simp only [sh_smul_left, sh_add_left, hw1, hw2, mul_zero, add_zero]
    · have := stdHermForm_mulVec_mulVec h hM ((a * a + b * b)⁻¹ • (-b • u₁ + a • u₂)) w
      rw [hpre2] at this
      rw [this]
      simp only [sh_smul_left, sh_add_left, hw1, hw2, mul_zero, add_zero]
  refine comm_of_frame h hQ rfl ?_
  set N : 𝕄₄ := uadj h (colMat v) * M * colMat v with hN
  have hNe : ∀ i j, N i j = stdHermForm h 4 (v i) (M *ᵥ v j) := fun i j =>
    uadj_colMat_mul_mul_colMat h M v v i j
  have hMu1 : M *ᵥ v 0 = a • u₁ - b • u₂ := hM1
  have hMu2 : M *ᵥ v 1 = b • u₁ + a • u₂ := hM2
  apply commutes_rot4_of_entries
  · rw [hNe, hNe, hMu1, hMu2]
    simp [hv, h11, h22, h12, h21, map_sub, map_add]
  · rw [hNe, hNe, hMu1, hMu2]
    simp [hv, h11, h22, h12, h21, map_sub, map_add]
  · rw [hNe]; exact (hmix (v 2) h13 h23).1
  · rw [hNe]; exact (hmix (v 3) h14 h24).1
  · rw [hNe]; exact (hmix (v 2) h13 h23).2
  · rw [hNe]; exact (hmix (v 3) h14 h24).2
  · rw [hNe, hMu1]
    simp [hv, h31, h32, map_sub]
  · rw [hNe, hMu2]
    simp [hv, h31, h32, map_add]
  · rw [hNe, hMu1]
    simp [hv, h41, h42, map_sub]
  · rw [hNe, hMu2]
    simp [hv, h41, h42, map_add]

end CFSG.ClassicalInvolution.ModelFacts.L6C
