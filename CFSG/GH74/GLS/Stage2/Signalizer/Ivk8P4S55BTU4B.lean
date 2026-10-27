module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTU4R
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4G2

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BU4

open Matrix Subgroup BS4 BL4

variable {K : Type} [Field K] {φ : K →+* K}

theorem ul_herm {M : MB K} (hM : M.toBlocks₂₁ = 0) (hu : (M.map φ)ᵀ * jU * M = jU) :
    (M.toBlocks₁₁.map φ)ᵀ * M.toBlocks₂₂ = 1 := by
  ext i j
  have e := congrFun (congrFun hu (Sum.inl i)) (Sum.inr j)
  have h0 : ∀ k l, M (Sum.inr k) (Sum.inl l) = 0 := fun k l => congrFun (congrFun hM k) l
  simp [Matrix.mul_apply, Fintype.sum_sum_type, h0] at e
  simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.mul_apply, Matrix.one_apply] at e ⊢
  exact e

theorem det_ne_zero_of_herm {M : MB K} (hM : M.toBlocks₂₁ = 0)
    (hu : (M.map φ)ᵀ * jU * M = jU) : (M.toBlocks₁₁.map φ).det ≠ 0 := by
  intro h0
  have e := congrArg Matrix.det (ul_herm hM hu)
  rw [det_mul, det_transpose, h0, zero_mul, det_one] at e
  exact zero_ne_one e

theorem comm_of_herm_blocks {Bm : MB K} (hB21 : Bm.toBlocks₂₁ = 0)
    (hBns : ∀ c : K, Bm.toBlocks₁₁ ≠ c • 1) {H : Subgroup (GL (Fin 2 ⊕ Fin 2) K)}
    (hH21 : ∀ x ∈ H, (x : MB K).toBlocks₂₁ = 0)
    (hHB : ∀ x ∈ H, Bm * (x : MB K) = (x : MB K) * Bm)
    (hHu : ∀ x ∈ H, ((x : MB K).map φ)ᵀ * jU * (x : MB K) = jU) :
    ∀ z ∈ ⁅H, H⁆, ∀ w ∈ ⁅H, H⁆, z * w = w * z := by
  have hul : ∀ x ∈ H, (x : MB K).toBlocks₁₁ * Bm.toBlocks₁₁ =
      Bm.toBlocks₁₁ * (x : MB K).toBlocks₁₁ := by
    intro x hx
    have := congrArg toBlocks₁₁ (hHB x hx)
    rw [ul_mul (hH21 x hx), ul_mul hB21] at this
    exact this.symm
  have hc : ∀ x ∈ H, ∀ y ∈ H, (x : MB K).toBlocks₁₁ * (y : MB K).toBlocks₁₁ =
      (y : MB K).toBlocks₁₁ * (x : MB K).toBlocks₁₁ := fun x hx y hy =>
    comm_of_comm_nonscalar hBns (hul x hx) (hul y hy)
  have hrel : ∀ z ∈ H, ((z : MB K).toBlocks₁₁.map φ)ᵀ * 1 * (z : MB K).toBlocks₂₂ = 1 :=
    fun z hz => by rw [Matrix.mul_one]; exact ul_herm (hH21 z hz) (hHu z hz)
  refine comm_of_blocks_comm hH21 hc fun x hx y hy => ?_
  exact comm_of_rel (by rw [det_one]; exact one_ne_zero)
    (det_ne_zero_of_herm (hH21 x hx) (hHu x hx)) (det_ne_zero_of_herm (hH21 y hy) (hHu y hy))
    (by rw [← Matrix.map_mul, ← Matrix.map_mul, hc x hx y hy]) (hrel x hx) (hrel y hy)

theorem map_smul_one (c : K) :
    (c • (1 : Matrix (Fin 2) (Fin 2) K)).map φ = φ c • 1 := by
  ext i j
  by_cases hij : i = j <;> simp [hij]

theorem norm_neg_one {B : MB K} (hB21 : B.toBlocks₂₁ = 0) (hBu : (B.map φ)ᵀ * jU * B = jU)
    {c : K} (hc : B.toBlocks₁₁ = c • 1) {s : K} (hs : B * B = s • 1)
    (hns : ∀ μ : K, B ≠ μ • 1) : c * φ c = -1 := by
  have hr := ul_herm hB21 hBu
  rw [hc, map_smul_one, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul] at hr
  have hφc : φ c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hr
    simpa using congrFun (congrFun hr 0) 0
  have hZ : B.toBlocks₂₂ = (φ c)⁻¹ • 1 := by
    rw [← hr, smul_smul, inv_mul_cancel₀ hφc, one_smul]
  have hB : B = fromBlocks (c • 1) B.toBlocks₁₂ 0 ((φ c)⁻¹ • 1) := by
    conv_lhs => rw [← fromBlocks_toBlocks B]
    rw [hB21, hc, hZ]
  have hsq := hs
  rw [hB, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul] at hsq
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, smul_smul, smul_zero] at hsq
  obtain ⟨h11, h12, -, h22⟩ := Matrix.fromBlocks_inj.mp hsq
  have e11 : c * c = s := by simpa using congrFun (congrFun h11 0) 0
  have e22 : (φ c)⁻¹ * (φ c)⁻¹ = s := by simpa using congrFun (congrFun h22 0) 0
  by_cases hcd : c + (φ c)⁻¹ = 0
  · have e : (c + (φ c)⁻¹) * φ c = 0 := by rw [hcd, zero_mul]
    rw [add_mul, inv_mul_cancel₀ hφc] at e
    linear_combination e
  · exfalso
    have hY : B.toBlocks₁₂ = 0 := by
      rw [← add_smul] at h12
      exact (smul_eq_zero.mp h12).resolve_left hcd
    have hcc : c = (φ c)⁻¹ := by
      have : (c - (φ c)⁻¹) * (c + (φ c)⁻¹) = 0 := by linear_combination e11 - e22
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hcd)
    apply hns c
    rw [hB, hY, ← hcc, ← fromBlocks_one, fromBlocks_smul, smul_zero]

theorem norm_one_of_semi {B A : MB K} (hB21 : B.toBlocks₂₁ = 0) {c : K}
    (hc : B.toBlocks₁₁ = c • 1) (hA21 : A.toBlocks₂₁ = 0) (hAd : A.det ≠ 0)
    (hBA : B * A * B.map φ = A) : c * φ c = 1 := by
  have hφ21 : (B.map φ).toBlocks₂₁ = 0 := by
    ext i j
    have := congrFun (congrFun hB21 i) j
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply, Matrix.map_apply] at this ⊢
    rw [this, map_zero]
  have hφ11 : (B.map φ).toBlocks₁₁ = φ c • 1 := by
    rw [← map_smul_one, ← hc]
    rfl
  have h := congrArg toBlocks₁₁ hBA
  rw [ul_mul hφ21, ul_mul hA21, hc, hφ11] at h
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul] at h
  have hX : A.toBlocks₁₁ ≠ 0 := by
    intro h0
    apply hAd
    rw [← fromBlocks_toBlocks A, hA21, det_fromBlocks_zero₂₁, h0]
    simp
  have h' : (c * φ c - 1) • A.toBlocks₁₁ = 0 := by
    rw [sub_smul, one_smul, mul_comm, h, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h').resolve_right hX)

theorem norm_one_of_smul {n : Type*} [Fintype n] [DecidableEq n] {J M : Matrix n n K}
    (hJ : J ≠ 0) (hM : (M.map φ)ᵀ * J * M = J) {μ : K}
    (hμ : ((μ • M).map φ)ᵀ * J * (μ • M) = J) : μ * φ μ = 1 := by
  have e : (μ • M).map φ = φ μ • M.map φ := by
    ext i j
    simp
  rw [e, transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, hM, smul_smul] at hμ
  obtain ⟨i, j, hij⟩ : ∃ i j, J i j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hJ (Matrix.ext hc)
  have := congrFun (congrFun hμ i) j
  rw [Matrix.smul_apply, smul_eq_mul] at this
  have h1 : (φ μ * μ - 1) * J i j = 0 := by linear_combination this
  rw [mul_comm]
  exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hij)

theorem herm_mul {n : Type*} [Fintype n] [DecidableEq n] {J M N : Matrix n n K}
    (hM : (M.map φ)ᵀ * J * M = J) (hN : (N.map φ)ᵀ * J * N = J) :
    ((M * N).map φ)ᵀ * J * (M * N) = J := by
  calc ((M * N).map φ)ᵀ * J * (M * N) = (N.map φ)ᵀ * ((M.map φ)ᵀ * J * M) * N := by
        rw [Matrix.map_mul, transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = J := by rw [hM, hN]

end BU4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
