module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearAut
public import CFSG.LocalAnalysis.ComponentInitial.ScalarSemilinearNormalizer

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.U4Red

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K]

theorem sim_pow (h : UnitaryFieldData p f K) {C : GL (HypIndex 2 0) K} {μ : K}
    (hC : ((C : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar)ᵀ * hypGram 2 0 K *
      (C : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = μ • hypGram 2 0 K) (n : ℕ) :
    ((((C : Matrix (HypIndex 2 0) (HypIndex 2 0) K) ^ n).map h.bar)ᵀ * hypGram 2 0 K *
      ((C : Matrix (HypIndex 2 0) (HypIndex 2 0) K) ^ n)) = (μ ^ n) • hypGram 2 0 K := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', conjTranspose_mul_mul, hC, Matrix.mul_smul, Matrix.smul_mul, ih, smul_smul,
      pow_succ']

theorem norm_det_eq (h : UnitaryFieldData p f K)
    {C : Matrix (HypIndex 2 0) (HypIndex 2 0) K} {μ : K}
    (hC : (C.map h.bar)ᵀ * hypGram 2 0 K * C = μ • hypGram 2 0 K) :
    h.norm C.det = μ ^ 4 := by
  have h1 := congrArg Matrix.det hC
  rw [det_mul, det_mul, det_transpose, det_smul] at h1
  have e : (C.map h.bar).det = h.bar C.det := by
    rw [RingHom.map_det]
    rfl
  have hJ : (hypGram 2 0 K).det ≠ 0 := det_hypGram_ne_zero
  have e4 : Fintype.card (HypIndex 2 0) = 4 := by simp
  rw [e, e4] at h1
  have h2 : (C.det * h.bar C.det) * (hypGram 2 0 K).det = μ ^ 4 * (hypGram 2 0 K).det := by
    rw [← h1]; ring
  exact mul_right_cancel₀ hJ h2

theorem exists_pow_four_eq (h : UnitaryFieldData p f K) {C : GL (HypIndex 2 0) K} {μ : K}
    (hC : ((C : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar)ᵀ * hypGram 2 0 K *
      (C : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = μ • hypGram 2 0 K) :
    ∃ (c : Kˣ) (g : hypSU h 2 0),
      C ^ 4 = GeneralLinearGroup.scalar (HypIndex 2 0) c * (g : GL (HypIndex 2 0) K) := by
  set c : Kˣ := Matrix.GeneralLinearGroup.det C with hc
  have hcC : (c : K) = (C : Matrix (HypIndex 2 0) (HypIndex 2 0) K).det :=
    Matrix.GeneralLinearGroup.val_det_apply C
  have hN : h.norm (c : K) = μ ^ 4 := by rw [hcC]; exact norm_det_eq h hC
  have hcoe : (((GeneralLinearGroup.scalar (HypIndex 2 0) c⁻¹ * C ^ 4 : GL (HypIndex 2 0) K)) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
        ((c⁻¹ : Kˣ) : K) • (C : Matrix (HypIndex 2 0) (HypIndex 2 0) K) ^ 4 := by
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul, Units.val_pow_eq_pow_val]
  have hg0 : (GeneralLinearGroup.scalar (HypIndex 2 0) c⁻¹ * C ^ 4 : GL (HypIndex 2 0) K) ∈
      hypSU h 2 0 := by
    rw [mem_hypSU, hcoe]
    constructor
    · rw [Matrix.map_smul' _ _ _ (map_mul h.bar), Matrix.transpose_smul]
      simp only [Matrix.smul_mul, Matrix.mul_smul]
      rw [sim_pow h hC 4, smul_smul, smul_smul]
      have h3 : ((c⁻¹ : Kˣ) : K) * h.bar ((c⁻¹ : Kˣ) : K) * μ ^ 4 = 1 := by
        have h4 : (c : K) * h.bar (c : K) = μ ^ 4 := hN
        have hc0 : (c : K) ≠ 0 := c.ne_zero
        have hb0 : h.bar (c : K) ≠ 0 := (map_ne_zero h.bar).mpr hc0
        rw [Units.val_inv_eq_inv_val, map_inv₀, ← h4]
        field_simp
      rw [h3, one_smul]
    · rw [det_smul, det_pow]
      have e4 : Fintype.card (HypIndex 2 0) = 4 := by simp
      rw [e4, ← hcC, Units.val_inv_eq_inv_val]
      field_simp
  refine ⟨c, ⟨_, hg0⟩, ?_⟩
  simp

theorem semilinearAutHom_inl (h : UnitaryFieldData p f K) (g : hypSU h 2 0) :
    semilinearAutHom h (by norm_num) (by norm_num)
      ⟨SemidirectProduct.inl (g : GL (HypIndex 2 0) K), inl_mem_semilinearSimilitudes g⟩ =
        MulAut.conj (hypProj h 2 0 g) := by
  ext s
  obtain ⟨s₀, rfl⟩ := hypProj_surjective h 2 0 s
  rw [semilinearAutHom_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem semilinearAutHom_pow_four_mem (h : UnitaryFieldData p f K)
    (x : ↥(semilinearSimilitudes h 2 0))
    (hx : (x : SemiGL (HypIndex 2 0) K).right = 1) :
    semilinearAutHom h (by norm_num) (by norm_num) (x ^ 4) ∈
      (MulAut.conj : hypPSU h 2 0 →* MulAut (hypPSU h 2 0)).range := by
  obtain ⟨μ, -, -, hC⟩ := x.2
  obtain ⟨c, g, hcg⟩ := exists_pow_four_eq h hC
  have hxinl : (x : SemiGL (HypIndex 2 0) K) =
      SemidirectProduct.inl (x : SemiGL (HypIndex 2 0) K).left :=
    SemidirectProduct.ext (by simp) (by simp [hx])
  let y : ↥(semilinearSimilitudes h 2 0) :=
    ⟨SemidirectProduct.inl (g : GL (HypIndex 2 0) K), inl_mem_semilinearSimilitudes g⟩
  have hx4 : ((x ^ 4 : ↥(semilinearSimilitudes h 2 0)) : SemiGL (HypIndex 2 0) K) =
      SemidirectProduct.inl (((x : SemiGL (HypIndex 2 0) K).left) ^ 4) := by
    rw [Subgroup.coe_pow, hxinl, ← map_pow]
    simp
  have hy' : semilinearAutHom h (by norm_num) (by norm_num) (x ^ 4 * y⁻¹) = 1 := by
    rw [semilinearAutHom_eq_one_iff h (by norm_num) (by norm_num) (by norm_num)]
    refine ⟨?_, c, ?_⟩
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, SemidirectProduct.mul_right,
        SemidirectProduct.inv_right, hx4, y]
      simp
      rfl
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, SemidirectProduct.mul_left,
        SemidirectProduct.inv_left, hx4, y]
      simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl, inv_one, map_one,
        MulAut.one_apply, hcg]
      exact mul_inv_cancel_right _ _
  have hfac : x ^ 4 = (x ^ 4 * y⁻¹) * y := by group
  rw [hfac, map_mul, hy', one_mul]
  exact ⟨hypProj h 2 0 g, (semilinearAutHom_inl h g).symm⟩

theorem commutator_pow_four_mem_hypPSU (h : UnitaryFieldData p f K) (hp : p ≠ 2)
    (α β : MulAut (hypPSU h 2 0)) :
    (α * β * α⁻¹ * β⁻¹) ^ 4 ∈ (MulAut.conj : hypPSU h 2 0 →* MulAut (hypPSU h 2 0)).range := by
  have := h.finite
  obtain ⟨b₁, rfl⟩ := semilinearAutHom_surjective h (by norm_num) (by norm_num) hp (by norm_num) α
  obtain ⟨b₂, rfl⟩ := semilinearAutHom_surjective h (by norm_num) (by norm_num) hp (by norm_num) β
  have hr : ((b₁ * b₂ * b₁⁻¹ * b₂⁻¹ : ↥(semilinearSimilitudes h 2 0)) :
      SemiGL (HypIndex 2 0) K).right = 1 := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, SemidirectProduct.mul_right,
      SemidirectProduct.inv_right]
    have := commutatorElement_eq_one_iff_mul_comm.mpr
      (ringAut_mul_comm K (b₁ : SemiGL (HypIndex 2 0) K).right
        (b₂ : SemiGL (HypIndex 2 0) K).right)
    rwa [commutatorElement_def] at this
  have := semilinearAutHom_pow_four_mem h _ hr
  simpa only [map_pow, map_mul, map_inv] using this

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.U4Red
