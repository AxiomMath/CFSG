module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearPureGraph
import CFSG.HardMathSupport.Timmesfeld.LinearRank.UnitaryDiagonal
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormTransport

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

@[expose] noncomputable def antiunitaryMap (h : UnitaryFieldData p f K)
    (A : Matrix (Fin n) (Fin n) K) : (Fin n → K) →ₛₗ[h.bar] (Fin n → K) where
  toFun v := A *ᵥ fun i => h.bar (v i)
  map_add' v w := by
    rw [← mulVec_add]
    congr 1
    funext i
    exact map_add h.bar (v i) (w i)
  map_smul' a v := by
    rw [← mulVec_smul]
    congr 1
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]

theorem antiunitaryMap_apply (h : UnitaryFieldData p f K) (A : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K) : antiunitaryMap h A v = A *ᵥ fun i => h.bar (v i) :=
  rfl

section Transport

variable (h : UnitaryFieldData p f K) {C C₀ : Matrix (Fin n) (Fin n) K} {H : GL (Fin n) K}
  (hH : ((H : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * C * H = C₀)

include hH

theorem inv_gram_eq :
    (((H⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * C₀ *
      ((H⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = C := by
  rw [← hH, ← barTranspose_mul_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one, Matrix.one_mul,
    Matrix.mul_one]

theorem conj_mem_gramSU_of_gram {g : GL (Fin n) K} (hg : g ∈ gramSU h C₀) :
    H * g * H⁻¹ ∈ gramSU h C := by
  refine mem_gramSU.mpr ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, barTranspose_mul_mul, barTranspose_mul_mul, hH,
      (mem_gramSU.mp hg).1, inv_gram_eq h hH]
  · rw [Units.val_mul, Units.val_mul, det_mul, det_mul, (mem_gramSU.mp hg).2, mul_one, ← det_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]

@[expose] noncomputable def gramTransportSU : gramSU h C₀ ≃* gramSU h C where
  toFun g := ⟨H * g * H⁻¹, conj_mem_gramSU_of_gram h hH g.2⟩
  invFun g := ⟨H⁻¹ * g * H⁻¹⁻¹, conj_mem_gramSU_of_gram h (inv_gram_eq h hH) g.2⟩
  left_inv g := Subtype.ext (by
    change H⁻¹ * (H * (g : GL (Fin n) K) * H⁻¹) * H⁻¹⁻¹ = g
    group)
  right_inv g := Subtype.ext (by
    change H * (H⁻¹ * (g : GL (Fin n) K) * H⁻¹⁻¹) * H⁻¹ = g
    group)
  map_mul' g g' := Subtype.ext (by
    change H * ((g : GL (Fin n) K) * g') * H⁻¹ =
      (H * (g : GL (Fin n) K) * H⁻¹) * (H * (g' : GL (Fin n) K) * H⁻¹)
    group)

theorem coe_gramTransportSU (g : gramSU h C₀) :
    ((gramTransportSU h hH g : gramSU h C) : GL (Fin n) K) = H * g * H⁻¹ :=
  rfl

theorem coe_gramTransportSU_symm (g : gramSU h C) :
    (((gramTransportSU h hH).symm g : gramSU h C₀) : GL (Fin n) K) = H⁻¹ * g * H⁻¹⁻¹ :=
  rfl

theorem map_normOneScalars_gramTransport :
    (normOneScalars h (gramSU h C₀) n).map (gramTransportSU h hH).toMonoidHom =
      normOneScalars h (gramSU h C) n := by
  have hfix : ∀ (M : GL (Fin n) K) (c : Kˣ),
      M * GeneralLinearGroup.scalar (Fin n) c * M⁻¹ = GeneralLinearGroup.scalar (Fin n) c :=
    fun M c => by rw [(commute_scalar c M).eq, mul_inv_cancel_right]
  ext z
  constructor
  · rintro ⟨y, ⟨c, hcN, hcn, hy⟩, rfl⟩
    refine ⟨c, hcN, hcn, ?_⟩
    change H * (y : GL (Fin n) K) * H⁻¹ = _
    rw [hy, hfix]
  · rintro ⟨c, hcN, hcn, hz⟩
    refine ⟨(gramTransportSU h hH).symm z, ⟨c, hcN, hcn, ?_⟩, MulEquiv.apply_symm_apply _ _⟩
    rw [coe_gramTransportSU_symm, hz, hfix]

@[expose] noncomputable def gramTransportP : primeFormP h C₀ ≃* primeFormP h C :=
  QuotientGroup.congr _ _ (gramTransportSU h hH) (map_normOneScalars_gramTransport h hH)

theorem gramTransportP_mk (g : gramSU h C₀) :
    gramTransportP h hH (g : primeFormP h C₀) =
      ((gramTransportSU h hH g : gramSU h C) : primeFormP h C) :=
  QuotientGroup.congr_mk _ _ _ _ g

theorem gramTransportP_symm_mk (g : gramSU h C) :
    (gramTransportP h hH).symm (g : primeFormP h C) =
      (((gramTransportSU h hH).symm g : gramSU h C₀) : primeFormP h C₀) := by
  rw [MulEquiv.symm_apply_eq, gramTransportP_mk, MulEquiv.apply_symm_apply]

end Transport

theorem isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin n) K) :=
  CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one

theorem blockSwapJ_eq_submatrix [CharP K 2] {r : ℕ} (hr : r + r = n) :
    blockSwapJ n r = (Matrix.J (Fin r) K).submatrix (finSumFinEquiv.trans (finCongr hr)).symm
      (finSumFinEquiv.trans (finCongr hr)).symm := by
  ext i j
  rw [Matrix.submatrix_apply, J_apply_eq_blockSwapJ hr, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

theorem blockSwapJ_mul_self [CharP K 2] {r : ℕ} (hr : r + r = n) :
    blockSwapJ n r * blockSwapJ (K := K) n r = 1 := by
  have hneg : (-1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 := by
    ext i j
    rw [Matrix.neg_apply, CharTwo.neg_eq]
  rw [blockSwapJ_eq_submatrix hr, Matrix.submatrix_mul_equiv, Matrix.J_squared, hneg,
    Matrix.submatrix_one_equiv]

@[expose] noncomputable def blockSwapGL [CharP K 2] {r : ℕ} (hr : r + r = n) : GL (Fin n) K :=
  ⟨blockSwapJ n r, blockSwapJ n r, blockSwapJ_mul_self hr, blockSwapJ_mul_self hr⟩

theorem coe_blockSwapGL [CharP K 2] {r : ℕ} (hr : r + r = n) :
    ((blockSwapGL hr : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = blockSwapJ n r :=
  rfl

theorem isPrimeFormGram_blockSwapGL [CharP K 2] {r : ℕ} (hr : r + r = n) :
    IsPrimeFormGram (blockSwapGL (K := K) hr) := by
  refine ⟨?_, fun i j => ?_⟩
  · rw [coe_blockSwapGL]
    ext i j
    simp only [transpose_apply, blockSwapJ, Matrix.of_apply, or_comm]
  · rw [coe_blockSwapGL, blockSwapJ, Matrix.of_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
