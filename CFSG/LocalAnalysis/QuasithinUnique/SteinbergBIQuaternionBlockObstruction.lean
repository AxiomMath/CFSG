module

public import CFSG.LocalAnalysis.QuasithinUnique.SteinbergBIQuaternionCommutant

public section

namespace CFSG.QuasithinUnique

open Matrix

variable {K : Type*} [Field K]

@[expose] def bdiag (G : Matrix (Fin 2) (Fin 2) K) (e : K) : Matrix (Fin 3) (Fin 3) K :=
  !![G 0 0, G 0 1, 0; G 1 0, G 1 1, 0; 0, 0, e]

theorem bdiag_mul (G H : Matrix (Fin 2) (Fin 2) K) (e f : K) :
    bdiag G e * bdiag H f = bdiag (G * H) (e * f) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bdiag, Matrix.mul_apply, Fin.sum_univ_succ]

theorem bdiag_one : bdiag (1 : Matrix (Fin 2) (Fin 2) K) 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bdiag]

theorem det_bdiag (G : Matrix (Fin 2) (Fin 2) K) (e : K) : (bdiag G e).det = G.det * e := by
  rw [bdiag, det_fin_three, det_fin_two]
  simp
  ring

theorem bdiag_injective {G H : Matrix (Fin 2) (Fin 2) K} {e f : K}
    (h : bdiag G e = bdiag H f) : G = H ∧ e = f := by
  have h' : ∀ i j, bdiag G e i j = bdiag H f i j := fun i j => by rw [h]
  refine ⟨?_, by simpa [bdiag] using h' 2 2⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [bdiag] using h' 0 0
  · simpa [bdiag] using h' 0 1
  · simpa [bdiag] using h' 1 0
  · simpa [bdiag] using h' 1 1

@[expose] def blockGamma (g : GL (Fin 2) K) : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨bdiag g (g : Matrix (Fin 2) (Fin 2) K).det⁻¹, by
    rw [det_bdiag, mul_inv_cancel₀]
    exact (Matrix.GeneralLinearGroup.det g).ne_zero⟩

theorem coe_blockGamma (g : GL (Fin 2) K) :
    (blockGamma g : Matrix (Fin 3) (Fin 3) K) = bdiag g (g : Matrix (Fin 2) (Fin 2) K).det⁻¹ :=
  rfl

theorem blockGamma_mul (g h : GL (Fin 2) K) : blockGamma (g * h) = blockGamma g * blockGamma h := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_blockGamma, coe_blockGamma, coe_blockGamma,
    bdiag_mul, Units.val_mul, det_mul, mul_inv]

theorem blockGamma_one : blockGamma (1 : GL (Fin 2) K) = 1 := by
  apply Subtype.ext
  rw [coe_blockGamma, Units.val_one, det_one, inv_one, bdiag_one,
    Matrix.SpecialLinearGroup.coe_one]

@[expose] def jmat : Matrix (Fin 2) (Fin 2) K := !![0, 1; -1, 0]

@[expose] def dmat : Matrix (Fin 3) (Fin 3) K := bdiag jmat 1

end CFSG.QuasithinUnique
