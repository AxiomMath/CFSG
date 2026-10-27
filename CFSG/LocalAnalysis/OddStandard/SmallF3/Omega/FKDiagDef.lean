module

public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.LieType.Universal.Spin (quadPlus quadPlus_apply)

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)

@[expose] noncomputable def fkDiag (d : Fin 4 ⊕ Fin 4 → (GaloisField 3 1)ˣ) :
    (Fin 4 ⊕ Fin 4 → GaloisField 3 1) ≃ₗ[GaloisField 3 1] (Fin 4 ⊕ Fin 4 → GaloisField 3 1) :=
  LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfUnit (d i)

theorem fkDiag_apply (d : Fin 4 ⊕ Fin 4 → (GaloisField 3 1)ˣ)
    (v : Fin 4 ⊕ Fin 4 → GaloisField 3 1) (i : Fin 4 ⊕ Fin 4) :
    fkDiag d v i = (d i : GaloisField 3 1) * v i :=
  rfl

theorem fkDiag_symm_apply (d : Fin 4 ⊕ Fin 4 → (GaloisField 3 1)ˣ)
    (v : Fin 4 ⊕ Fin 4 → GaloisField 3 1) (i : Fin 4 ⊕ Fin 4) :
    (fkDiag d)⁻¹ v i = ((d i)⁻¹ : (GaloisField 3 1)ˣ) * v i :=
  rfl

theorem quadPlus_fkDiag (d : Fin 4 ⊕ Fin 4 → (GaloisField 3 1)ˣ) (μ : GaloisField 3 1)
    (hd : ∀ m : Fin 4, (d (.inl m) : GaloisField 3 1) * d (.inr m) = μ)
    (v : Fin 4 ⊕ Fin 4 → GaloisField 3 1) :
    quadPlus 4 (GaloisField 3 1) (fkDiag d v) = μ * quadPlus 4 (GaloisField 3 1) v := by
  rw [quadPlus_apply, quadPlus_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [fkDiag_apply, fkDiag_apply, ← hd m]
  ring

@[expose] noncomputable def fkD0 : Fin 4 ⊕ Fin 4 → (GaloisField 3 1)ˣ := Sum.elim 1 (-1)

@[expose] noncomputable def fkD1 : Fin 4 ⊕ Fin 4 → (GaloisField 3 1)ˣ :=
  Sum.elim ![-1, 1, 1, 1] ![1, -1, -1, -1]

theorem fkD0_mul (m : Fin 4) : (fkD0 (.inl m) : GaloisField 3 1) * fkD0 (.inr m) = -1 := by
  simp [fkD0]

theorem fkD1_mul (m : Fin 4) : (fkD1 (.inl m) : GaloisField 3 1) * fkD1 (.inr m) = -1 := by
  fin_cases m <;> simp [fkD1]

end CFSG.OddStandard.SmallF3.Omega
