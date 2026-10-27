module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F]

@[expose] def fixSub (σ : F ≃+* F) : Subfield F :=
  RingHom.eqLocusField σ.toRingHom (RingHom.id F)

@[expose] noncomputable def iotaGL (σ : F ≃+* F) : GL (Fin 3) (fixSub σ) →* GL (Fin 3) F :=
  Matrix.GeneralLinearGroup.map (fixSub σ).subtype

theorem coe_iotaGL (σ : F ≃+* F) (g : GL (Fin 3) (fixSub σ)) (i j : Fin 3) :
    ((iotaGL σ g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j =
      (((g : Matrix (Fin 3) (Fin 3) (fixSub σ)) i j : fixSub σ) : F) := rfl

theorem iotaGL_injective (σ : F ≃+* F) : Function.Injective (iotaGL σ) := by
  intro a b h
  apply Units.ext
  ext i j
  have := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F) i j) h
  simp only [coe_iotaGL] at this
  exact this

theorem iotaGL_scalar (σ : F ≃+* F) (c : (fixSub σ)ˣ) :
    iotaGL σ (Matrix.GeneralLinearGroup.scalar (Fin 3) c) =
      Matrix.GeneralLinearGroup.scalar (Fin 3)
        (Units.map (fixSub σ).subtype.toMonoidHom c) := by
  apply Units.ext
  ext i j
  rw [coe_iotaGL]
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> rfl

theorem exists_iota_of_fixed (σ : F ≃+* F) (g : GL (Fin 3) F)
    (h : ∀ i j, σ ((g : Matrix (Fin 3) (Fin 3) F) i j) = (g : Matrix (Fin 3) (Fin 3) F) i j) :
    ∃ g₀ : GL (Fin 3) (fixSub σ), iotaGL σ g₀ = g := by
  have hmap : GeneralLinearGroup.map (σ : F →+* F) g = g := by
    apply Units.ext
    ext i j
    exact h i j
  have hinv : ∀ i j, σ (((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j) =
      ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j := by
    intro i j
    have := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F) i j)
      (show GeneralLinearGroup.map (σ : F →+* F) g⁻¹ = g⁻¹ by rw [map_inv, hmap])
    exact this
  refine ⟨⟨Matrix.of fun i j => ⟨(g : Matrix (Fin 3) (Fin 3) F) i j, h i j⟩,
    Matrix.of fun i j => ⟨((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j, hinv i j⟩, ?_, ?_⟩,
    ?_⟩
  · ext i j
    have := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M i j) g.mul_inv
    simpa [Matrix.mul_apply, Matrix.one_apply, apply_ite Subtype.val, Fin.sum_univ_three] using this
  · ext i j
    have := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M i j) g.inv_mul
    simpa [Matrix.mul_apply, Matrix.one_apply, apply_ite Subtype.val, Fin.sum_univ_three] using this
  · apply Units.ext
    ext i j
    rfl

theorem fieldAut_comm_conjAut_iota (σ : F ≃+* F) (g : GL (Fin 3) (fixSub σ)) :
    conjAut 3 F (iotaGL σ g) * fieldAut 3 F σ = fieldAut 3 F σ * conjAut 3 F (iotaGL σ g) := by
  have e1 : fieldAut 3 F σ * conjAut 3 F (iotaGL σ g) =
      conjAut 3 F (GeneralLinearGroup.map (σ : F →+* F) (iotaGL σ g)) * fieldAut 3 F σ := by
    have := conjAut_mul_fieldAut_mul (n := 3) (K := F) 1 (iotaGL σ g) σ 1
    simpa using this
  have hfix : GeneralLinearGroup.map (σ : F →+* F) (iotaGL σ g) = iotaGL σ g := by
    apply Units.ext
    ext i j
    exact (((g : Matrix (Fin 3) (Fin 3) (fixSub σ)) i j).2)
  rw [e1, hfix]

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3
