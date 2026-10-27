module

public import CFSG.ClassicalInvolution.Asc77.AscL62Aut

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19K

open CFSG.ClassicalInvolution
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem trace_semilinHom (G : GL (Fin 2) F) (τ : F ≃+* F) (A : SL(2, F)) :
    ((Asc77.AscL62.semilinHom G τ A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace =
      τ ((A : Matrix (Fin 2) (Fin 2) F).trace) := by
  rw [Asc77.AscL62.coe_semilinHom, Matrix.trace_units_conj]
  simp [Matrix.trace_fin_two]

theorem trace_eq_of_conj [Finite F] (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    {X : Type} [Group X] (ι₀ ι₁ : X ≃* SL(2, F)) (β : X →* X) (g : GL (Fin 2) F)
    (hβ : ∀ x, ι₁ (β x) = Asc77.AscL62.semilinHom g (RingEquiv.refl F) (ι₁ x)) (x : X) :
    ((ι₀ (β x) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace =
      ((ι₀ x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace := by
  obtain ⟨γ, H, -, hγ⟩ :=
    Asc77.AscL62.exists_semilinear_data hodd (by omega) (ι₀.symm.trans ι₁)
  have hsemi := Asc77.AscL62.eq_semilinHom_of_smul (by omega) (ι₀.symm.trans ι₁) H γ.right hγ
  have key : ∀ y : X, ((ι₁ y : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace =
      γ.right ((ι₀ y : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace := by
    intro y
    have h1 := hsemi (ι₀ y)
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
    rw [h1, trace_semilinHom]
  apply γ.right.injective
  rw [← key, ← key, hβ, trace_semilinHom, RingEquiv.refl_apply]

@[expose] def traceSL (c : F) : SL(2, F) :=
  ⟨!![c, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

theorem trace_traceSL (c : F) : ((traceSL c : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace = c := by
  simp [traceSL, Matrix.trace_fin_two]

theorem trace_inv (A : SL(2, F)) :
    ((A⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace =
      ((A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.trace_fin_two,
    Matrix.trace_fin_two]
  simp [add_comm]

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
