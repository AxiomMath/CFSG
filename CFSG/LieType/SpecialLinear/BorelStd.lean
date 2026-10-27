module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearAut

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LocalAnalysis.ComponentInitial

variable (n : ℕ) (F : Type) [Field F]

theorem isUnit_det_revPermMatrix :
    IsUnit (LinearFlag.permMatrix n F Fin.revPerm).det := by
  rw [LinearFlag.det_permMatrix]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with h | h <;>
    simp [h]

@[expose] noncomputable def revGL : GL (Fin n) F :=
  Matrix.GeneralLinearGroup.mk'' (LinearFlag.permMatrix n F Fin.revPerm)
    (isUnit_det_revPermMatrix n F)

theorem coe_revGL :
    ((revGL n F : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      LinearFlag.permMatrix n F Fin.revPerm :=
  rfl

@[expose] noncomputable def borelGraph : MulAut (SpecialLinearGroup (Fin n) F) :=
  CFSG.QuasithinUnique.K1.stdAut (revGL n F) (RingEquiv.refl F) 1

variable {n F}

@[expose] def IsUpperGL (A : GL (Fin n) F) : Prop :=
  ∀ i j : Fin n, j < i → (A : Matrix (Fin n) (Fin n) F) i j = 0

variable (n F) in
@[expose] noncomputable def borelStd (A : GL (Fin n) F) (σ : F ≃+* F) (ε : ℕ) :
    MulAut (SpecialLinearGroup (Fin n) F) :=
  CFSG.QuasithinUnique.K1.stdAut A σ 0 * borelGraph n F ^ ε

theorem borelStd_zero (A : GL (Fin n) F) (σ : F ≃+* F) :
    borelStd n F A σ 0 = CFSG.QuasithinUnique.K1.stdAut A σ 0 := by
  simp [borelStd]

theorem borelStd_apply (A : GL (Fin n) F) (σ : F ≃+* F) (ε : ℕ)
    (g : SpecialLinearGroup (Fin n) F) :
    borelStd n F A σ ε g = CFSG.QuasithinUnique.K1.stdAut A σ 0 ((borelGraph n F ^ ε) g) :=
  rfl

theorem coe_borelGraph (g : SpecialLinearGroup (Fin n) F) :
    ((borelGraph n F g : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      LinearFlag.permMatrix n F Fin.revPerm *
        ((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ *
        (((revGL n F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  rw [borelGraph, CFSG.QuasithinUnique.K1.coe_stdAut_one, coe_revGL]
  congr 2

end CFSG.LieType.SpecialLinear
