module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearAut

public section

namespace CFSG.LieType.SpecialLinear

open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def swapPair : SL(2, F) × SL(2, F) →* SL(2, F) × SL(2, F) where
  toFun m := (m.2, m.1)
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem swapPair_apply (m : SL(2, F) × SL(2, F)) : swapPair m = (m.2, m.1) := rfl

@[simp]
theorem swapPair_swapPair (m : SL(2, F) × SL(2, F)) : swapPair (swapPair m) = m := rfl

@[expose] noncomputable def pairAut (A₁ A₂ : GL (Fin 2) F) (σ : F ≃+* F) (sw : Bool) :
    SL(2, F) × SL(2, F) →* SL(2, F) × SL(2, F) where
  toFun m :=
    if sw then (CFSG.QuasithinUnique.K1.stdAut A₁ σ 0 m.2,
        CFSG.QuasithinUnique.K1.stdAut A₂ σ 0 m.1)
    else (CFSG.QuasithinUnique.K1.stdAut A₁ σ 0 m.1,
        CFSG.QuasithinUnique.K1.stdAut A₂ σ 0 m.2)
  map_one' := by cases sw <;> simp
  map_mul' m n := by
    cases sw <;> simp [map_mul]

theorem pairAut_false_apply (A₁ A₂ : GL (Fin 2) F) (σ : F ≃+* F)
    (m : SL(2, F) × SL(2, F)) :
    pairAut A₁ A₂ σ false m =
      (CFSG.QuasithinUnique.K1.stdAut A₁ σ 0 m.1,
        CFSG.QuasithinUnique.K1.stdAut A₂ σ 0 m.2) := rfl

theorem pairAut_true_apply (A₁ A₂ : GL (Fin 2) F) (σ : F ≃+* F)
    (m : SL(2, F) × SL(2, F)) :
    pairAut A₁ A₂ σ true m =
      (CFSG.QuasithinUnique.K1.stdAut A₁ σ 0 m.2,
        CFSG.QuasithinUnique.K1.stdAut A₂ σ 0 m.1) := rfl

theorem pairAut_false_inl (A₁ A₂ : GL (Fin 2) F) (σ : F ≃+* F) (g : SL(2, F)) :
    pairAut A₁ A₂ σ false (g, 1) =
      (CFSG.QuasithinUnique.K1.stdAut A₁ σ 0 g, 1) := by
  simp [pairAut_false_apply]

theorem pairAut_false_inr (A₁ A₂ : GL (Fin 2) F) (σ : F ≃+* F) (g : SL(2, F)) :
    pairAut A₁ A₂ σ false (1, g) =
      (1, CFSG.QuasithinUnique.K1.stdAut A₂ σ 0 g) := by
  simp [pairAut_false_apply]

theorem pairAut_true_inl (A₁ A₂ : GL (Fin 2) F) (σ : F ≃+* F) (g : SL(2, F)) :
    pairAut A₁ A₂ σ true (g, 1) =
      (1, CFSG.QuasithinUnique.K1.stdAut A₂ σ 0 g) := by
  simp [pairAut_true_apply]

theorem pairAut_true_inr (A₁ A₂ : GL (Fin 2) F) (σ : F ≃+* F) (g : SL(2, F)) :
    pairAut A₁ A₂ σ true (1, g) =
      (CFSG.QuasithinUnique.K1.stdAut A₁ σ 0 g, 1) := by
  simp [pairAut_true_apply]

end CFSG.LieType.SpecialLinear
