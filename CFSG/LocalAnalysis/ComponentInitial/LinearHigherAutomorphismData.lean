module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphAction
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix Subgroup CFSG.ComponentClassification

variable (n : ℕ) (K : Type*) [Field K]

theorem map_scalars_eq (e : MulAut (SpecialLinearGroup (Fin n) K)) :
    (scalars n K).map (e : SpecialLinearGroup (Fin n) K →* SpecialLinearGroup (Fin n) K) =
      scalars n K := by
  rw [scalars_eq_center]
  exact map_center_eq e

@[expose] def descendAut :
    MulAut (SpecialLinearGroup (Fin n) K) →* MulAut (projectiveSL n K) where
  toFun e := QuotientGroup.congr (scalars n K) (scalars n K) e (map_scalars_eq n K e)
  map_one' := by
    ext x
    obtain ⟨g, rfl⟩ := proj_surjective n K x
    rfl
  map_mul' e₁ e₂ := by
    ext x
    obtain ⟨g, rfl⟩ := proj_surjective n K x
    rfl

theorem descendAut_proj (e : MulAut (SpecialLinearGroup (Fin n) K))
    (g : SpecialLinearGroup (Fin n) K) : descendAut n K e (proj n K g) = proj n K (e g) :=
  QuotientGroup.congr_mk' _ _ _ (map_scalars_eq n K e) g

@[expose] def conjAut : GL (Fin n) K →* MulAut (projectiveSL n K) :=
  (descendAut n K).comp (CatalogueBHigherLinearAction.slConjugation n K)

@[expose] def fieldAut : (K ≃+* K) →* MulAut (projectiveSL n K) :=
  (descendAut n K).comp (CatalogueBHigherLinearField.slFieldAut (Fin n) K)

@[expose] def dualAut : MulAut (projectiveSL n K) :=
  descendAut n K (CatalogueBGraphForm.slGraphAut n K)

@[expose] def linearAutGroup : Subgroup (MulAut (projectiveSL n K)) :=
  closure (Set.range (conjAut n K))

@[expose] def semilinearAutGroup : Subgroup (MulAut (projectiveSL n K)) :=
  closure ((linearAutGroup n K : Set (MulAut (projectiveSL n K))) ∪ Set.range (fieldAut n K))

@[expose] def standardAutGroup : Subgroup (MulAut (projectiveSL n K)) :=
  closure ((semilinearAutGroup n K : Set (MulAut (projectiveSL n K))) ∪ {dualAut n K})

variable {n K}

theorem conjAut_proj (A : GL (Fin n) K) (g : SpecialLinearGroup (Fin n) K) :
    conjAut n K A (proj n K g) =
      proj n K (CatalogueBHigherLinearAction.slConjugation n K A g) :=
  descendAut_proj n K _ g

theorem coe_slConjugation (A : GL (Fin n) K) (g : SpecialLinearGroup (Fin n) K) :
    ((CatalogueBHigherLinearAction.slConjugation n K A g : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) =
      (A : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) *
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  CatalogueBHigherLinearAction.slConjugation_matrix n K A g

theorem fieldAut_proj (σ : K ≃+* K) (g : SpecialLinearGroup (Fin n) K) :
    fieldAut n K σ (proj n K g) = proj n K (SpecialLinearGroup.map σ.toRingHom g) :=
  descendAut_proj n K _ g

theorem dualAut_proj (g : SpecialLinearGroup (Fin n) K) :
    dualAut n K (proj n K g) = proj n K (g⁻¹).transpose :=
  descendAut_proj n K _ g

theorem conjAut_mem_linearAutGroup (A : GL (Fin n) K) : conjAut n K A ∈ linearAutGroup n K :=
  subset_closure ⟨A, rfl⟩

theorem linearAutGroup_le_semilinearAutGroup : linearAutGroup n K ≤ semilinearAutGroup n K :=
  fun _ h => subset_closure (Or.inl h)

theorem fieldAut_mem_semilinearAutGroup (σ : K ≃+* K) :
    fieldAut n K σ ∈ semilinearAutGroup n K :=
  subset_closure (Or.inr ⟨σ, rfl⟩)

theorem semilinearAutGroup_le_standardAutGroup :
    semilinearAutGroup n K ≤ standardAutGroup n K :=
  fun _ h => subset_closure (Or.inl h)

theorem dualAut_mem_standardAutGroup : dualAut n K ∈ standardAutGroup n K :=
  subset_closure (Or.inr rfl)

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
