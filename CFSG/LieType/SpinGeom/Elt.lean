module

public import CFSG.LieType.SpinGeom.Cases
public import CFSG.LieType.SpinGeom.Count
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.LieType.SpinGeom

open CFSG.StandardType CFSG.StandardType.Triality CFSG.LieType.D4Small CFSG.LieType.Sp6Spin
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear QuadraticMap
open scoped Matrix

section Elt

variable {K : Type} [Field K] [Finite K] [CharP K 2]

noncomputable def sE (c m : Fin 3 → K) (g : Matrix.SpecialLinearGroup (Fin 3) K) : Om8 K :=
  (exists_mem_spinSeven_spinElt c m (g : Matrix (Fin 3) (Fin 3) K) g.2).choose

theorem sE_mem (c m : Fin 3 → K) (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    sE c m g ∈ spinSeven K :=
  (exists_mem_spinSeven_spinElt c m (g : Matrix (Fin 3) (Fin 3) K) g.2).choose_spec.1

theorem sE_act (c m : Fin 3 → K) (g : Matrix.SpecialLinearGroup (Fin 3) K)
    (v : Fin (2 * 4) → K) :
    (((sE c m g : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v =
      spinElt K c m (g : Matrix (Fin 3) (Fin 3) K) v :=
  (exists_mem_spinSeven_spinElt c m (g : Matrix (Fin 3) (Fin 3) K) g.2).choose_spec.2 v

omit [Finite K] [CharP K 2] in
theorem om8_eq_of_act {h h' : Om8 K}
    (e : ∀ v, ((h : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v =
      ((h' : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v) : h = h' :=
  Subtype.ext (gl_eq_of_mulVec_eq e)

theorem sE_eq_of_act {c m : Fin 3 → K} {g : Matrix.SpecialLinearGroup (Fin 3) K} {h : Om8 K}
    (e : ∀ v, ((h : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v =
      spinElt K c m (g : Matrix (Fin 3) (Fin 3) K) v) : h = sE c m g :=
  om8_eq_of_act fun v => (e v).trans (sE_act c m g v).symm

theorem sE_mul (c₁ m₁ c₂ m₂ : Fin 3 → K) (g₁ g₂ : Matrix.SpecialLinearGroup (Fin 3) K) :
    sE c₁ m₁ g₁ * sE c₂ m₂ g₂ =
      sE (c₁ + (g₁ : Matrix (Fin 3) (Fin 3) K).adjugateᵀ *ᵥ c₂ +
        altMat K ((g₁ : Matrix (Fin 3) (Fin 3) K) *ᵥ m₂) *ᵥ m₁)
        (m₁ + (g₁ : Matrix (Fin 3) (Fin 3) K) *ᵥ m₂) (g₁ * g₂) := by
  refine sE_eq_of_act fun v => ?_
  have e : ((((sE c₁ m₁ g₁ * sE c₂ m₂ g₂ : Om8 K)) : GL (Fin (2 * 4)) K) :
      Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) =
      (((sE c₁ m₁ g₁ : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *
        (((sE c₂ m₂ g₂ : Om8 K) : GL (Fin (2 * 4)) K) :
          Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) := rfl
  rw [e, ← Matrix.mulVec_mulVec, sE_act, sE_act, spinElt_comp c₁ m₁ _ g₁.2,
    Matrix.SpecialLinearGroup.coe_mul]

theorem sE_one : sE (0 : Fin 3 → K) 0 (1 : Matrix.SpecialLinearGroup (Fin 3) K) = 1 := by
  refine (om8_eq_of_act fun v => ?_).symm
  rw [sE_act]
  simp [spinElt_one]

theorem sE_fix (c m : Fin 3 → K) (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    (((sE c m g : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
      frameE K 0 = frameE K 0 := by
  rw [sE_act, spinElt_frameE_zero]

end Elt

end CFSG.LieType.SpinGeom
