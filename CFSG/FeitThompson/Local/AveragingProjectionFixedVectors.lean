module

public import Mathlib.RepresentationTheory.Invariants

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Matrix

namespace CFSG.FeitThompson

variable {R : Type*} [CommRing R] {B : Type*} [Group B]
  {n : Type*} [Fintype n] [DecidableEq n]

def glRepresentation (ρ : B →* GL n R) : Representation R B (n → R) :=
  (Units.coeHom (Module.End R (n → R))).comp
    (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρ)

@[simp]
lemma glRepresentation_apply (ρ : B →* GL n R) (b : B) :
    glRepresentation ρ b = (ρ b : Matrix n n R).mulVecLin := (rfl)

lemma glRepresentation_apply_apply (ρ : B →* GL n R) (b : B) (v : n → R) :
    glRepresentation ρ b v = (ρ b : Matrix n n R) *ᵥ v := (rfl)

lemma mem_invariants_glRepresentation (ρ : B →* GL n R) (v : n → R) :
    v ∈ (glRepresentation ρ).invariants ↔ ∀ b : B, (ρ b : Matrix n n R) *ᵥ v = v := by
  simp [Representation.mem_invariants]

section Averaging

variable [Fintype B] [Invertible (Fintype.card B : R)]

private lemma averageMap_eq {V : Type*} [AddCommGroup V] [Module R V]
    (σ : Representation R B V) :
    σ.averageMap = ⅟(Fintype.card B : R) • ∑ b : B, σ b := by
  rw [Representation.averageMap, GroupAlgebra.average, map_smul, map_sum]
  simp

def averagingMatrix (ρ : B →* GL n R) : Matrix n n R :=
  ⅟(Fintype.card B : R) • ∑ b : B, (ρ b : Matrix n n R)

lemma averagingMatrix_mulVec (ρ : B →* GL n R) (v : n → R) :
    averagingMatrix ρ *ᵥ v = ⅟(Fintype.card B : R) • ∑ b : B, (ρ b : Matrix n n R) *ᵥ v := by
  rw [averagingMatrix, smul_mulVec, sum_mulVec]

lemma mulVecLin_averagingMatrix (ρ : B →* GL n R) :
    (averagingMatrix ρ).mulVecLin = (glRepresentation ρ).averageMap := by
  rw [averageMap_eq, averagingMatrix, ← Matrix.toLin'_apply', map_smul, map_sum]
  simp [Matrix.toLin'_apply']

theorem isProj_averagingMatrix (ρ : B →* GL n R) :
    LinearMap.IsProj (glRepresentation ρ).invariants (averagingMatrix ρ).mulVecLin := by
  rw [mulVecLin_averagingMatrix]
  exact Representation.isProj_averageMap _

theorem averagingMatrix_mul_self (ρ : B →* GL n R) :
    averagingMatrix ρ * averagingMatrix ρ = averagingMatrix ρ := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_apply', Matrix.toLin'_apply', Matrix.mulVecLin_mul]
  exact (isProj_averagingMatrix ρ).isIdempotentElem

theorem averagingMatrix_sq (ρ : B →* GL n R) :
    averagingMatrix ρ ^ 2 = averagingMatrix ρ := by
  rw [pow_two, averagingMatrix_mul_self]

theorem range_mulVecLin_averagingMatrix (ρ : B →* GL n R) :
    LinearMap.range (averagingMatrix ρ).mulVecLin = (glRepresentation ρ).invariants :=
  (isProj_averagingMatrix ρ).range

theorem averagingMatrix_mulVec_of_forall (ρ : B →* GL n R) {v : n → R}
    (hv : ∀ b : B, (ρ b : Matrix n n R) *ᵥ v = v) : averagingMatrix ρ *ᵥ v = v :=
  (isProj_averagingMatrix ρ).map_id v ((mem_invariants_glRepresentation ρ v).2 hv)

theorem mulVec_averagingMatrix_mulVec (ρ : B →* GL n R) (v : n → R) (b : B) :
    (ρ b : Matrix n n R) *ᵥ (averagingMatrix ρ *ᵥ v) = averagingMatrix ρ *ᵥ v :=
  (isProj_averagingMatrix ρ).map_mem v b

theorem range_averagingMatrix_mulVec (ρ : B →* GL n R) :
    Set.range (fun v => averagingMatrix ρ *ᵥ v) =
      {v : n → R | ∀ b : B, (ρ b : Matrix n n R) *ᵥ v = v} := by
  ext v
  refine ⟨?_, fun hv => ⟨v, averagingMatrix_mulVec_of_forall ρ hv⟩⟩
  rintro ⟨w, rfl⟩
  exact fun b => mulVec_averagingMatrix_mulVec ρ w b

end Averaging

end CFSG.FeitThompson
