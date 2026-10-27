module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm

public section

namespace CFSG.GH74.Uniqueness.Bender.Frame

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {E : Type} [Field E]

@[expose] noncomputable def herm (hU : UnitaryFieldData p f E) (v w : Fin 3 → E) : E :=
  ∑ i, hU.bar (v i) * w i

@[expose] def PermutesLines (v : Fin 3 → (Fin 3 → E)) (g : GL (Fin 3) E) : Prop :=
  ∀ i, ∃ j, ∃ c : E, (g : Matrix (Fin 3) (Fin 3) E) *ᵥ v i = c • v j

@[expose] noncomputable def FixesIsotropicLine (hU : UnitaryFieldData p f E)
    (C : Subgroup (GL (Fin 3) E)) : Prop :=
  ∃ v : Fin 3 → E, v ≠ 0 ∧ herm hU v v = 0 ∧
    ∀ c ∈ C, ∃ μ : E, (c : Matrix (Fin 3) (Fin 3) E) *ᵥ v = μ • v

@[expose] def IsScalarMat (g : GL (Fin 3) E) : Prop :=
  ∃ μ : E, (g : Matrix (Fin 3) (Fin 3) E) = μ • (1 : Matrix (Fin 3) (Fin 3) E)

@[expose] noncomputable def IsOrthonormalFrame (hU : UnitaryFieldData p f E)
    (v : Fin 3 → (Fin 3 → E)) : Prop :=
  ∀ i j, herm hU (v i) (v j) = if i = j then 1 else 0


section Groups

variable (hU : UnitaryFieldData p f E) (v : Fin 3 → (Fin 3 → E))

@[expose] def frameTorusSU : Subgroup (gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) where
  carrier := {g | ∀ i, ∃ c : E, c ≠ 0 ∧
    ((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ v i = c • v i}
  mul_mem' := by
    rintro g g' hg hg' i
    obtain ⟨c, hc0, hc⟩ := hg i
    obtain ⟨c', hc0', hc'⟩ := hg' i
    refine ⟨c * c', mul_ne_zero hc0 hc0', ?_⟩
    change (((g : GL (Fin 3) E) * (g' : GL (Fin 3) E) : GL (Fin 3) E) :
      Matrix (Fin 3) (Fin 3) E) *ᵥ v i = _
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hc', Matrix.mulVec_smul, hc, smul_smul, mul_comm]
  one_mem' := fun i => ⟨1, one_ne_zero, by simp⟩
  inv_mem' := by
    intro g hg i
    obtain ⟨c, hc0, hc⟩ := hg i
    refine ⟨c⁻¹, inv_ne_zero hc0, ?_⟩
    have h1 : ((g⁻¹ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) : GL (Fin 3) E) =
        ((g : GL (Fin 3) E))⁻¹ := rfl
    rw [h1]
    have h2 := congrArg (fun w => (((g : GL (Fin 3) E))⁻¹ : GL (Fin 3) E).val *ᵥ w) hc
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_smul] at h2
    rw [Units.inv_mul, Matrix.one_mulVec] at h2
    rw [eq_inv_smul_iff₀ hc0]
    first
      | exact h2
      | exact h2.symm

@[expose] def frameMonoSU : Subgroup (gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) where
  carrier := {g | PermutesLines v (g : GL (Fin 3) E) ∧ PermutesLines v (g : GL (Fin 3) E)⁻¹}
  mul_mem' := by
    rintro g g' ⟨hg, hgi⟩ ⟨hg', hgi'⟩
    refine ⟨fun i => ?_, fun i => ?_⟩
    · obtain ⟨j, c, hc⟩ := hg' i
      obtain ⟨k, d, hd⟩ := hg j
      refine ⟨k, d * c, ?_⟩
      change (((g : GL (Fin 3) E) * (g' : GL (Fin 3) E) : GL (Fin 3) E) :
        Matrix (Fin 3) (Fin 3) E) *ᵥ v i = _
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul, hd, smul_smul, mul_comm]
    · obtain ⟨j, c, hc⟩ := hgi i
      obtain ⟨k, d, hd⟩ := hgi' j
      refine ⟨k, d * c, ?_⟩
      change ((((g : GL (Fin 3) E) * (g' : GL (Fin 3) E))⁻¹ : GL (Fin 3) E) :
        Matrix (Fin 3) (Fin 3) E) *ᵥ v i = _
      rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul, hd,
        smul_smul, mul_comm]
  one_mem' := ⟨fun i => ⟨i, 1, by simp⟩, fun i => ⟨i, 1, by simp⟩⟩
  inv_mem' := by
    intro g hg
    exact ⟨hg.2, by simpa using hg.1⟩

theorem mem_frameTorusSU {g : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)} :
    g ∈ frameTorusSU hU v ↔ ∀ i, ∃ c : E, c ≠ 0 ∧
      ((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ v i = c • v i := Iff.rfl

theorem mem_frameMonoSU {g : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)} :
    g ∈ frameMonoSU hU v ↔
      PermutesLines v (g : GL (Fin 3) E) ∧ PermutesLines v (g : GL (Fin 3) E)⁻¹ := Iff.rfl

@[expose] noncomputable def frameTorus :
    Subgroup (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) :=
  (frameTorusSU hU v).map
    (QuotientGroup.mk' (normOneScalars hU (gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) 3))

@[expose] noncomputable def frameMono :
    Subgroup (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) :=
  (frameMonoSU hU v).map
    (QuotientGroup.mk' (normOneScalars hU (gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) 3))

end Groups

end CFSG.GH74.Uniqueness.Bender.Frame
