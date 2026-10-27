module

public import CFSG.LieType.ChevTwo.OppCl.Defs

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open CFSG.LieType.BorelTits

section InducesOfConj

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

theorem semilinMap_apply (A : GL ι F) (σ : F ≃+* F) (v : ι → F) :
    semilinMap A σ v = Matrix.mulVec (A : Matrix ι ι F) (fun i => σ (v i)) := rfl

theorem map_mulVec_ringEquiv (σ : F ≃+* F) (M : Matrix ι ι F) (v : ι → F) :
    (fun i => σ (Matrix.mulVec M v i)) = Matrix.mulVec (M.map σ) (fun i => σ (v i)) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem semilinMap_mulVec (A : GL ι F) (σ : F ≃+* F) (M : Matrix ι ι F) (v : ι → F) :
    semilinMap A σ (Matrix.mulVec M v) =
      Matrix.mulVec ((A : Matrix ι ι F) * M.map σ * ((A⁻¹ : GL ι F) : Matrix ι ι F))
        (semilinMap A σ v) := by
  rw [semilinMap_apply, semilinMap_apply, map_mulVec_ringEquiv, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc]
  congr 1
  rw [Units.inv_mul, Matrix.mul_one]

variable [Finite F]

theorem induces_of_conj (H : Subgroup (GL ι F)) (A : GL ι F) (σ : F ≃+* F)
    (α : MulAut (StatedProj H))
    (hα : ∀ h : H, ∃ h' : H, ((h' : GL ι F) : Matrix ι ι F) =
        (A : Matrix ι ι F) * ((h : GL ι F) : Matrix ι ι F).map σ * ((A⁻¹ : GL ι F) : Matrix ι ι F) ∧
      α (QuotientGroup.mk' ((StatedScalars ι F).subgroupOf H) h) =
        QuotientGroup.mk' ((StatedScalars ι F).subgroupOf H) h') :
    Induces (QuotientGroup.mk' ((StatedScalars ι F).subgroupOf H)) (natRep H)
      (semilinMap A σ) α := by
  choose φ hφ1 hφ2 using hα
  have key : ∀ (h : H) (v : ι → F), semilinMap A σ (natRep H h v) =
      natRep H (φ h) (semilinMap A σ v) := by
    intro h v
    rw [natRep_apply, natRep_apply, semilinMap_mulVec, hφ1]
  have hinj : Function.Injective φ := by
    intro h₁ h₂ h
    apply natRep_injective H
    apply LinearMap.ext
    intro v
    apply (semilinMap A σ).injective
    rw [key, key, h]
  have hsurj : Function.Surjective φ := Finite.injective_iff_surjective.mp hinj
  refine ⟨fun h => ⟨φ h, key h, hφ2 h⟩, fun h => ?_⟩
  obtain ⟨h'', rfl⟩ := hsurj h
  refine ⟨h'', fun v => ?_, ?_⟩
  · apply (semilinMap A σ).injective
    have h2 : ∀ w, semilinMap A σ ((semilinMap A σ)⁻¹ w) = w :=
      fun w => (semilinMap A σ).apply_symm_apply w
    rw [h2, key, h2]
  · rw [← hφ2 h'']
    exact α.symm_apply_apply _

end InducesOfConj

end CFSG.LieType.ChevTwo.OppCl
