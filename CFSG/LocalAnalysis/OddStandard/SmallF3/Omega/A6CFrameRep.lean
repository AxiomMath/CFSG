module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Sim
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Frame

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {n : ℕ} {c : ZMod 3}

noncomputable def a6cFrameRep (fr : NFrame Q (Fin n) c) :
    simGroup Q →* Matrix (Fin n) (Fin n) (ZMod 3) :=
  (LinearMap.toMatrixAlgEquiv fr.b : (V →ₗ[ZMod 3] V) →* Matrix (Fin n) (Fin n) (ZMod 3)).comp
    ((LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 3) (M := V)).comp
      (simGroup Q).subtype)

theorem a6cFrameRep_apply (fr : NFrame Q (Fin n) c) (γ : simGroup Q) (i j : Fin n) :
    a6cFrameRep fr γ i j = fr.b.repr ((γ : V ≃ₗ[ZMod 3] V) (fr.b j)) i := by
  have h := LinearMap.toMatrixAlgEquiv_apply fr.b
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom ((simGroup Q).subtype γ)) i j
  simpa [a6cFrameRep, MonoidHom.comp_apply, LinearMap.toMatrixAlgEquiv_apply] using h

private lemma a6cFrameRep_piOrth (fr : NFrame Q (Fin n) c) :
    a6cFrameRep fr (orthToSim Q (piOrth Q)) = -1 := by
  ext i j
  rw [a6cFrameRep_apply, coe_orthToSim, coe_piOrth_apply]
  by_cases hij : i = j
  · rw [hij]
    simp [map_neg, Finsupp.neg_apply, Pi.neg_apply, Module.Basis.repr_self_apply,
      Matrix.one_apply]
  · have hji : j ≠ i := fun h => hij h.symm
    simp [map_neg, Finsupp.neg_apply, Pi.neg_apply, Module.Basis.repr_self_apply,
      Matrix.one_apply, hij, hji]

theorem a6cFrameRep_injective (fr : NFrame Q (Fin n) c) : Function.Injective (a6cFrameRep fr) := by
  intro γ₁ γ₂ h
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (LinearMap.toMatrixAlgEquiv fr.b).injective
  simpa [a6cFrameRep, MonoidHom.comp_apply] using h

theorem a6cFrameRep_mem_piSim (fr : NFrame Q (Fin n) c) (γ : simGroup Q) :
    γ ∈ piSim Q ↔ a6cFrameRep fr γ = 1 ∨ a6cFrameRep fr γ = -1 := by
  constructor
  · intro h
    rcases mem_piSim_iff.mp h with rfl | rfl
    · exact Or.inl (map_one _)
    · exact Or.inr (a6cFrameRep_piOrth fr)
  · rintro (h | h)
    · exact mem_piSim_iff.mpr (Or.inl (a6cFrameRep_injective fr (h.trans (map_one _).symm)))
    · exact mem_piSim_iff.mpr
        (Or.inr (a6cFrameRep_injective fr (h.trans (a6cFrameRep_piOrth fr).symm)))

theorem a6cFrameRep_signChange (fr : NFrame Q (Fin n) c) (J : Finset (Fin n)) :
    a6cFrameRep fr (orthToSim Q (fr.signChange J)) =
      Matrix.diagonal fun i => if i ∈ J then (-1 : ZMod 3) else 1 := by
  ext i j
  rw [a6cFrameRep_apply, coe_orthToSim, NFrame.repr_signChange, Matrix.diagonal_apply,
    Module.Basis.repr_self_apply]
  by_cases hij : i = j
  · rw [hij]
    by_cases hJ : j ∈ J <;> simp [hJ]
  · have hji : j ≠ i := fun h => hij h.symm
    by_cases hJ : i ∈ J <;> simp [hJ, hij, hji]

end CFSG.OddStandard.SmallF3.Omega
