module

public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.RootTransport

open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne



section MaxHeight

variable {τ : Tag}

@[expose] def IsMaxHeightRoot (τ : Tag) (θ : Fin τ.rank → ℤ) : Prop :=
  IsRoot τ θ ∧ ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → height γ ≤ height θ

theorem height_add_eq (u v : Fin τ.rank → ℤ) : height (u + v) = height u + height v := by
  simp [height, Finset.sum_add_distrib]

theorem exists_maxHeightRoot (τ : Tag) : ∃ θ : Fin τ.rank → ℤ, IsMaxHeightRoot τ θ := by
  classical
  have hrank : 0 < τ.rank := by cases τ <;> decide
  obtain ⟨θ, hθ, hmax⟩ := Finset.exists_max_image (rootFinset τ) (fun v => height v)
    ⟨Pi.single ⟨0, hrank⟩ 1, mem_rootFinset.2 (isRoot_single τ ⟨0, hrank⟩)⟩
  exact ⟨θ, mem_rootFinset.1 hθ, fun γ hγ => hmax γ (mem_rootFinset.2 hγ)⟩

theorem IsMaxHeightRoot.height_pos {θ : Fin τ.rank → ℤ} (hθ : IsMaxHeightRoot τ θ) : 0 < height θ := by
  have hrank : 0 < τ.rank := by cases τ <;> decide
  have h := hθ.2 (Pi.single ⟨0, hrank⟩ 1) (isRoot_single τ ⟨0, hrank⟩)
  have h1 : height (Pi.single ⟨0, hrank⟩ (1 : ℤ) : Fin τ.rank → ℤ) = 1 := by
    simp [height]
  omega

theorem IsMaxHeightRoot.not_isRoot_add {θ : Fin τ.rank → ℤ} (hθ : IsMaxHeightRoot τ θ)
    {γ : Fin τ.rank → ℤ} (hpos : 0 < height γ) : ¬ IsRoot τ (θ + γ) := fun h => by
  have := hθ.2 _ h
  rw [height_add_eq] at this
  omega

theorem IsMaxHeightRoot.commute_xPar {D : AdjData τ} (hD : D.Valid) (hτ : NoG2 τ)
    {θ : Fin τ.rank → ℤ} (hθ : IsMaxHeightRoot τ θ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hpos : 0 < height γ) {K : Type} [Field K] (a b : K) :
    Commute (xPar (rootOperatorFamily τ) θ a) (xPar (rootOperatorFamily τ) γ b) := by
  refine CFSG.LieType.Steinberg.Adjoint.commute_xPar hD hτ hθ.1 hγ ?_ (hθ.not_isRoot_add hpos) a b
  intro h0
  have h1 := congrArg height h0
  rw [height_add_eq] at h1
  have h2 := hθ.height_pos
  simp [height] at h1
  simp only [height] at h2 hpos
  omega

theorem IsMaxHeightRoot.rootNorm_F4 {θ : Fin Tag.F4.rank → ℤ} (hθ : IsMaxHeightRoot Tag.F4 θ) :
    rootNorm Tag.F4 θ = 4 := by
  have hmem : θ ∈ rootFinset Tag.F4 := mem_rootFinset.2 hθ.1
  have hmax : ∀ γ ∈ rootFinset Tag.F4, height γ ≤ height θ := fun γ hγ =>
    hθ.2 γ (mem_rootFinset.1 hγ)
  have key : ∀ θ ∈ rootFinset Tag.F4, (∀ γ ∈ rootFinset Tag.F4, height γ ≤ height θ) →
      rootNorm Tag.F4 θ = 4 := by decide +kernel
  exact key θ hmem hmax

end MaxHeight

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
