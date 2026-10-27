module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataSemilinear

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (plusIndexEquiv)

variable (K : Type*) [Field K] (n : ℕ)

@[expose] def lowSpan (ℓ : ℕ) : Submodule K (Fin (2 * n) → K) where
  carrier := {v | ∀ i : Fin n, v (plusIndexEquiv n (.inr i)) = 0 ∧
    (ℓ ≤ i.val → v (plusIndexEquiv n (.inl i)) = 0)}
  add_mem' := by
    intro v w hv hw i
    refine ⟨by simp [(hv i).1, (hw i).1], fun h => by simp [(hv i).2 h, (hw i).2 h]⟩
  zero_mem' := fun _ => ⟨rfl, fun _ => rfl⟩
  smul_mem' := by
    intro c v hv i
    refine ⟨by simp [(hv i).1], fun h => by simp [(hv i).2 h]⟩

@[expose] def lowPerp (ℓ : ℕ) : Submodule K (Fin (2 * n) → K) where
  carrier := {v | ∀ i : Fin n, i.val < ℓ → v (plusIndexEquiv n (.inr i)) = 0}
  add_mem' := by
    intro v w hv hw i hi
    simp [hv i hi, hw i hi]
  zero_mem' := fun _ _ => rfl
  smul_mem' := by
    intro c v hv i hi
    simp [hv i hi]

variable {K n}

theorem lowSpan_le_lowPerp (ℓ : ℕ) : lowSpan K n ℓ ≤ lowPerp K n ℓ :=
  fun _ hv i _ => (hv i).1

theorem single_inl_mem_lowSpan {ℓ : ℕ} {i : Fin n} (hi : i.val < ℓ) :
    (Pi.single (plusIndexEquiv n (.inl i)) (1 : K) : Fin (2 * n) → K) ∈ lowSpan K n ℓ := by
  intro j
  have hne : ∀ x : Fin n ⊕ Fin n, x ≠ .inl i →
      (Pi.single (plusIndexEquiv n (.inl i)) (1 : K) : Fin (2 * n) → K) (plusIndexEquiv n x) = 0 :=
    fun x hx => Pi.single_eq_of_ne (fun h => hx ((plusIndexEquiv n).injective h)) _
  refine ⟨hne _ Sum.inr_ne_inl, fun hj => hne _ fun h => ?_⟩
  have : j = i := Sum.inl_injective h
  subst this
  omega

end CFSG.SeitzReduction.OmegaPilot
