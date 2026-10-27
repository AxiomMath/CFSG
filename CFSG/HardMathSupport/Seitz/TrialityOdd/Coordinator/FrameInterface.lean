module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4PlaneMinus

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS.Stage2.Bender.Thm1


@[expose] def PhiFramePlaneGenAt (ε : ℤ) (r : ℕ) : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    r.Prime → r ≠ ℓ → (r : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * ((ℓ ^ f : ℕ) : ℤ) + 1 →
    ∀ E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      CFSG.IsElementaryAbelian r E → Nat.card E = r ^ 2 →
      (∃ F : D4PhiFrame K σ (ℓ ^ f) ε, F.Contains E) →
      Subgroup.closure {k : graphFixedRootGroup TwistTag.D4 K σ.toRingHom |
        ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤

@[expose] def TwistedTorusPlaneGenAt (r : ℕ) : Prop :=
  ∀ (ℓ f : ℕ) (hℓ : ℓ.Prime), ℓ ≠ 2 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    r.Prime → r ≠ ℓ → r ∣ ℓ ^ f + 1 →
    ∀ E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      CFSG.IsElementaryAbelian r E → Nat.card E = r ^ 2 →
      D4PlaneInTorusMinus ℓ f hℓ K σ E →
      Subgroup.closure {k : graphFixedRootGroup TwistTag.D4 K σ.toRingHom |
        ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤

end CFSG.HardMathSupport.Seitz.TrialityOdd
