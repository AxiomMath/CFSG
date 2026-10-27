module

public import CFSG.LieType.SeitzGeneration.RegimesOuterNarrow
public import CFSG.LieType.Chevalley.GraphFixedData

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration


@[expose] def InnerModelGen (Q : ℕ → Prop) : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ ℓ → Q p →
    ∀ E : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      IsElemAbelian p E → Nat.card E = p ^ 2 →
      E ≤ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range →
      RankLE2 p (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →
      ¬ (∃ S : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), S ≠ ⊥ ∧ IsPGroup ℓ S ∧
        ∀ β ∈ E, S.map β.toMonoidHom = S) →
      PlaneGen E

@[expose] def OuterModelGen (Q : ℕ → Prop) : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ ℓ → Q p →
    ∀ E : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      IsElemAbelian p E → Nat.card E = p ^ 2 →
      ¬ E ≤ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range →
      NarrowScope p E → PlaneGen E

end CFSG.HardMathSupport.Seitz.TrialityOdd
