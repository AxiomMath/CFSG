module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCoreDefs
public import CFSG.LieType.SeitzGeneration.ExcHigh.NativeCond

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three


@[expose] def TwE6All24PlaneIn (K : Type) [Field K] (σ : K ≃+* K)
    (E₀ : Subgroup (twistedE6RootGroup K σ)) : Prop :=
  ∃ P : Subgroup (twistedE6RootGroup K σ), P ≤ E₀ ∧ Nat.card P = 3 ^ 2 ∧
    ∀ s ∈ P, s ≠ 1 → twE6FixDim K σ s = 24

@[expose] def TwE6NegDatumDiag (K : Type) [Field K] (σ : K ≃+* K) (q : ℕ)
    (E₀ : Subgroup (twistedE6RootGroup K σ)) : Prop :=
  ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ q) ∧
  ∃ v : WeylGroup TwistTag.E6.tag,
    (∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ) ∧
  ∃ g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K),
    twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v ∧
    ∀ x ∈ E₀, g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x : ModGL TwistTag.E6.tag K) * g0 ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K)

@[expose] def TwE6ToralBar (K : Type) [Field K] (σ : K ≃+* K)
    (E₀ : Subgroup (twistedE6RootGroup K σ)) : Prop :=
  ∃ g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K), ∀ x ∈ E₀,
    g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) * g ∈
      torusGroup TwistTag.E6.tag (AlgebraicClosure K)

@[expose] def TwE6InnerNRTwo : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), Nat.card K = q ^ 2 →
    (∀ c, σ c = c ^ q) → q % 3 = 2 → q ≠ 2 →
    ∀ E₀ : Subgroup (twistedE6RootGroup K σ), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ → TwE6All24PlaneIn K σ E₀ ∨ TwE6NegDatumDiag K σ q E₀

@[expose] def TwE6ToralNegTwo : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), Nat.card K = q ^ 2 →
    (∀ c, σ c = c ^ q) → q % 3 = 2 →
    ∀ E₀ : Subgroup (twistedE6RootGroup K σ), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ → TwE6ToralBar K σ E₀ → TwE6NegDatumDiag K σ q E₀

@[expose] def TwE6InnerA2CaseTwo : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), Nat.card K = q ^ 2 →
    (∀ c, σ c = c ^ q) → q % 3 = 2 → q ≠ 2 →
    ∀ E₀ : Subgroup (twistedE6RootGroup K σ), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ →
      (∃ s ∈ E₀, s ≠ 1 ∧ twE6FixDim K σ s = 24) → TwE6All24PlaneIn K σ E₀ ∨ TwE6ToralBar K σ E₀

@[expose] def TwE6InnerNoA2Two : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), Nat.card K = q ^ 2 →
    (∀ c, σ c = c ^ q) → q % 3 = 2 → q ≠ 2 →
    ∀ E₀ : Subgroup (twistedE6RootGroup K σ), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ →
      (∀ s ∈ E₀, s ≠ 1 → twE6FixDim K σ s ≠ 24) → TwE6ToralBar K σ E₀

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
