module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverTwRank

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule


@[expose] def twN0 : Fin TwistTag.E6.foldedTag.rank := ⟨0, by decide⟩

@[expose] def twN3 : Fin TwistTag.E6.foldedTag.rank := ⟨3, by decide⟩

@[expose] def Tw27Type {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (k : Type) [Field k] [Algebra K k]
    (χ : ↥(TwistedE6.fixedGroup K σ) → k) (J : Finset (Fin TwistTag.E6.foldedTag.rank)) : Prop :=
  J = Finset.univ.erase twN0 ∧ ∃ b < 2 * f, ∀ w : (orbitField TwistTag.E6 K σ twN0)ˣ,
    χ (hatH hf hK σ hσ twN0 w) =
      (algebraMap K k ((w : orbitField TwistTag.E6 K σ twN0) : K)) ^ (2 ^ b)

@[expose] def Tw78Type {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (k : Type) [Field k] [Algebra K k]
    (χ : ↥(TwistedE6.fixedGroup K σ) → k) (J : Finset (Fin TwistTag.E6.foldedTag.rank)) : Prop :=
  J = Finset.univ.erase twN3 ∧ ∃ b < f, ∀ w : (orbitField TwistTag.E6 K σ twN3)ˣ,
    χ (hatH hf hK σ hσ twN3 w) =
      (algebraMap K k ((w : orbitField TwistTag.E6 K σ twN3) : K)) ^ (2 ^ b)

@[expose] def TwTypeBoundStmt {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) : Prop :=
  ∀ (k : Type) [Field k] [Finite k] [CharP k 2] [Algebra K k] (m : ℕ)
    (ρ : Representation k ↥(TwistedE6.fixedGroup K σ) (Fin m → k)) (y : Fin m → k)
    (χ : ↥(TwistedE6.fixedGroup K σ) → k) (J : Finset (Fin TwistTag.E6.foldedTag.rank)) (g : ℕ),
    IsSimpleRep ρ → (∃ x, ρ x ≠ 1) →
    IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J → 1 ≤ g → g ∣ 2 * f →
    (∀ (a : Fin TwistTag.E6.foldedTag.rank) (w : (orbitField TwistTag.E6 K σ a)ˣ),
      χ (hatH hf hK σ hσ a w) ^ (2 ^ g) = χ (hatH hf hK σ hσ a w)) →
    (2 * f / g = 1 → 40 ≤ m ∨ Tw27Type hf K hK σ hσ k χ J) ∧
    (2 * f / g = 2 → 78 ≤ m ∧ (79 ≤ m ∨ Tw78Type hf K hK σ hσ k χ J)) ∧
    (3 ≤ 2 * f / g → 39 * (2 * f / g) + 1 ≤ m)

@[expose] def Tw27SurvivorBound {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) : Prop :=
  ∀ (k : Type) [Field k] [Finite k] [CharP k 2] [Algebra K k] (m : ℕ)
    (ρ : Representation k ↥(TwistedE6.fixedGroup K σ) (Fin m → k)) (y : Fin m → k)
    (χ : ↥(TwistedE6.fixedGroup K σ) → k) (J : Finset (Fin TwistTag.E6.foldedTag.rank)),
    IsSimpleRep ρ → (∃ x, ρ x ≠ 1) →
    IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J → Tw27Type hf K hK σ hσ k χ J →
    ∀ A : Subgroup ↥(TwistedE6.fixedGroup K σ), A ≠ ⊥ → (∀ a ∈ A, a ^ 2 = 1) →
      Nat.card A * Nat.card K ^ Module.finrank k (Representation.invariants (ρ.comp A.subtype)) <
        Nat.card K ^ m

@[expose] def Tw78HalfOffenderBound {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    Prop :=
  ∀ (k : Type) [Field k] [Finite k] [CharP k 2] [Algebra K k] (m : ℕ)
    (ρ : Representation k ↥(TwistedE6.fixedGroup K σ) (Fin m → k)) (y : Fin m → k)
    (χ : ↥(TwistedE6.fixedGroup K σ) → k) (J : Finset (Fin TwistTag.E6.foldedTag.rank)),
    IsSimpleRep ρ → IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J →
    Tw78Type hf K hK σ hσ k χ J →
    ∀ A : Subgroup ↥(TwistedE6.fixedGroup K σ), A ≠ ⊥ → (∀ a ∈ A, a ^ 2 = 1) →
      2 * Nat.card A * (2 ^ f) ^ Module.finrank k (Representation.invariants (ρ.comp A.subtype)) <
        (2 ^ f) ^ m

@[expose] def Tw78CentreTrivial {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    Prop :=
  ∀ (k : Type) [Field k] [Finite k] [CharP k 2] [Algebra K k] (m : ℕ)
    (ρ : Representation k ↥(TwistedE6.fixedGroup K σ) (Fin m → k)) (y : Fin m → k)
    (χ : ↥(TwistedE6.fixedGroup K σ) → k) (J : Finset (Fin TwistTag.E6.foldedTag.rank)),
    IsSimpleRep ρ → IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J →
    Tw78Type hf K hK σ hσ k χ J →
    ∀ x : ↥(TwistedE6.fixedGroup K σ), coverHom hf hK σ hσ x = 1 → ρ x = 1

@[expose] def TwE6AdjDisplacement {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    Prop :=
  ∀ (k : Type) [Field k] [Finite k] [CharP k 2] [Algebra K k] (m : ℕ)
    (ρ : Representation k ↥(TwistedE6.fixedGroup K σ) (Fin m → k)) (y : Fin m → k)
    (χ : ↥(TwistedE6.fixedGroup K σ) → k) (J : Finset (Fin TwistTag.E6.foldedTag.rank)),
    IsSimpleRep ρ → IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J →
    Tw78Type hf K hK σ hσ k χ J →
    ∀ u : ↥(TwistedE6.fixedGroup K σ), u ≠ 1 → u ^ 2 = 1 →
      22 ≤ Module.finrank k (LinearMap.range (ρ u - 1))

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
