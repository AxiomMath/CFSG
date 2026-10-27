module

public import CFSG.LieType.SeitzGeneration.ExcTorusRankTw
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergRoot
public import CFSG.RankThree.PartOne.CTP.SeitzField
public import CFSG.RankThree.PartOne.CTP.StrongPClassification

open CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartOne.CTP
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne


noncomputable abbrev subfieldGroup (τ : Tag) {K : Type} [Field K] (σ : K ≃+* K) :
    Subgroup ↥(adjointGroup τ K) :=
  fixedSubgroup (entrywiseAdjointAut τ σ)

@[expose] def SubfieldMaximalLeOne (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (p : ℕ), p.Prime → 5 ≤ p → p ≠ ringChar K →
    orderOf σ = p → degCount τ (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 1 →
    p ∣ Nat.card ↥(subfieldGroup τ σ) →
    ∀ M : Subgroup ↥(adjointGroup τ K), subfieldGroup τ σ ≤ M → M = subfieldGroup τ σ ∨ M = ⊤

@[expose] def SubfieldMaximalLeOneTwE6 : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (ℓ ^ f) ^ 2 →
    ∀ (σ : K ≃+* K), (∀ c, σ c = c ^ (ℓ ^ f)) → ∀ (p : ℕ), p.Prime → 5 ≤ p → p ≠ ℓ →
    ∀ η : K ≃+* K, orderOf η = p → degCountTw (orderOf (((ℓ ^ f : ℕ)) : ZMod p)) ≤ 1 →
    p ∣ Nat.card ↥(fixedSubgroup (fieldActor (t := TwistTag.E6) σ η)) →
    ∀ M : Subgroup ↥(twistedE6RootGroup K σ),
      fixedSubgroup (fieldActor (t := TwistTag.E6) σ η) ≤ M →
      M = fixedSubgroup (fieldActor (t := TwistTag.E6) σ η) ∨ M = ⊤

@[expose] def SubfieldMaximalAll (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (p : ℕ), p.Prime → 5 ≤ p → p ≠ ringChar K →
    orderOf σ = p → ∀ M : Subgroup ↥(adjointGroup τ K), subfieldGroup τ σ ≤ M → M = subfieldGroup τ σ ∨ M = ⊤

@[expose] def SubfieldMaximalAllTwE6 : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (ℓ ^ f) ^ 2 →
    ∀ (σ : K ≃+* K), (∀ c, σ c = c ^ (ℓ ^ f)) → ∀ (p : ℕ), p.Prime → 5 ≤ p → p ≠ ℓ →
    ∀ η : K ≃+* K, orderOf η = p →
    ∀ M : Subgroup ↥(twistedE6RootGroup K σ),
      fixedSubgroup (fieldActor (t := TwistTag.E6) σ η) ≤ M →
      M = fixedSubgroup (fieldActor (t := TwistTag.E6) σ η) ∨ M = ⊤

@[expose] def SubfieldMaximalAllOdd (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (p : ℕ), p.Prime → p ≠ 2 → p ≠ ringChar K →
    orderOf σ = p → ∀ M : Subgroup ↥(adjointGroup τ K), subfieldGroup τ σ ≤ M → M = subfieldGroup τ σ ∨ M = ⊤

@[expose] def SubfieldMaximalAllThree (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (p : ℕ), p = 3 → p ≠ ringChar K →
    orderOf σ = p → ∀ M : Subgroup ↥(adjointGroup τ K), subfieldGroup τ σ ≤ M → M = subfieldGroup τ σ ∨ M = ⊤

@[expose] def SubfieldMaximalAllOddTwE6 : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (ℓ ^ f) ^ 2 →
    ∀ (σ : K ≃+* K), (∀ c, σ c = c ^ (ℓ ^ f)) → ∀ (p : ℕ), p.Prime → p ≠ 2 → p ≠ ℓ →
    ∀ η : K ≃+* K, orderOf η = p →
    ∀ M : Subgroup ↥(twistedE6RootGroup K σ),
      fixedSubgroup (fieldActor (t := TwistTag.E6) σ η) ≤ M →
      M = fixedSubgroup (fieldActor (t := TwistTag.E6) σ η) ∨ M = ⊤

@[expose] def SubfieldMaximalAllThreeTwE6 : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (ℓ ^ f) ^ 2 →
    ∀ (σ : K ≃+* K), (∀ c, σ c = c ^ (ℓ ^ f)) → ∀ (p : ℕ), p = 3 → p ≠ ℓ →
    ∀ η : K ≃+* K, orderOf η = p →
    ∀ M : Subgroup ↥(twistedE6RootGroup K σ),
      fixedSubgroup (fieldActor (t := TwistTag.E6) σ η) ≤ M →
      M = fixedSubgroup (fieldActor (t := TwistTag.E6) σ η) ∨ M = ⊤

theorem SubfieldMaximalAllOdd.toAll {τ : Tag} (h : SubfieldMaximalAllOdd τ) : SubfieldMaximalAll τ :=
  fun K _ _ σ p hp hp5 hpK hσ M hRM => h K σ p hp (by omega) hpK hσ M hRM

theorem SubfieldMaximalAllOdd.toThree {τ : Tag} (h : SubfieldMaximalAllOdd τ) : SubfieldMaximalAllThree τ :=
  fun K _ _ σ p hp3 hpK hσ M hRM => h K σ p (hp3 ▸ Nat.prime_three) (by omega) hpK hσ M hRM

theorem SubfieldMaximalAllOddTwE6.toAll (h : SubfieldMaximalAllOddTwE6) : SubfieldMaximalAllTwE6 :=
  fun ℓ f hℓ hf K _ _ hK σ hσ p hp hp5 hpℓ η hη M hRM =>
    h ℓ f hℓ hf K hK σ hσ p hp (by omega) hpℓ η hη M hRM

theorem SubfieldMaximalAllOddTwE6.toThree (h : SubfieldMaximalAllOddTwE6) : SubfieldMaximalAllThreeTwE6 :=
  fun ℓ f hℓ hf K _ _ hK σ hσ p hp3 hpℓ η hη M hRM =>
    h ℓ f hℓ hf K hK σ hσ p (hp3 ▸ Nat.prime_three) (by omega) hpℓ η hη M hRM

theorem SubfieldMaximalAll.toLeOne {τ : Tag} (h : SubfieldMaximalAll τ) : SubfieldMaximalLeOne τ :=
  fun K _ _ σ p hp hp5 hpK hσ _ _ M hRM => h K σ p hp hp5 hpK hσ M hRM

theorem SubfieldMaximalAllTwE6.toLeOne (h : SubfieldMaximalAllTwE6) : SubfieldMaximalLeOneTwE6 :=
  fun ℓ f hℓ hf K _ _ hK σ hσ p hp hp5 hpℓ η hη _ _ M hRM =>
    h ℓ f hℓ hf K hK σ hσ p hp hp5 hpℓ η hη M hRM

theorem xPar_mem_subfieldGroup (τ : Tag) {K : Type} [Field K] (σ : K ≃+* K)
    (γ : Fin τ.rank → ℤ) {c : K} (hc : c ∈ fixSubfield σ) :
    xPar (rootOperatorFamily τ) γ c ∈ subfieldGroup τ σ := by
  rw [mem_fixedSubgroup, CFSG.StandardType.AutSt.entrywiseAdjointAut_xPar,
    (mem_fixSubfield σ).1 hc]

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
