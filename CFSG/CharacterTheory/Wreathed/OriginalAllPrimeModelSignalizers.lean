module

public import CFSG.CharacterTheory.Wreathed.CentralSL2Abelianization
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.Data

public noncomputable section

namespace CFSG.Wreathed.OriginalAllPrime.ModelSignalizers

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2Abelianization
open CFSG.ABGTheoremB
open scoped Pointwise

variable {F : Type} [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
  (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

@[expose] def modelX : SemilinearExtension F b m hm heven Sigma hSigma :=
  SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ m)

@[expose] def modelY : SemilinearExtension F b m hm heven Sigma hSigma :=
  SemidirectProduct.inl ((cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) *
    specialInclusion F b m hm heven (weyl F))

@[expose] def modelLayer : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma) :=
  (specialInclusion F b m hm heven).range.map SemidirectProduct.inl

@[expose] def modelBase : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma) :=
  (SemidirectProduct.inl : CentralExtension F b m hm heven →* _).range

@[expose] def modelC : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma) :=
  Subgroup.centralizer {modelY b m hm heven Sigma hSigma}

structure ModelSignalizerFacts (p q : ℕ) : Prop where
  centralizer_le : ∀ g ∈ modelC b m hm heven Sigma hSigma,
    g ∈ Subgroup.centralizer ((modelLayer b m hm heven Sigma hSigma ⊓
      modelC b m hm heven Sigma hSigma : Subgroup _) : Set _) →
    g ∈ modelBase b m hm heven Sigma hSigma
  signalizer_le : ∀ r : ℕ, r.Prime → r ≠ 2 →
    ∀ U ∈ signalizers ⊤ (modelC b m hm heven Sigma hSigma) r,
      U ≤ modelLayer b m hm heven Sigma hSigma
  layer_signalizer : ∀ r : ℕ, r.Prime → r ≠ 2 →
    ∀ X ∈ signalizers (modelLayer b m hm heven Sigma hSigma) (modelC b m hm heven Sigma hSigma) r,
      X ≠ ⊥ → q % 4 = 1 ∧ r = p
  layer_signalizer_pair : q % 4 = 1 →
    ∃ Q Qs : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma),
      Q ∈ signalizers (modelLayer b m hm heven Sigma hSigma) (modelC b m hm heven Sigma hSigma) p ∧
      Qs ∈ signalizers (modelLayer b m hm heven Sigma hSigma)
        (modelC b m hm heven Sigma hSigma) p ∧
      Nat.card Q = q ∧ Nat.card Qs = q ∧ Q ≠ Qs ∧
      modelLayer b m hm heven Sigma hSigma = Q ⊔ Qs ∧
      (∀ h : SemilinearExtension F b m hm heven Sigma hSigma,
        h * modelY b m hm heven Sigma hSigma * h⁻¹ =
          modelX b m hm heven Sigma hSigma * modelY b m hm heven Sigma hSigma →
        TotallyInverted.conjSub h Q = Qs) ∧
      (∀ X ∈ signalizers (modelLayer b m hm heven Sigma hSigma)
          (modelC b m hm heven Sigma hSigma) p, X ≤ Q ∨ X ≤ Qs) ∧
      (∀ X : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma), X ≤ Q →
        modelC b m hm heven Sigma hSigma ≤ Subgroup.normalizer (X : Set _) → X = ⊥ ∨ X = Q) ∧
      (∀ X : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma), X ≤ Qs →
        modelC b m hm heven Sigma hSigma ≤ Subgroup.normalizer (X : Set _) → X = ⊥ ∨ X = Qs)
  permutable_le : ∀ U : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma),
    Odd (Nat.card U) →
    (U : Set (SemilinearExtension F b m hm heven Sigma hSigma)) *
        (modelC b m hm heven Sigma hSigma : Set (SemilinearExtension F b m hm heven Sigma hSigma)) =
      (modelC b m hm heven Sigma hSigma : Set (SemilinearExtension F b m hm heven Sigma hSigma)) *
        (U : Set (SemilinearExtension F b m hm heven Sigma hSigma)) →
    ∃ (p' : ℕ) (X : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)), p'.Prime ∧
      X ∈ signalizers (modelLayer b m hm heven Sigma hSigma) (modelC b m hm heven Sigma hSigma) p' ∧
      U ≤ modelC b m hm heven Sigma hSigma ⊔ X

@[expose] def AllModelSignalizerFacts : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (p f : ℕ), p.Prime → Odd p → 1 ≤ f →
    Nat.card F = p ^ f → 5 < p ^ f → ∀ ε : ℤ, ε = (if p ^ f % 4 = 1 then 1 else -1) →
    ∀ (m : ℕ) (hm : 0 < m) (heven : Even m), m = 2 ^ padicValInt 2 ((p ^ f : ℕ) - ε) →
    ∀ Sigma : Subgroup (F ≃+* F), Odd (Nat.card Sigma) →
    ∀ (b : Fˣ) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b), ¬ IsSquare b →
      ModelSignalizerFacts b m hm heven Sigma hSigma p (p ^ f)

end CFSG.Wreathed.OriginalAllPrime.ModelSignalizers
