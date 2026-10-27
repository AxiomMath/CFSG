module

public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.LocalAnalysis.ComponentClassification.TBLitConfig

public noncomputable section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.UnbalancingLocal
open scoped commutatorElement MatrixGroups

@[expose] def ActsProperly {G : Type*} [Group G] (t : G) (E A B : Subgroup G) : Prop :=
  closure (insert t (E : Set G)) ≤ normalizer (A : Set G) ⊓ normalizer (B : Set G) ∧
    (∀ g ∈ closure (insert t (E : Set G)), (∀ a ∈ A, ⁅a, g⁆ ∈ B) → g ∈ E) ∧
    ∃ e ∈ E, ∃ a ∈ A, ⁅a, e⁆ ∉ B

@[expose] def IsM4 (X : Type) [Group X] : Prop :=
  IsSimpleGroup (GeneralizedFitting.subgroup X) ∧
    (∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) ∧
    OddLieType (GeneralizedFitting.subgroup X) ∧
    (∀ p f : ℕ, p.Prime → p ≠ 2 → ¬ LieModel (GeneralizedFitting.subgroup X) .PSL 2 p f) ∧
    ∃ a : X, orderOf a = 2 ∧ CFSG.oddCore (centralizer ({a} : Set X)) ≠ ⊥

@[expose] def autFixed {Q : Type*} [Group Q] (σ : MulAut Q) : Subgroup Q :=
  MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id Q)

@[expose] def ActsProperlyVia {J Q : Type*} [Group J] [Group Q] (φ : J →* MulAut Q) (t : J)
    (Y : Subgroup J) (A B : Subgroup Q) : Prop :=
  (∀ g ∈ closure (insert t (Y : Set J)),
      A.map (φ g).toMonoidHom = A ∧ B.map (φ g).toMonoidHom = B) ∧
    (∀ g ∈ closure (insert t (Y : Set J)), (∀ a ∈ A, φ g a * a⁻¹ ∈ B) →
      ∃ y ∈ Y, φ g = φ y) ∧
    ∃ y ∈ Y, ∃ a ∈ A, φ y a * a⁻¹ ∉ B

@[expose] def BurgoynePropA : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsM4 X → ∀ t : X, orderOf t = 2 →
    ∀ Y : Subgroup X, Y ≠ ⊥ → Y ≤ oddCentralizerCore t →
    ∃ u : X, orderOf u = 2 ∧ ∃ S : Subgroup X, S ≤ centralizer ({u} : Set X) ∧
      IsPComponent 2 (S.subgroupOf (centralizer ({u} : Set X))) ∧
      (∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
        Nonempty (S ≃* SL(2, GaloisField p n))) ∧
      (center S).map S.subtype = zpowers u ∧ ActsProperly t Y S ⊥

@[expose] def BurgoynePropB : Prop :=
  ∀ (J : Type) [Group J] [Finite J] (K : Subgroup J) [K.Normal],
    IsQuasisimple (K ⧸ pPrimeCore 2 K) →
    IsM4 (conjQuotAction K (centralPreimage (pPrimeCore 2 K))).range →
    ∀ (t : J) (s : MulAut (K ⧸ pPrimeCore 2 K)),
      orderOf (conjQuotAction K (pPrimeCore 2 K) t) = 2 → orderOf s = 2 →
    ∀ Y : Subgroup J, Y.map (conjQuotAction K (centralPreimage (pPrimeCore 2 K))) ≠ ⊥ →
      Y.map (conjQuotAction K (centralPreimage (pPrimeCore 2 K))).rangeRestrict ≤
        oddCentralizerCore
          ((conjQuotAction K (centralPreimage (pPrimeCore 2 K))).rangeRestrict t) →
      s * conjQuotAction K (pPrimeCore 2 K) t = conjQuotAction K (pPrimeCore 2 K) t * s →
      (∀ y ∈ Y, s * conjQuotAction K (pPrimeCore 2 K) y = conjQuotAction K (pPrimeCore 2 K) y * s) →
    ∀ Q : Subgroup (K ⧸ pPrimeCore 2 K), Q ≤ autFixed s →
      IsPComponent 2 (Q.subgroupOf (autFixed s)) →
      (∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
        Nonempty (Q ⧸ pPrimeCore 2 Q ≃* SL(2, GaloisField p n))) →
    ∀ c : K ⧸ pPrimeCore 2 K, c ∈ center (K ⧸ pPrimeCore 2 K) → c ∈ Q → orderOf c = 2 →
      ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t Y Q
        ((pPrimeCore 2 Q).map Q.subtype) →
    ∃ u : K ⧸ pPrimeCore 2 K, orderOf u = 2 ∧ ∃ S₁ S₂ : Subgroup (K ⧸ pPrimeCore 2 K),
      S₁ ≤ centralizer ({u} : Set _) ∧ IsPComponent 2 (S₁.subgroupOf (centralizer ({u} : Set _))) ∧
      S₂ ≤ centralizer ({u} : Set _) ∧ IsPComponent 2 (S₂.subgroupOf (centralizer ({u} : Set _))) ∧
      (∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
        Nonempty (S₁ ≃* SL(2, GaloisField p n)) ∧ Nonempty (S₂ ≃* SL(2, GaloisField p n))) ∧
      ⁅S₁, S₂⁆ = ⊥ ∧ S₁ ⊓ S₂ = ⊥ ∧
      (center ↥(S₁ ⊔ S₂)).map (S₁ ⊔ S₂).subtype = zpowers u ⊔ zpowers c ∧
      ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t Y S₁ ⊥ ∧
      ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t Y S₂ ⊥

@[expose] def BurgoynePropC : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsM4 X → ∀ r : X, orderOf r = 2 →
    ∀ R₁ R₂ : Subgroup X, R₁ ≤ centralizer ({r} : Set X) →
      IsPComponent 2 (R₁.subgroupOf (centralizer ({r} : Set X))) →
      R₂ ≤ centralizer ({r} : Set X) → IsPComponent 2 (R₂.subgroupOf (centralizer ({r} : Set X))) →
    ∀ (p n : ℕ) [Fact p.Prime], p ≠ 2 → 0 < n →
      Nonempty (R₁ ⧸ pPrimeCore 2 R₁ ≃* PSL(2, GaloisField p n)) →
      Nonempty (R₂ ⧸ pPrimeCore 2 R₂ ≃* SL(2, GaloisField p n)) → r ∈ R₂ →
      LieModel (GeneralizedFitting.subgroup X) .POmegaOdd 3 p n ∧
        ¬ ∃ t : X, orderOf t = 2 ∧ ∃ Y : Subgroup X, Y ≠ ⊥ ∧ Y ≤ oddCentralizerCore t ∧
          ActsProperly t Y R₁ ((pPrimeCore 2 R₁).map R₁.subtype) ∧
          ActsProperly t Y R₂ ((pPrimeCore 2 R₂).map R₂.subtype)

@[expose] def L34PumpUpExclusion : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Catalog X →
    (∃ z : X, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ α β γ : X, orderOf α = 2 → orderOf β = 2 → orderOf γ = 2 →
      α * β = β * α → α * γ = γ * α → β * γ = γ * β →
    ∀ K : Subgroup X, K ≤ centralizer ({γ} : Set X) →
      IsPComponent 2 (K.subgroupOf (centralizer ({γ} : Set X))) → γ ∈ K →
      α ∈ normalizer (K : Set X) → β ∈ normalizer (K : Set X) →
      LieModel (K ⧸ Open.fusionZStar K) .PSL 3 2 2 →
    ∀ S : Subgroup X, S ≤ K → S ≤ centralizer ({β} : Set X) ⊓ centralizer ({γ} : Set X) →
      IsPComponent 2 (S.subgroupOf (centralizer ({β} : Set X) ⊓ centralizer ({γ} : Set X))) →
      γ ∈ S →
      (∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
        Nonempty (S ⧸ pPrimeCore 2 S ≃* SL(2, GaloisField p n))) →
    ∀ E : Subgroup X, E ≤ oddCentralizerCore α →
      E ≤ centralizer ({β} : Set X) ⊓ centralizer ({γ} : Set X) →
      ¬ ActsProperly α E S ((pPrimeCore 2 S).map S.subtype)

@[expose] def HeldTrivialMultiplier : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsQuasisimple Q →
    Nonempty (Q ⧸ center Q ≃* NativeSporadic.He) → center Q = ⊥

@[expose] def GriessMultipliersAllModels : Prop :=
  CFSG.Open.GriessAllModelsStatement

@[expose] def GriessMultipliersCentralCovers : Prop :=
  type_of% @Milestones.cl_lit_griess_schur_multipliers_central_covers

@[expose] def SolomonSignalizerInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ (b : X) (n : ℕ) (K : Subgroup X), orderOf b = 2 → Odd n → 7 ≤ n →
      K ≤ centralizer ({b} : Set X) → IsPComponent 2 (K.subgroupOf (centralizer ({b} : Set X))) →
      Nonempty (K ⧸ Open.fusionZStar K ≃* alternatingGroup (Fin n)) →
      Open.fusionZStar K = pPrimeCore 2 K

end CFSG.ComponentClassification.TBLit
