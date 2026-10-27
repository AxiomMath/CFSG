module

public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitInputs
public import CFSG.RankThree.PerfectCover.HopfCover
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerSemidihedralTwoComponents

public section

namespace CFSG.ComponentClassification.SolAltLit

open CFSG Subgroup
open scoped Pointwise

@[expose] def thetaFunctor {X : Type*} [Group X] (E : Subgroup X) (b : X) : Subgroup X :=
  ⁅(pPrimeCore 2 (centralizer ({b} : Set X))).map (centralizer ({b} : Set X)).subtype, E⁆ ⊔
    ((pPrimeCore 2 (centralizer ({b} : Set X))).map (centralizer ({b} : Set X)).subtype ⊓
      (pPrimeCore 2 (centralizer (E : Set X))).map (centralizer (E : Set X)).subtype)

@[expose] def MaximalAltComponentInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ (t : X) (J : Subgroup X) (n : ℕ), IsAltTwoComponent t J n → Odd n → 9 ≤ n →
      (∀ (t' : X) (K' : Subgroup X) (n' : ℕ), IsAltTwoComponent t' K' n' → Odd n' → n' ≤ n) →
      (∀ g : X, ⁅J, conjugate J g⁆ ≠ ⊥) ∧
      ∀ y : X, orderOf y = 2 → J ≤ centralizer ({y} : Set X) →
        centralizer ({y} : Set X) ≤ normalizer
          ((((pPrimeCore 2 (centralizer ({y} : Set X))).map
            (centralizer ({y} : Set X)).subtype ⊔ J : Subgroup X)) : Set X)

@[expose] def SignalizerTrivialityInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ (t₀ : X) (K₀ : Subgroup X) (m : ℕ), IsAltTwoComponent t₀ K₀ m → Odd m → 9 ≤ m →
    ∃ (t : X) (J : Subgroup X) (n : ℕ), IsAltTwoComponent t J n ∧ Odd n ∧ 9 ≤ n ∧
      (∀ (t' : X) (K' : Subgroup X) (n' : ℕ), IsAltTwoComponent t' K' n' → Odd n' → n' ≤ n) ∧
      ∃ (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X), E ≤ J ∧
        Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
        (∃ D : Finset (Fin n), D.card = 4 ∧ ∀ x : J, (x : X) ∈ E → ∀ ω ∉ D,
          ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ω =
            ω) ∧
        ∀ y : X, orderOf y = 2 → y ∈ centralizer (E : Set X) →
          y ∈ UnbalancedLayer.coreActionKernel J → y ∉ J →
          ∀ b ∈ E ⊔ zpowers y, b ≠ 1 → thetaFunctor E b = ⊥

@[expose] def SchurAlternatingMultiplierInput : Prop :=
  ∀ m : ℕ, 5 ≤ m →
    IsCyclic (RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin m))) ∧
      Nat.card (RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin m))) =
        if m = 6 ∨ m = 7 then 6 else 2

end CFSG.ComponentClassification.SolAltLit
