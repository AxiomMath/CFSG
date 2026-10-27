module

public import CFSG.LieType.OutStructure
public import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.Parity

public section

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms

theorem not_dvd_outer_of_mulEquiv {K L : Type} [Group K] [Finite K] [Group L] [Finite L]
    (e : K ≃* L) {p : ℕ} (h : ¬ p ∣ Nat.card (Outer L)) : ¬ p ∣ Nat.card (Outer K) := by
  rwa [CFSG.SignalizerFunctorTheorem.CatalogBridge.card_outer_eq_of_mulEquiv e]

theorem i713_of_mulEquiv_alternating {K : Type} [Group K] [Finite K] {n : ℕ} (hn : 5 ≤ n)
    (e : K ≃* alternatingGroup (Fin n)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Outer K) := by
  exact not_dvd_outer_of_mulEquiv e
    (CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn p hp hp2)

theorem i713_alternating {K : Type} [Group K] [Finite K] {n : ℕ} (hn : 5 ≤ n)
    (e : K ≃* alternatingGroup (Fin n)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (¬ p ∣ Nat.card (Outer K)) ∨
      (∃ F : Subgroup (MulAut K), (CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F).Normal ∧
        IsCyclic ↥F ∧ F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner K = ⊥ ∧
        ¬ p ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F).index ∧
        ∀ x : MulAut K, (∃ k : ℕ, x ^ (p ^ k) = 1) →
          x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F) ∨
      (p = 3 ∧ IsCyclic (Outer K) ∧ OuterPElementLifts K p) :=
  Or.inl (i713_of_mulEquiv_alternating hn e hp hp2)

end CFSG.LieType.OutStructure
