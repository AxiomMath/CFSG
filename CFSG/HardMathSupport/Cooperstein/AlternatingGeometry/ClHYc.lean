module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClHYz
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.StatementHYc

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin CFSG.RankThree.PartTwo
  CFSG.QuasithinUnique
open CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
open CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0
open scoped commutatorElement

@[expose] def E0NonShortNotHYcStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Asc81bHyp X S → IsWeakSBlock X S L →
    S ≤ Subgroup.normalizer (L : Set G) → ∀ N : ℕ, 10 ≤ N →
    ∀ θ : ↥(L ⊔ S) →* Perm (Fin N), NaturalSectionTheta S L N θ →
    (∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S) → EOffenderData S (blockV S L) →
    (S.subgroupOf (L ⊔ S)).map θ ≤ ((thompsonJ S).subgroupOf (L ⊔ S)).map θ →
    ∀ Δ₀ : Finset (Fin N), Δ₀.card = 4 →
    ∀ P : Subgroup (Perm (Fin N)), Nat.card P = 4 → (∀ p ∈ P, p * p = 1) →
    (∀ p ∈ P, ∀ i, i ∉ Δ₀ → p i = i) → (∀ i ∈ Δ₀, ∀ j ∈ Δ₀, ∃ p ∈ P, p i = j) →
    ∀ ω : Perm (Fin N), (∀ x, ω (ω x) = x) → (∀ x ∈ Δ₀, ω x = x) → (∀ x, x ∉ Δ₀ → ω x ≠ x) →
    (S.subgroupOf (L ⊔ S)).map θ = P ⊔ Subgroup.closure {τ | ∃ x, x ∉ Δ₀ ∧ τ = swap x (ω x)} →
    ¬ HYc S L → ¬ ⁅pCoreOf 2 (L ⊔ S), L⁆ ≤ blockV S L → False

theorem e0NonShortNotHYzStatement_of_hyc (h : E0NonShortNotHYcStatement) :
    E0NonShortNotHYzStatement := by
  intro G _ _ X S L hA hL hSL N hN θ hNS hθS hEO hJ Δ₀ hΔ₀ P hPc hPsq hPfix hPtrans ω hωω hωΔ
    hωfree hθ _hyz hshort
  by_cases hyc : HYc S L
  · exact false_of_E0_HYc' hA hL hSL hN hNS hθS hΔ₀ hPc hPsq hPfix hPtrans hωω hωΔ hωfree hθ hyc
  · exact h G X S L hA hL hSL N hN θ hNS hθS hEO hJ Δ₀ hΔ₀ P hPc hPsq hPfix hPtrans ω hωω hωΔ
      hωfree hθ hyc hshort

theorem eightTenResidualOutcomes_of_E0_hyc (h : E0NonShortNotHYcStatement) :
    EightTenResidualOutcomes :=
  eightTenResidualOutcomes_of_E0_hyz (e0NonShortNotHYzStatement_of_hyc h)

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
