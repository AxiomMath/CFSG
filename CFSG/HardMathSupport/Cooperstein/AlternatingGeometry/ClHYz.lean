module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClHYt
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.StatementHYz

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin CFSG.RankThree.PartTwo
  CFSG.QuasithinUnique
open CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
open CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0
open scoped commutatorElement

@[expose] def E0NonShortNotHYzStatement : Prop :=
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
    ¬ HYz S L → ¬ ⁅pCoreOf 2 (L ⊔ S), L⁆ ≤ blockV S L → False

theorem e0NonShortNotHYtStatement_of_hyz (h : E0NonShortNotHYzStatement) :
    E0NonShortNotHYtStatement := by
  intro G _ _ X S L hA hL hSL N hN θ hNS hθS hEO hJ Δ₀ hΔ₀ P hPc hPsq hPfix hPtrans ω hωω hωΔ
    hωfree hθ _hyt hshort
  by_cases hyz : HYz S L
  · exact false_of_E0_HYz' hA hL hSL hN hNS hθS hΔ₀ hPc hPsq hPfix hPtrans hωω hωΔ hωfree hθ hyz
  · exact h G X S L hA hL hSL N hN θ hNS hθS hEO hJ Δ₀ hΔ₀ P hPc hPsq hPfix hPtrans ω hωω hωΔ
      hωfree hθ hyz hshort


theorem eightTenNodeFourOrbit_of_E0_hyz (h : E0NonShortNotHYzStatement) :
    EightTenNodeFourOrbit :=
  eightTenNodeFourOrbit_of_E0_hyt (e0NonShortNotHYtStatement_of_hyz h)

theorem eightTenNodeColourFour_of_E0_hyz (h : E0NonShortNotHYzStatement) :
    EightTenNodeColourFour :=
  eightTenNodeColourFour_of_E0_hyt (e0NonShortNotHYtStatement_of_hyz h)

theorem eightTenResidualOutcomes_of_E0_hyz (h : E0NonShortNotHYzStatement) :
    EightTenResidualOutcomes :=
  eightTenResidualOutcomes_of_E0_hyt (e0NonShortNotHYtStatement_of_hyz h)

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
