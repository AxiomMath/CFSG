module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClHYc
public import CFSG.HardMathSupport.RichardWeiss.Proving.CaseI

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin CFSG.RankThree.PartTwo
  CFSG.QuasithinUnique
open CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
open CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0
open scoped commutatorElement

@[expose] def CaseIOf {G : Type} [Group G] [Finite G] (S L : Subgroup G) : Prop :=
  S ⊓ Subgroup.centralizer ((⁅S, S⁆ : Subgroup G) : Set G) ≤ pCoreOf 2 (L ⊔ S) ∧
    ⁅L, pCoreOf 2 (L ⊔ S)⁆ ≤ Subgroup.centralizer ((⁅S, S⁆ : Subgroup G) : Set G)

@[expose] def E0NonShortNotCaseIStatement : Prop :=
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
    ¬ HYc S L → ¬ ⁅pCoreOf 2 (L ⊔ S), L⁆ ≤ blockV S L → ¬ CaseIOf S L → False

theorem false_of_caseIOf {G : Type} [Group G] [Finite G] {X S L : Subgroup G}
    (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hc : CaseIOf S L) : False := by
  have hMQ : L ⊔ S ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ S) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (L ⊔ S)
  exact CFSG.HardMathSupport.RichardWeiss.Proving.false_of_caseI hA
    hL.toIsTwoPrimeComponent.le hL.not_le_normalizer
    (CFSG.HardMathSupport.Cooperstein.Coordinator.twoCore_sup_le hA hL hSL)
    (fun l hl q hq => (Subgroup.mem_normalizer_iff.1 (hMQ ((le_sup_left : L ≤ L ⊔ S) hl)) q).1 hq)
    hc.1 hc.2

theorem e0NonShortNotHYcStatement_of_caseI (h : E0NonShortNotCaseIStatement) :
    E0NonShortNotHYcStatement := by
  intro G _ _ X S L hA hL hSL N hN θ hNS hθS hEO hJ Δ₀ hΔ₀ P hPc hPsq hPfix hPtrans ω hωω hωΔ
    hωfree hθ hyc hshort
  by_cases hc : CaseIOf S L
  · exact (false_of_caseIOf hA hL hSL hc).elim
  · exact h G X S L hA hL hSL N hN θ hNS hθS hEO hJ Δ₀ hΔ₀ P hPc hPsq hPfix hPtrans ω hωω hωΔ
      hωfree hθ hyc hshort hc

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
