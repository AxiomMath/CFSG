module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.HYprime

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0

open CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
  Equiv Equiv.Perm

@[expose] def HYp {G : Type} [Group G] (S L : Subgroup G) : Prop :=
  ∀ y ∈ ⁅S, S⁆ ⊔ Subgroup.closure {s ^ 2 | s ∈ S}, y ^ 2 = 1 →
    ∃ v ∈ blockV S L, ∃ c ∈ pCoreOf 2 (L ⊔ S) ⊓ Subgroup.centralizer (L : Set G), y = v * c

theorem false_of_E0_HYp' {G : Type} [Group G] [Finite G] {X S L : Subgroup G} (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) (hSL : S ≤ Subgroup.normalizer (L : Set G)) {N : ℕ} (hN : 10 ≤ N)
    {θ : ↥(L ⊔ S) →* Perm (Fin N)} (hNS : NaturalSectionTheta S L N θ)
    (hθS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S)
    {Δ₀ : Finset (Fin N)} (hΔ₀ : Δ₀.card = 4) {P : Subgroup (Perm (Fin N))}
    (hPc : Nat.card P = 4) (hPsq : ∀ p ∈ P, p * p = 1)
    (hPfix : ∀ p ∈ P, ∀ i, i ∉ Δ₀ → p i = i) (hPtrans : ∀ i ∈ Δ₀, ∀ j ∈ Δ₀, ∃ p ∈ P, p i = j)
    {ω : Perm (Fin N)} (hωω : ∀ x, ω (ω x) = x) (hωΔ : ∀ x ∈ Δ₀, ω x = x)
    (hωfree : ∀ x, x ∉ Δ₀ → ω x ≠ x)
    (hθ : (S.subgroupOf (L ⊔ S)).map θ =
      P ⊔ Subgroup.closure {τ | ∃ x, x ∉ Δ₀ ∧ τ = swap x (ω x)})
    (hJ : (S.subgroupOf (L ⊔ S)).map θ ≤ ((thompsonJ S).subgroupOf (L ⊔ S)).map θ)
    (hY : HYp S L) : False := by
  refine false_of_E0_HYp hA hL hSL hN hNS hθS
    ⟨hΔ₀, hPsq, hPfix, hPc, hPtrans, hωω, hωΔ, hωfree⟩ hθ hJ ?_
  intro y hy hy2
  refine hY y ?_ hy2
  simpa [Phi, eq_comm] using hy

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0
