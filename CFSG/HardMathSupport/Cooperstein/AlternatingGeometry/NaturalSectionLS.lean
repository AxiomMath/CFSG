module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderGlue
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenNode

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19 CFSG.QuasithinUnique
open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock barM InClassXBlock NineThreeFive blockV)

variable {G : Type} [Group G]

@[expose] def NaturalSectionLS (S L : Subgroup G) (d : ℕ) : Prop :=
  ∃ (π : ↥⁅blockV S L, L⁆ →* Multiplicative (altHeart d)) (θ : ↥(L ⊔ S) →* Equiv.Perm (Fin d)),
    Function.Surjective π ∧
    π.ker = (⁅blockV S L, L⁆ ⊓ Subgroup.centralizer ((L ⊔ S : Subgroup G) : Set G)).subgroupOf
      ⁅blockV S L, L⁆ ∧
    (∀ σ ∈ alternatingGroup (Fin d), ∃ l : ↥L, θ ⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩ = σ) ∧
    SectionEquiv ⁅blockV S L, L⁆ (L ⊔ S) π θ ∧
    ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ Subgroup.centralizer (blockV S L : Set G)

@[expose] def NaturalSectionLSL (S L : Subgroup G) (d : ℕ) : Prop :=
  ∃ (π : ↥⁅blockV S L, L⁆ →* Multiplicative (altHeart d)) (θ : ↥(L ⊔ S) →* Equiv.Perm (Fin d)),
    Function.Surjective π ∧
    π.ker = (⁅blockV S L, L⁆ ⊓ Subgroup.centralizer (L : Set G)).subgroupOf ⁅blockV S L, L⁆ ∧
    (∀ σ ∈ alternatingGroup (Fin d), ∃ l : ↥L, θ ⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩ = σ) ∧
    SectionEquiv ⁅blockV S L, L⁆ (L ⊔ S) π θ ∧
    ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ Subgroup.centralizer (blockV S L : Set G)

@[expose] def GF2NaturalLS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L → S ≤ Subgroup.normalizer (L : Set G) →
    ∀ m : ℕ, (m = 7 ∨ 8 < m) →
    Nonempty (↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin m)) →
      NaturalSectionLS S L m ∨ (m = 7 ∧ Nat.card ↥⁅blockV S L, L⁆ = 2 ^ 4)

@[expose] def GF2NaturalLSL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L → S ≤ Subgroup.normalizer (L : Set G) →
    ∀ m : ℕ, (m = 7 ∨ 8 < m) →
    Nonempty (↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin m)) →
      NaturalSectionLSL S L m ∨ (m = 7 ∧ Nat.card ↥⁅blockV S L, L⁆ = 2 ^ 4)

theorem NaturalSectionLSL.naturalSectionL {S L : Subgroup G} {d : ℕ} (h : NaturalSectionLSL S L d) :
    NaturalSectionL S L d := by
  obtain ⟨π, θ, hπ, hker, hA, hequiv, -⟩ := h
  refine ⟨π, θ.comp (Subgroup.inclusion le_sup_left), hπ, hker, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨l, hl⟩ := hA σ hσ
    exact ⟨l, hl⟩
  · intro l t t' ht' x hx
    exact hequiv ⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩ t t' ht' x hx

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
