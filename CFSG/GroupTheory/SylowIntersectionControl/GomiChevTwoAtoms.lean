module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevOrbitSwapDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwoPar
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevAtomTransport
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwoMap

public section

namespace CFSG.GroupTheory

open CFSG.ABGLocalTools CFSG.QuasithinUnique Subgroup
open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar (TwoPar)

variable {K : Type} [Group K] [Finite K]

private lemma twoPar_eq_or_eq_of_covBy {S : Type} [Group S] {T P₁ P₂ A : Subgroup S}
    (h : TwoPar S T P₁ P₂) (hcov : Subgroup.normalizer (T : Set S) ⋖ A) :
    A = P₁ ∨ A = P₂ := by
  rcases h.hover A hcov.le with e | e | e | e
  · exact absurd e hcov.ne'
  · exact Or.inl e
  · exact Or.inr e
  · exfalso
    subst e
    exact hcov.2 h.lt₁ h.top₁.lt_top

theorem gomiAtomOrbitTop_of_twoPar {Y₀ : Type} [Group Y₀] [Finite Y₀] (e : K ≃* Y₀)
    {T₀ P₁ P₂ : Subgroup Y₀} (h : TwoPar Y₀ T₀ P₁ P₂) : GomiAtomOrbitTop K := by
  intro S A 𝒜 hS _ hfix hA α₁ hα₁ α₂ hα₂
  have hS' : IsSylowTwoOf S ⊤ := (Setup.X6.isSylowTwoOf_iff_isSylowOf).2 hS
  obtain ⟨P₁', P₂', h'⟩ := h.exists_of_equiv e.symm hS'
  have key : ∀ X : Subgroup K, IsGomiAtom ⊤ S X → X = P₁' ∨ X = P₂' := fun X hX =>
    twoPar_eq_or_eq_of_covBy h' ((isGomiAtom_top_iff_covBy S X).1 hX)
  have hA' : A = P₁' ∨ A = P₂' := key A hA
  have hA₁ : A.map α₁.toMonoidHom = P₁' ∨ A.map α₁.toMonoidHom = P₂' := by
    apply key
    rw [← hfix α₁ hα₁]
    exact (isGomiAtom_top_map_mulEquiv_iff α₁ S A).2 hA
  have hA₂ : A.map α₂.toMonoidHom = P₁' ∨ A.map α₂.toMonoidHom = P₂' := by
    apply key
    rw [← hfix α₂ hα₂]
    exact (isGomiAtom_top_map_mulEquiv_iff α₂ S A).2 hA
  rcases hA' with hA' | hA' <;> rcases hA₁ with h₁ | h₁ <;> rcases hA₂ with h₂ | h₂ <;>
    simp_all

theorem gomiAtomsFixed_of_twoPar_card_ne {Y₀ : Type} [Group Y₀] [Finite Y₀] (e : K ≃* Y₀)
    {T₀ P₁ P₂ : Subgroup Y₀} (h : TwoPar Y₀ T₀ P₁ P₂) (hc : Nat.card P₁ ≠ Nat.card P₂) :
    GomiAtomsFixed K := by
  have h' : TwoPar K (T₀.map e.symm.toMonoidHom) (P₁.map e.symm.toMonoidHom)
      (P₂.map e.symm.toMonoidHom) := h.map e.symm
  refine gomiAtomsFixed_of_isSylowOf (Setup.X6.isSylowTwoOf_iff_isSylowOf.1 h'.sylow) ?_
  intro A α hα hA
  have hcard : Nat.card (P₁.map e.symm.toMonoidHom) ≠ Nat.card (P₂.map e.symm.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective e.symm.injective,
      Subgroup.card_map_of_injective e.symm.injective]
    exact hc
  have key : ∀ X : Subgroup K, IsGomiAtom ⊤ (T₀.map e.symm.toMonoidHom) X →
      X = P₁.map e.symm.toMonoidHom ∨ X = P₂.map e.symm.toMonoidHom := fun X hX =>
    twoPar_eq_or_eq_of_covBy h'
      ((isGomiAtom_top_iff_covBy (T₀.map e.symm.toMonoidHom) X).1 hX)
  have hA' : A = P₁.map e.symm.toMonoidHom ∨ A = P₂.map e.symm.toMonoidHom := key A hA
  have hAα : A.map α.toMonoidHom = P₁.map e.symm.toMonoidHom ∨
      A.map α.toMonoidHom = P₂.map e.symm.toMonoidHom := by
    apply key
    rw [← hα]
    exact (isGomiAtom_top_map_mulEquiv_iff α (T₀.map e.symm.toMonoidHom) A).2 hA
  have hcardα : Nat.card (A.map α.toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective α.injective
  rcases hA' with hA' | hA'
  · rcases hAα with h | h
    · exact h.trans hA'.symm
    · exfalso
      exact hcard (by rw [← hA', ← h, hcardα])
  · rcases hAα with h | h
    · exfalso
      exact hcard (by rw [← h, hcardα, hA'])
    · exact h.trans hA'.symm

theorem gomiAtomsFixed_of_covBy_imp {ι : Type*} {T : Subgroup K} {P : ι → Subgroup K}
    (hT : IsSylowTwoOf T ⊤) (hcov : ∀ A : Subgroup K, normalizer (T : Set K) ⋖ A → ∃ i, A = P i)
    (hinv : ∀ (α : MulAut K) (i : ι), T.map α.toMonoidHom = T →
      (P i).map α.toMonoidHom = P i) : GomiAtomsFixed K := by
  refine gomiAtomsFixed_of_isSylowOf (Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hT) fun A α hα hA => ?_
  obtain ⟨i, rfl⟩ := hcov A ((isGomiAtom_top_iff_covBy T A).1 hA)
  exact hinv α i hα

theorem gomiAtomsFixed_of_covBy_relIndex_ne {T P₁ P₂ : Subgroup K} (hT : IsSylowTwoOf T ⊤)
    (hcov : ∀ A : Subgroup K, normalizer (T : Set K) ⋖ A ↔ A = P₁ ∨ A = P₂)
    (hidx : (normalizer (T : Set K)).relIndex P₁ ≠ (normalizer (T : Set K)).relIndex P₂) :
    GomiAtomsFixed K := by
  refine gomiAtomsFixed_of_isSylowOf (Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hT) ?_
  intro A α hα hA
  have hN : (normalizer (T : Set K)).map α.toMonoidHom = normalizer (T : Set K) := by
    rw [Subgroup.map_equiv_normalizer_eq T α, hα]
  have hcovA : normalizer (T : Set K) ⋖ A := (isGomiAtom_top_iff_covBy T A).1 hA
  have hcovAα : normalizer (T : Set K) ⋖ A.map α.toMonoidHom := by
    have h1 := (apply_covBy_apply_iff (MulEquiv.mapSubgroup α)).2 hcovA
    change Subgroup.map α.toMonoidHom (normalizer (T : Set K)) ⋖
      Subgroup.map α.toMonoidHom A at h1
    rwa [hN] at h1
  have hA' : A = P₁ ∨ A = P₂ := (hcov A).1 hcovA
  have hAα' : A.map α.toMonoidHom = P₁ ∨ A.map α.toMonoidHom = P₂ :=
    (hcov (A.map α.toMonoidHom)).1 hcovAα
  have hidx' : (normalizer (T : Set K)).relIndex (A.map α.toMonoidHom) =
      (normalizer (T : Set K)).relIndex A := by
    have h1 := Subgroup.relIndex_map_map_of_injective (f := α.toMonoidHom)
      (Subgroup.normalizer (T : Set K)) A α.injective
    rwa [hN] at h1
  rcases hA' with rfl | rfl
  · rcases hAα' with h | h
    · exact h
    · exfalso; rw [h] at hidx'; exact hidx hidx'.symm
  · rcases hAα' with h | h
    · exfalso; rw [h] at hidx'; exact hidx hidx'
    · exact h

theorem gomiAtomsFixed_of_isCoatom_normalizer
    (h : ∀ T : Subgroup K, IsSylowTwoOf T ⊤ → IsCoatom (normalizer (T : Set K))) :
    GomiAtomsFixed K := by
  intro S A α hS _ hA
  have hS' : IsSylowTwoOf S ⊤ := (Setup.X6.isSylowTwoOf_iff_isSylowOf).2 hS
  have htop : A = ⊤ := (h S hS').lt_iff.1 ((isGomiAtom_top_iff_covBy S A).1 hA).lt
  subst htop
  exact Subgroup.map_top_of_surjective α.toMonoidHom α.surjective

end CFSG.GroupTheory
