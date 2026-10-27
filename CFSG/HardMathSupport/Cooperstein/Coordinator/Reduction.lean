module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Parts
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Setting
public import CFSG.HardMathSupport.Cooperstein.Proving.NineThreeTransferNat
public import CFSG.HardMathSupport.Cooperstein.Proving.NineThreeTransfer
public import CFSG.HardMathSupport.Cooperstein.Proving.PCoreSup

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19 CFSG.Open
open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock IsTwoPrimeComponent barM InClassXBlock NineThreeTwo
  NineThreeThree NineThreeFour NineThreeFive NineThreeEight IsClassicalTwoOrG2)
open CFSG.HardMathSupport.Cooperstein.Proving (barMEquiv quotCenterEquiv)

@[expose] def Asc81bNineThreeChevLS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S L : Subgroup G), CFSG.Open.IsKGroup ↥(L ⊔ S) →
    Asc81bHyp (L ⊔ S) S → IsWeakSBlock (L ⊔ S) S L → S ≤ Subgroup.normalizer (L : Set G) →
    IsClassicalTwoOrG2 (↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L)) →
      InClassXBlock L ∨ NineThreeTwo (L ⊔ S) S L ∨
        (NineThreeThree (L ⊔ S) S L ∧ IsTypeScriptL L) ∨
        (NineThreeFour (L ⊔ S) S L ∧ IsA6Z3Type L)

@[expose] def Asc81bNineThreeAltLS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L → S ≤ Subgroup.normalizer (L : Set G) →
    ∀ m : ℕ, (m = 7 ∨ 8 < m) →
    Nonempty (↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃*
      alternatingGroup (Fin m)) →
      InClassXBlock L ∨ (NineThreeFive (L ⊔ S) L ∧ IsA7FourType L) ∨
        NineThreeSixNat (L ⊔ S) S L ∨ NineThreeSevenNat (L ⊔ S) S L ∨
        (NineThreeEight X S L ∧ IsTypeScriptL L)

section Reduction

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

theorem inf_pCoreOf_eq_inf_pCoreOf_sup (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) :
    L ⊓ pCoreOf 2 X = L ⊓ pCoreOf 2 (L ⊔ S) := by
  rw [hL.toIsTwoPrimeComponent.inf_twoCore,
    Proving.inf_pCoreOf_sup hL.toIsTwoPrimeComponent hA.twoRadical.1 hA.twoRadical.isPGroup hSL]

noncomputable def barMSupCenterEquiv (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) :
    ↥(barM X L) ⧸ Subgroup.center ↥(barM X L) ≃*
      ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) :=
  quotCenterEquiv (barMEquiv hL.le le_sup_left (inf_pCoreOf_eq_inf_pCoreOf_sup hA hL hSL))

end Reduction

theorem asc81bNineThreeAlt_of_LS (h : Asc81bNineThreeAltLS) : Asc81bNineThreeAlt := by
  intro G _ _ X S L hX hA hL m hm ⟨e⟩
  have hSL := le_normalizer_of_isWeakSBlock hX hA hL
  have hYX : L ⊔ S ≤ X := sup_le hL.le hA.twoRadical.1
  have hcore := inf_pCoreOf_eq_inf_pCoreOf_sup hA hL hSL
  rcases h G X S L hX hA hL hSL m hm ⟨(barMSupCenterEquiv hA hL hSL).symm.trans e⟩ with
    h1 | ⟨h5, h5'⟩ | h6 | h7 | h8
  · exact Or.inl h1
  · exact Or.inr (Or.inl ⟨Proving.nineThreeFive_of_le hYX le_sup_left hcore h5, h5'⟩)
  · exact Or.inr (Or.inr (Or.inl (Proving.nineThreeSixNat_of_le hYX le_sup_left hcore h6)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Proving.nineThreeSevenNat_of_le hYX le_sup_left hcore h7))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h8)))

end CFSG.HardMathSupport.Cooperstein.Coordinator
