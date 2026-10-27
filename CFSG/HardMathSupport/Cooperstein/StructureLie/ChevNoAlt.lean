module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Parts
public import CFSG.HardMathSupport.Cooperstein.StructureLie.Transvection
public import CFSG.HardMathSupport.Cooperstein.StructureLie.TransvectionIrreducible

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19
open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock barM InClassXBlock NineThreeTwo NineThreeThree
  NineThreeFour NineThreeFive NineThreeEight IsClassicalTwoOrG2)
open CFSG.HardMathSupport.Cooperstein.Coordinator (Asc81bNineTwo Asc81bNineThreeAlt)

@[expose] def Asc81bNineThreeChevNoAlt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L →
    IsClassicalTwoOrG2 (↥(barM X L) ⧸ Subgroup.center ↥(barM X L)) →
    (∀ m : ℕ, (m = 7 ∨ 9 ≤ m) →
      IsEmpty (↥(barM X L) ⧸ Subgroup.center ↥(barM X L) ≃* alternatingGroup (Fin m))) →
      InClassXBlock L ∨ NineThreeTwo X S L ∨ (NineThreeThree X S L ∧ IsTypeScriptL L) ∨
        (NineThreeFour X S L ∧ IsA6Z3Type L)

theorem asc81bNineThreeNat_of_parts_noAlt (h92 : Asc81bNineTwo)
    (hC : Asc81bNineThreeChevNoAlt) (hA : Asc81bNineThreeAlt) : Asc81bNineThreeNat := by
  intro G _ _ X S L hX hhyp hL
  have hfromAlt : ∀ m : ℕ, (m = 7 ∨ 8 < m) →
      Nonempty (↥(barM X L) ⧸ Subgroup.center ↥(barM X L) ≃* alternatingGroup (Fin m)) →
      InClassXBlock L ∨ NineThreeTwo X S L ∨ (NineThreeThree X S L ∧ IsTypeScriptL L) ∨
        (NineThreeFour X S L ∧ IsA6Z3Type L) ∨ (NineThreeFive X L ∧ IsA7FourType L) ∨
        NineThreeSixNat X S L ∨ NineThreeSevenNat X S L ∨
          (NineThreeEight X S L ∧ IsTypeScriptL L) := by
    intro m hm he
    rcases hA G X S L hX hhyp hL m hm he with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
  have hChev : IsClassicalTwoOrG2 (↥(barM X L) ⧸ Subgroup.center ↥(barM X L)) →
      (∀ m : ℕ, (m = 7 ∨ 9 ≤ m) →
        IsEmpty (↥(barM X L) ⧸ Subgroup.center ↥(barM X L) ≃* alternatingGroup (Fin m))) →
      InClassXBlock L ∨ NineThreeTwo X S L ∨ (NineThreeThree X S L ∧ IsTypeScriptL L) ∨
        (NineThreeFour X S L ∧ IsA6Z3Type L) ∨ (NineThreeFive X L ∧ IsA7FourType L) ∨
        NineThreeSixNat X S L ∨ NineThreeSevenNat X S L ∨
          (NineThreeEight X S L ∧ IsTypeScriptL L) := by
    intro hc hAlt
    rcases hC G X S L hX hhyp hL hc hAlt with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  by_cases hbig : ∃ m : ℕ, (m = 7 ∨ 9 ≤ m) ∧
      Nonempty (↥(barM X L) ⧸ Subgroup.center ↥(barM X L) ≃* alternatingGroup (Fin m))
  · obtain ⟨m, hm, he⟩ := hbig
    exact hfromAlt m (by omega) he
  · have hAlt : ∀ m : ℕ, (m = 7 ∨ 9 ≤ m) →
        IsEmpty (↥(barM X L) ⧸ Subgroup.center ↥(barM X L) ≃* alternatingGroup (Fin m)) := by
      intro m hm
      exact ⟨fun e => hbig ⟨m, hm, ⟨e⟩⟩⟩
    rcases h92 G X S L hX hhyp hL with hc | ⟨m, hm5, ⟨he⟩⟩
    · exact hChev hc hAlt
    · by_cases hm : m = 5 ∨ m = 6 ∨ m = 8
      · exact hChev (Or.inr (Or.inl ⟨m, hm, ⟨he⟩⟩)) hAlt
      · exact hfromAlt m (by omega) ⟨he⟩

@[expose] def EightEightShapeNoAlt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L →
    IsClassicalTwoOrG2 (↥(barM X L) ⧸ Subgroup.center ↥(barM X L)) →
    (∀ m : ℕ, (m = 7 ∨ 9 ≤ m) →
      IsEmpty (↥(barM X L) ⧸ Subgroup.center ↥(barM X L) ≃* alternatingGroup (Fin m))) →
      TransvectionData S L → OrthOrTripleA6 X L

theorem chevNoAlt_of_nodes (h89 : EightNine)
    (hshape : EightEightShapeNoAlt) (h883 : EightEightShort) : Asc81bNineThreeChevNoAlt := by
  intro G _ _ X S L hX hA hL hc hAlt
  rcases h89 G X S L hX hA hL hc with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · have ht := eightEightTransvection G X S L hX hA hL hc h
    have ho := hshape G X S L hX hA hL hc hAlt ht
    have hirr := hasIrreducibleCommutatorQuotient_of_transvectionData hX hA hL ht
    obtain ⟨hs1, hs2⟩ := h883 G X S L hX hA hL hc ht hirr
    rcases ho with ho | ho
    · obtain ⟨hsh, hT⟩ := hs1 ho
      obtain ⟨s, hsS, h1, h2, h3⟩ := ht
      exact Or.inr (Or.inr (Or.inl ⟨⟨hsh, ho, hirr, s, hsS, h1, h2, h3⟩, hT⟩))
    · exact Or.inr (Or.inr (Or.inr (hs2 ho)))

end CFSG.HardMathSupport.Cooperstein.StructureLie
