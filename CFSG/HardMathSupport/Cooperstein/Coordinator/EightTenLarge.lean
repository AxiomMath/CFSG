module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFour
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTwoExcluded
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenSplit

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19 CFSG.QuasithinUnique
open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock)

@[expose] def EightTwoFourExcludedLarge : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L → S ≤ Subgroup.normalizer (L : Set G) →
    ∀ N r : ℕ, (r = 2 ∨ r = 4) → 6 ≤ N - 2 * r →
      ¬ (AlternatingGeometry.EightBlockData X S L r (N - 2 * r) ∧ IsShort2 L ∧ IsTypeScriptL L)

theorem eightTwoFourExcludedLarge_of (h2 : AlternatingGeometry.EightTwoExcluded)
    (hnat : AlternatingGeometry.GF2NaturalLSL) : EightTwoFourExcludedLarge := by
  intro G _ _ X S L hX hA hL hSL N r hr hs h
  rcases hr with rfl | rfl
  · exact h2 G X S L hX hA hL hSL N h
  · exact eightFourExcluded_large hnat G X S L hX hA hL hSL N hs h

theorem asc81bEightTen_of_printed_large (hP : AlternatingGeometry.Asc81bEightTenPrinted)
    (h4 : AlternatingGeometry.QuadFourExcluded) (h24 : EightTwoFourExcludedLarge) :
    AlternatingGeometry.Asc81bEightTen := by
  intro G _ _ X S L hX hA hL hSL m hm he
  rcases hP G X S L hX hA hL hSL m hm he with
    h1 | h5 | h6 | ⟨n, hn, hd, hnat⟩ | ⟨N, r, hN, hr2, hr1, hs, hD, hsh, hT⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h5)
  · exact Or.inr (Or.inr (Or.inl h6))
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨n, ?_, hd.toQuadBlockData, hnat⟩)))
    by_contra hn'
    have h : n = 4 := by omega
    subst h
    exact h4 G X S L hX hA hL hSL ⟨hd, hnat⟩
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨N, r, hN, hr2, hr1, ?_, hs, hD, hsh, hT⟩)))
    by_contra hr'
    have h : r = 2 ∨ r = 4 := by omega
    exact h24 G X S L hX hA hL hSL N r h hs ⟨hD, hsh, hT⟩

end CFSG.HardMathSupport.Cooperstein.Coordinator
