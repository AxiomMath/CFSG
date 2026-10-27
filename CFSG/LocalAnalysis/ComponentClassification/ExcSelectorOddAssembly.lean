module

public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddTriality
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

public noncomputable section

namespace CFSG.ComponentClassification.ExcSelector

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank

theorem noSmallComponent_of_model_odd {W : Type} [Group W] {t : StatedLieTag} {p f : ℕ}
    (hp2 : p ≠ 2) (hW : ChevalleyExceptionalModel W t p f) : NoSmallComponent W := by
  obtain ⟨⟨hp, hf, -⟩, hm⟩ := hW
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  cases t
  case G2 =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hm
    rw [← hK] at hodd
    exact noSmallComponent_of_equiv e fun β hβ2 _ L hL _ =>
      odd_GFE_not_smallType (Or.inl rfl) hodd β hβ2 hL
  case F4 =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hm
    rw [← hK] at hodd
    exact noSmallComponent_of_equiv e fun β hβ2 _ L hL _ =>
      odd_GFE_not_smallType (Or.inr (Or.inl rfl)) hodd β hβ2 hL
  case E6 =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hm
    rw [← hK] at hodd
    exact noSmallComponent_of_equiv e fun β hβ2 _ L hL _ => odd_E6_not_smallType hodd β hβ2 hL
  case E7 =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E7 hm
    rw [← hK] at hodd
    exact noSmallComponent_of_equiv e fun β hβ2 _ L hL _ => odd_E7_not_smallType hodd β hβ2 hL
  case E8 =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E8 hm
    rw [← hK] at hodd
    exact noSmallComponent_of_equiv e fun β hβ2 _ L hL _ =>
      odd_GFE_not_smallType (Or.inr (Or.inr rfl)) hodd β hβ2 hL
  case twistedE6 =>
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .E6 hp hf hm
    exact noSmallComponent_of_equiv e fun β hβ2 _ L hL _ =>
      odd_twistedE6_not_smallType hp hp2 hf hK σ hσ β hβ2 hL
  case trialityD4 =>
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf hm
    exact noSmallComponent_of_equiv e fun β hβ2 _ L hL _ =>
      odd_triality_not_smallType hp hp2 hf hK σ hσ β hβ2 hL
  all_goals exact hm.elim

end CFSG.ComponentClassification.ExcSelector
