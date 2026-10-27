module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9Lemma5E49
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9Lemma5Red
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9Lemma5Two
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma5Ord

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

theorem case1295Two_of_F4
    (h1222 : Stmt12_2_2_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hD310 : D310) (hD391 : D391) (hI4 : Insp4) (hFine : F918Fine4) : Case1295Two_F4 := by
  intro G _ _ T L V n hcx V₁ K₁ hV₁ hU hLK hK hHz hlist hnot
  have hspor : (Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* NativeSporadic.M24) ∨
      Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* NativeSporadic.J4) ∨
      Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* NativeSporadic.M23) ∨
      Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* NativeSporadic.HS) ∨
      Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* NativeSporadic.He) ∨
      Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* NativeSporadic.Ru)) → False := by
    intro h
    obtain ⟨hS, hord⟩ := L1295B.isSimpleGroup_and_not_fourListOrder h
    exact hord (L1295B.card_of_fourList (L1295B.fourList_of_simple_F4 h1222 h37 h38 h39 hD310
      hD391 hI4 hcx hV₁ hU hLK hK hHz hS))
  rcases hlist with (h5 | h24 | hJ4) | (h4 | h7 | h7h | h23 | hHS | hHe | hRu | hE)
  · exact hnot (Or.inr (Or.inr h5))
  · exact hspor (Or.inl h24)
  · exact hspor (Or.inr (Or.inl hJ4))
  · exact hnot (Or.inr (Or.inl h4))
  · exact hnot (Or.inl h7)
  · exact L1295B.false_of_hatA7_F4 h1222 h37 h38 h39 hD310 hD391 hI4 hFine hcx hV₁ hU hLK hK hHz
      h7h
  · exact hspor (Or.inr (Or.inr (Or.inl h23)))
  · exact hspor (Or.inr (Or.inr (Or.inr (Or.inl hHS))))
  · exact hspor (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hHe)))))
  · exact hspor (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hRu)))))
  · exact L1295B.false_of_e49_F4 h1222 h37 h38 h39 hcx hV₁ hU hLK hK hHz hE

end CFSG.Quasithin.H13
