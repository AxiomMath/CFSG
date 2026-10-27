module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S146F13
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S146zQLists
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S146zRCaseTwo
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S146zRL3Set
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S146zRSL2Fin
public import CFSG.Quasithin.EmptyFaithful.S146zMList
public import CFSG.Quasithin.EmptyFaithful.S146zSWr

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

theorem input14614Shape_of_inputs_F4 (h12 : Stage14612PartP_F4) (h36 : A36ForSQTK)
    (hlist : SQTKList3Dvd) (iL : Input14614Lists_F4) (iS : Input14614NoSz) :
    Input14614Shape_F4 := by
  intro G _ _ T M S H PQ p hred hmax hne
  refine (stage14614At_iff T H p).mpr ?_
  obtain ⟨K₁, hK₁, ⟨s, hsT, hsN, hKz, hcase⟩ | ⟨hp3, hKz, n, hn, e⟩⟩ :=
    iL G T M S H PQ p hred hmax hne
  · rcases hcase with ⟨m, hm, hpm, e⟩ | ⟨hp3, e⟩
    · rcases S.p_eq_three_or_five_of_isRedCE hred with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, K₁, s, hK₁, hsT, hsN, hKz,
          Or.inl (q_wreath_A5_F4 h12 h36 hlist iS S hred hmax hK₁ hsT hsN hKz hm hpm e).2⟩))
      · obtain ⟨rfl, hII, hidx⟩ :=
          q_stage14614C4_data h36 hlist iS S hred hmax hK₁ hsT hsN hKz hm hpm e
        exact Or.inr (Or.inr (Or.inr ⟨rfl, K₁, s, hK₁, hsT, hsN, hKz, hII, hidx, e⟩))
    · subst hp3
      exact Or.inr (Or.inr (Or.inl ⟨rfl, K₁, s, hK₁, hsT, hsN, hKz,
        Or.inr (q_wreath_L3_F4 h12 h36 hlist iS S hred hmax hK₁ hsT hsN hKz e)⟩))
  · exact Or.inr (Or.inl (q_stage14614C2_F4 h12 h36 hlist iS S hred hmax hK₁ hp3 hKz hn e))

theorem input14614Shape_proved_F4
    (h12 : Stage14612PartP_F4) (h36 : A36ForSQTK) (iL : Input14614Lists_F4) (iS : Input14614NoSz) :
    Input14614Shape_F4 :=
  input14614Shape_of_inputs_F4 h12 h36 sqtkList3Dvd_proved iL iS

end CFSG.Quasithin
