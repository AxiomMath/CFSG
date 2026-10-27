module

public import CFSG.GH74.GLS.Prop27.LocBalFinal
public import CFSG.GH74.Uniqueness.SU.SU14Rank3

public section

namespace CFSG.GH74.GLS.Prop27

open CFSG.GH74.E2

theorem S_Thm182_P27_of_rank3 (h : Uniqueness.SU.SU14.S_Thm182_rank3) : S_Thm182_P27 :=
  fun G _ _ hs hn hK _ S hS hΓ => h G hs hn hK S hS hΓ

theorem s_prop27G_of_rank3
    (hG : Generic.GenericKnownFacts) (hF : E2ComponentFacts)
    (h : Uniqueness.SU.SU14.S_Thm182_rank3) : S_prop27G :=
  s_prop27G_of_facts hG hF (S_Thm182_P27_of_rank3 h)

end CFSG.GH74.GLS.Prop27
