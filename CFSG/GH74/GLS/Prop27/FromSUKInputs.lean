module

public import CFSG.GH74.GLS.Prop27.FromSU
public import CFSG.GH74.Uniqueness.SU.SU14Rank3Final

public section

namespace CFSG.GH74.GLS.Prop27

open CFSG.GH74.E2

theorem s_prop27G_of_kinputs
    (hG : Generic.GenericKnownFacts) (hF : E2ComponentFacts)
    (hKI1 : Uniqueness.SU.K.KI1r3) (hKI5 : Uniqueness.SU.K.KI5b) (hKI6 : Uniqueness.SU.K.KI6) :
    S_prop27G :=
  s_prop27G_of_rank3 hG hF (Uniqueness.SU.SU14.S_Thm182_rank3_of_kinputs hKI1 hKI5 hKI6)

end CFSG.GH74.GLS.Prop27
