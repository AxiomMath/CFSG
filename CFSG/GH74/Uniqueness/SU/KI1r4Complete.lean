module

public import CFSG.GH74.Uniqueness.SU.KI1r3Final
public import CFSG.GH74.Uniqueness.SU.KI1r4L34
public import CFSG.GH74.Uniqueness.SU.KI1r4F61Main
public import CFSG.GH74.Uniqueness.SU.KI1r4QFinal

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

theorem ki1_of_f61gaps

























































 (G : F61Gaps) : KI1 :=
  ki1_of_r3_r4 K.R3.ki1r3
    (ki1r4_of_parts (f61full_of_gaps G) (ki1r4L34_of (ki1r4TwoGroup_of lemma85 ki1r4Q64))
      (ki1r4TwoGroup_of lemma85 ki1r4Q64))

end CFSG.GH74.Uniqueness.SU.K.R4
