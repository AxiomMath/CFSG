module

public import CFSG.GH74.Uniqueness.SU.SU14P189
public import CFSG.GH74.Uniqueness.SU.SU14R3
public import CFSG.GH74.Uniqueness.SU.SU10P212
public import CFSG.GH74.Uniqueness.Section165GapFinal

public section

namespace CFSG.GH74.Uniqueness.SU.SU14

open CFSG.Blueprint

theorem S_Thm182_rank3_of_kfacts
    (hKI1 : K.KI1r3) (hKI2 : K.KI2) (hKI5 : K.KI5b) (hKI6 : K.KI6)
    (hKI7b : K.KI7b9) (hU : SU8.NoUnitaryStmt) : S_Thm182_rank3 :=
  S_Thm182_rank3_of_stmts SU4.lemma183 SU4.lemma186 SU4.lemma18H (prop189_rank3 hKI1 hKI2)
    (prop211_rank3 hKI5 hKI6 (prop201c_of hU)) (SU10.cor213 hKI6 S_CorZD_unconditional) hKI7b

end CFSG.GH74.Uniqueness.SU.SU14
