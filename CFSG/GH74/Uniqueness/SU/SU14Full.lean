module

public import CFSG.GH74.Uniqueness.SU.SU14Main
public import CFSG.GH74.Uniqueness.SU.SU14T184
public import CFSG.GH74.Uniqueness.SU.SU4P189
public import CFSG.GH74.Uniqueness.SU.SU7Final
public import CFSG.GH74.Uniqueness.SU.SU7L196c3
public import CFSG.GH74.Uniqueness.SU.SU8B202
public import CFSG.GH74.Uniqueness.SU.SU9Orb
public import CFSG.GH74.Uniqueness.SU.SU10P211
public import CFSG.GH74.Uniqueness.SU.SU10P212
public import CFSG.GH74.Uniqueness.Section165GapFinal
public import CFSG.GH74.GLS.IVK.KI2

public section

namespace CFSG.GH74.Uniqueness.SU.SU14

theorem sec19_false_of_kfacts (hKI3 : K.KI3) (hKI4 : K.KI4) : SU7.Sec19FalseStmt :=
  SU9.sec19_false_of_stmts SU7.lemma191 (SU7.lemma192 hKI3 hKI4)
    (SU7.lemma194 hKI3 hKI4) (SU7.cor195 hKI3 hKI4)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ hc _ ha haU => SU7.L196c.lemma196c hKI3 hKI4 hc ha haU)

theorem thm184_of_kfacts
    (hKI1 : K.KI1) (hKI3 : K.KI3) (hKI4 : K.KI4) : SU7.Thm184Stmt :=
  thm184_of_stmts SU4.lemma186 SU4.lemma18H (SU4.prop189 hKI1 CFSG.GH74.GLS.IVK.ki2)
    (sec19_false_of_kfacts hKI3 hKI4)

theorem S_Thm182_of_kfacts
    (hKI1 : K.KI1) (hKI3 : K.KI3) (hKI4 : K.KI4)
    (hKI5 : K.KI5) (hKI6 : K.KI6) (h221 : SU12.Prop221Stmt)
    (h231 : SU13.Thm231Stmt) : S_Thm182 :=
  S_Thm182_of_stmts SU4.lemma183 (thm184_of_kfacts hKI1 hKI3 hKI4)
    (SU10.prop211 hKI5 hKI6 (SU8.prop201 hKI5))
    (SU10.cor213 hKI6 S_CorZD_unconditional) h221 h231

theorem S_SU_of_kfacts
    (hKI1 : K.KI1) (hKI3 : K.KI3) (hKI4 : K.KI4)
    (hKI5 : K.KI5) (hKI6 : K.KI6) (h221 : SU12.Prop221Stmt)
    (h231 : SU13.Thm231Stmt) : S_SU :=
  S_SU_of_S_Thm182 (S_Thm182_of_kfacts hKI1 hKI3 hKI4 hKI5 hKI6 h221 h231)

theorem S_SUS_KGH_of_kfacts
    (hKI1 : K.KI1) (hKI3 : K.KI3) (hKI4 : K.KI4)
    (hKI5 : K.KI5) (hKI6 : K.KI6) (h221 : SU12.Prop221Stmt)
    (h231 : SU13.Thm231Stmt) : GLS.S_SUS_KGH :=
  GLS.S_SUS_KGH_of_S_SU (S_SU_of_kfacts hKI1 hKI3 hKI4 hKI5 hKI6 h221 h231)

end CFSG.GH74.Uniqueness.SU.SU14
