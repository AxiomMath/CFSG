module

public import CFSG.GH74.Uniqueness.ZDFinal
public import CFSG.GH74.Uniqueness.Section165GapMain

public section

namespace CFSG.GH74.Uniqueness

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.false_unconditional
    (S : ZDSetup X Z M) : False := by
  have h122 := S.lemma122
  have h123 := S.lemma123
  have h124 := S.lemma124
  have h126 := S.lemma126 h124
  have h127 := S.lemma127 h124 h126
  have h128 := S.lemma128 h124 h127
  have h129 := S.lemma129 h124 h128
  have h1210 := S.lemma1210 h123 h124 h128 h129
  have h1211 := S.lemma1211 h1210 h127
  have h1212 := S.lemma1212
  have h1213 := S.prop1213 h1212
  have h1214 := S.lemma1214 h124 h1210 h1212 h1213
  have h12 : Sec12Results Z M :=
    ⟨h122, h123, h124, h126, h127, h128, h129, h1210, h1211, h1212, h1213, h1214⟩
  have h131 := S.prop131 h12
  have h141 := S.prop141 h12 h131
  have h151 := S.prop151 h12 h131 hering32_stmt
  have h121 := thm121_of Z M h122 h141 h151
  have h161 := S.lemma161
  have h162 := S.lemma162
  have h163 := S.lemma163
  have h164 := S.lemma164 h121 h161 h162 h163
  have h165 := S.prop165_gap h121 h161 h162 h163 h164
  have h166 := S.cor166 h163 h164 h165
  have h167 := S.lemma167 h166
  have h171 := S.lemma171 h166
  have h172 := S.lemma172 h121 h161 h164 h166 h167 h171
  have h173 := S.lemma173 h166 h172
  have h174 := S.lemma174 lemma311BenderStmt h166 h172
  have h175 := S.lemma175 h166 h171 h172
  have h176 := S.prop176 h121 h166 h172 h175
  exact S.false_of_stmts (fun _ => S.nonempty_conf16) h163 h166 h173 h174 h176

theorem S_ZD_gen_unconditional
    : S_ZD_gen :=
  S_ZD_gen_of_no_setup fun _ _ _ _ _ S => S.false_unconditional

theorem S_ZD_unconditional
    : S_ZD :=
  S_ZD_of_S_ZD_gen S_ZD_gen_unconditional

theorem S_CorZD_unconditional :
    S_CorZD :=
  S_CorZD_of_S_ZD_gen S_ZD_gen_unconditional

theorem gapHyp
    : GapHyp := fun _ _ _ _ _ S => S.false_unconditional.elim

end CFSG.GH74.Uniqueness
