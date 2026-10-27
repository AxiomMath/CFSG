module

public import CFSG.GH74.GLS.C3.Layer1.P34Core
public import CFSG.GH74.GLS.C3.Layer1.P34L310
public import CFSG.GH74.GLS.C3.Layer1.P34Transfer
public import CFSG.GH74.GLS.C3.Layer1.P34L37
public import CFSG.GH74.GLS.C3.Layer1.P34L38
public import CFSG.GH74.GLS.C3.Layer1.P34L39
public import CFSG.GH74.GLS.C3.Layer1.P34Odd
public import CFSG.GH74.GLS.C3.Layer1.P34QShape

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34

open Subgroup

variable {X : Type} [Group X] [Finite X] {T P Q : Subgroup X} {x z f h : X}

theorem prop34_core_of_dihedral (c : Cfg34 X T P Q x z f h) (hD : DihedralShapeFacts)
    (hM : DihedralMaxFacts) : False := by
  have h35 := lemma35 c
  have h37 := lemma37 c hD qShapeFacts oddMove
  have h38 := lemma38 c hD qShapeFacts h37
  have h39 := lemma39 c h38
  have h310 := lemma310 c alperinStep oddMove
    (fun hDT hPD hg hgodd hmove => lemma310_core c hD hM h38 h39 hDT hPD hg hgodd hmove)
  exact prop34_core c h35 h37 h310 qShapeFacts h38

end CFSG.GH74.GLS.C3.Layer1.P34
