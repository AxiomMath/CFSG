module

public import CFSG.GH74.Uniqueness.Section14Lem47A
public import CFSG.GH74.Uniqueness.Section14Lem47B

public section

namespace CFSG.GH74.Uniqueness

theorem lemma147 {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X} {t : X} {n r : ℕ}
    {L K J Mo P U T S2 : Subgroup X} (F : Facts14 Z M t n r L K J Mo P U T S2)
    (h146 : Concl146 M t n K Mo U T S2) : Concl147 n K J Mo U T S2 where
  complement _ hyJ hyp hydvd hyU := Sec147.complement_exists F h146 hyJ hyp hydvd hyU
  elem := Sec147.elem_of_involution F h146

end CFSG.GH74.Uniqueness
