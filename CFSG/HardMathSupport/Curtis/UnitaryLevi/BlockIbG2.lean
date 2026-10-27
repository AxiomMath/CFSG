module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbGeneric
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc.Cells

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc

theorem isClassicalTwoOrG2_of_isLieOf_g2 {X : Type} [Group X] (h : IsLieOf IdxG2 X) :
    IsClassicalTwoOrG2 X := by
  obtain ⟨⟨d, hv⟩, hd, he⟩ := h
  cases d with
  | G2 q => exact Or.inl ⟨⟨_, hv⟩, hd, he⟩
  | _ => exact hd.elim

section G2


theorem blockIb_false_g2 {Y : Type} [Group Y] [Finite Y] {Lb Pb D : Subgroup Y} {x : Y}
    (hP : BlockIbParab Lb Pb) (hX : IsLieOf IdxG2 (↥Lb ⧸ Subgroup.center ↥Lb))
    (hD : BlockIbData Lb Pb D x) : False := by
  have hCP : CompParabE Lb Pb :=
    CompParab.toE (compParab_of_blockIb hP hD (isClassicalTwoOrG2_of_isLieOf_g2 hX))
  obtain ⟨-, -, -, v, hv⟩ := exists_centCycBar hCP Nat.prime_three hD.Dperf hD.Dle hD.Dcyc
    hD.Dcarry hD.hx hD.hx3 hD.hxC hD.free
  exact false_of_centCycBar_escapes hv (center_bar_eq_bot hCP)
    (centralizerEscapes_of_isLieOf_g2 hX Nat.prime_three (by norm_num))

theorem blockIbRankFam_g2 : BlockIbRankFam (IsLieOf IdxG2) := by
  intro Y _ _ Lb Pb D x hP hX hD
  exact (blockIb_false_g2 hP hX hD).elim

theorem blockIbAbFam_g2 : BlockIbAbFam (IsLieOf IdxG2) := by
  intro Y _ _ Lb Pb D x hP hX hD
  exact (blockIb_false_g2 hP hX hD).elim

end G2

end CFSG.HardMathSupport.Curtis.UnitaryLevi
