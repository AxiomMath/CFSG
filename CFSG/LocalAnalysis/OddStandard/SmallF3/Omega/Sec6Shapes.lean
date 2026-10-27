module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Main
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6ShapesDef

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Asc82OtherLeaves : Prop where
  h7 : AschOmega7
  h8p : AschOmega8Plus
  h8m : AschOmega8Minus
  h6z : AschOmega6MinusZ2

theorem asc82Shapes_of_leaves (h : Asc82OtherLeaves) : Asc82Shapes := by
  intro G _ _ t L hS
  have hF := hS.inF
  unfold InF IsFGroup at hF
  obtain ⟨-, hQ⟩ := hF
  rcases hQ with hQ | hQ
  · unfold SmallF3OmegaQuotient at hQ
    rcases hQ with h5 | h6p | h6m | h7 | h8p | h8m
    · exact Or.inl h5
    · exact Or.inr (Or.inl h6p)
    · exact Or.inr (Or.inr h6m)
    · exact (h.h7 G t L hS h7).elim
    · exact (h.h8p G t L hS h8p).elim
    · exact (h.h8m G t L hS h8m).elim
  · exact (h.h6z G t L hS hQ).elim

end CFSG.OddStandard.SmallF3.Omega
