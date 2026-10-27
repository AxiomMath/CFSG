module

public import CFSG.GH74.GLS.Bg.Pu5.L299T
public import CFSG.GH74.GLS.Bg.Pu5.L299Abs
public import CFSG.GH74.GLS.Bg.Pu5.Assembly
public import CFSG.GH74.GLS.Bg.Pu5.L299Statements

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.Iii2 CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec6

theorem l299_of_parts (hM : L299MS) : L299 := by
  have hT := l299t_of
  intro G _ _ z t S hC hcard P
  obtain ⟨K, hK⟩ := rigid_nonempty hC.hz hC.hzK
  obtain ⟨e⟩ := hT G z t S hC hcard K hK P
  rcases hM G z t S hC hcard K hK with hcyc | hmax
  · exact Or.inl (e.isCyclic.2 hcyc)
  · exact Or.inr (isNonabelianMaximalClassTwoGroup_of_mulEquiv e.symm hmax)

end CFSG.GH74.GLS.Bg.Pu5
