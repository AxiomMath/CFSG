module

public import CFSG.ClassicalInvolution.Q3.TL4MF163L33
public import CFSG.ClassicalInvolution.Q3.TL4E3Z2

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution

theorem modelL3U3Acts3_proved :
    ModelL3U3Acts3 := by
  intro X _ _ R S z hd hc hL
  rcases hL with hL | hU
  · obtain ⟨e⟩ := GH74.KGroups.L33.equiv_of_lieModel hL
    exact MF163.tightActs3_of_equiv_l33 e hd hc
  · obtain ⟨e⟩ := GH74.KGroups.U33.equiv_of_lieModel hU
    exact MF163.tightActs3_of_equiv_u33 e hd hc

end CFSG.ClassicalInvolution.Q3.TL4
