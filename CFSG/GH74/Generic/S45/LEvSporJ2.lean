module

public import CFSG.GH74.GLS.C3.Layer1.EvenSpor
public import CFSG.GH74.Generic.S45.LEvSporFacts

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore

namespace CFSG.GH74.GLS

theorem b_spor_J2_table_proved :
    B_spor_J2_table := by
  intro G _ _ H K hH hKH hK5 hrk
  obtain ⟨e⟩ := hH
  have hF : Generic.S45.J2Facts H :=
    Generic.S45.J2Facts.of_equiv (e.trans j2PermEquiv) Generic.S45.EvSpor.j2_facts
  obtain ⟨E, hEY, hEa, hE4⟩ := Generic.S45.exists_elemAb_of_two_le_pRank hrk
  exact Generic.S45.leaf1_of_facts hF hKH hK5 ⟨E, hEY, hEa, hE4⟩

end CFSG.GH74.GLS
