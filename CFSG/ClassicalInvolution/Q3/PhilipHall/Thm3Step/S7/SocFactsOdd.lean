module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwoInputs
public import CFSG.GH74.GLS.Prop27.LocBalL33
public import CFSG.GH74.GLS.Prop27.LocBalU33
public import CFSG.GH74.KGroups.M12LocBal

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident

theorem socleOddCore_proved :
    SocleOddCore := by
  intro G _ _ N hN hC hS z hz
  have key : CFSG.pPrimeCore 2 ↥(Subgroup.centralizer ({z} : Set G)) = ⊥ := by
    rcases hS with h | h | h
    · exact GH74.GLS.Prop27.locBal2_L33 G N hN h hC z hz
    · exact GH74.GLS.Prop27.locBal2_U33 G N hN h hC z hz
    · exact GH74.KGroups.M12.locBal2_M12 G N hN h hC z hz
  rw [← GH74.KGroups.M12.oddCore_eq_pPrimeCore_two] at key
  exact key

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident
