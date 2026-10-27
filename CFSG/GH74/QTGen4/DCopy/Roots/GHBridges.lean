module

public import CFSG.GH74.QTGen4.Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Statements

public section

namespace CFSG.GH74.QTGen4.DCopy.Roots

open CFSG.GH74.QTGen4

theorem stmt13_1_2_three_GH_of_F4 (h : CFSG.Quasithin.H13.Stmt13_1_2_three_F4) :
    Stmt13_1_2_three_GH :=
  fun G _ _ hc => by haveI := finite4_of_gen4 hc.1; exact h G

theorem stmt13_6_1_GH_of_F4 (h : CFSG.Quasithin.H13.Stmt13_6_1_F4) : Stmt13_6_1_GH :=
  fun G _ _ hc => by haveI := finite4_of_gen4 hc.1; exact h G

theorem stmt14_8_1_three_GH_of_F4 (h : CFSG.Quasithin.H13.Stmt14_8_1_three_F4) :
    Stmt14_8_1_three_GH :=
  fun G _ _ hc => by haveI := finite4_of_gen4 hc.1; exact h G

end CFSG.GH74.QTGen4.DCopy.Roots
