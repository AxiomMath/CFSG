module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47CStmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47Inv
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47Rank3

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer

theorem p47BranchC_of (hfld : P47FieldCase) : P47BranchC := by
  intro G _ _ z k S _ F4 Y _ _ b hY hb2 p X hA hop hc hcp T' _ hTc hTn E hET hE
  have hEK : E ≤ ncl X := by
    intro e he
    have he2 : e * e = 1 := by
      have := hE.2 e he
      rwa [pow_two] at this
    have hbe : e * b = b * e := Subgroup.mem_centralizer_singleton_iff.mp (hTc (hET he))
    exact c_inv_mem_K hfld F4 hY hb2 hA hop hc hcp he2 hbe (hTn (hET he))
  obtain ⟨-, -, n, -, hLie⟩ := hcp
  exact card_elemAbelian_two_le_four_of_hat hA.prime hA.odd hLie E hEK hE

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
