module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTStmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1U3Rank
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31FLie

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open CFSG CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem rankCell_fu3 : RankCell FU3 := by
  intro k _ Y _ _ _ hY
  obtain ⟨p, f, hp, hf, hp2, hLie⟩ := id hY
  exact ⟨l31f_not_kindFactorAll_psu3 k hp hf (Or.inl (hp.odd_of_ne_two hp2).pow) hLie,
    fun E hE _ => L1.fu3_elemAbelian_le_eight hY E hE⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
