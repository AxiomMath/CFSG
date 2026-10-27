module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55G2Par
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55G2Out

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank


theorem defData_g2 {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hm : LieModel Y .G2 0 p f) : DefData p Y :=
  ⟨borelTitsConcl_g2 hm, evenParabolics_g2 hp hp2 hm, outerFalse_g2 hp hp2 hf hm⟩

theorem def55_g2 : Def55 FG2d :=
  def55_of_defData fun _ _ _ _ hp hp2 _ ⟨_, hf, hm⟩ => defData_g2 hp hp2 hf hm

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
