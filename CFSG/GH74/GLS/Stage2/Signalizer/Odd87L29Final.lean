module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29GWMain
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29NonSolvB
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FinalTheorem
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29NonSolv

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.GorensteinWalter

theorem lemma29NonSolv_of
    (hFirst : Lemma29First) : Lemma29NonSolv := by
  intro G _ _ z k S ctx U hU X hX hns
  have hGW : gorensteinWalterStatement.{0} := gorensteinWalter
  rcases hFirst G z k S ctx U hU with h2 | ⟨-, hdih, -⟩ | ⟨-, hb⟩
  · have : Group.IsSolvable ↥(centralizer (U : Set G)) := isSolvable_of_hasNormal2Compl h2
    exact absurd (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hX)
      (Subgroup.inclusion_injective hX)) hns
  · exact lemma29NonSolv_classical hGW hX hdih hns
  · have : Group.IsSolvable ↥(centralizer (U : Set G)) := isSolvable_of_lemma29b hb
    exact absurd (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hX)
      (Subgroup.inclusion_injective hX)) hns

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
