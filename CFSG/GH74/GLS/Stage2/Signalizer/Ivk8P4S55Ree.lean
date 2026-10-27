module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55ReePar
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55ReeOut

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank


theorem outerFalse_ree {Y : Type} [Group Y] [Finite Y] {f : ℕ} (hf : 1 ≤ f)
    (hm : LieModel Y .twistedG2 0 3 f) : OuterFalse 3 Y := by
  obtain ⟨f', hR⟩ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Odd87.reeTitsModel_of_FRee (Y := Y) ⟨f, hf, hm⟩
  obtain ⟨a, K, _, _, _, ha, hK, ⟨e⟩⟩ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Odd87.ree_model_data_pos hR
  exact OuterFalse.of_mulEquiv e (outerFalse_ree_native ha hK)

theorem defData_ree {Y : Type} [Group Y] [Finite Y] {f : ℕ} (hf : 1 ≤ f)
    (hm : LieModel Y .twistedG2 0 3 f) : DefData 3 Y :=
  ⟨borelTitsConcl_ree hm, evenParabolics_ree hf hm, outerFalse_ree hf hm⟩

theorem def55_ree : Def55 FReed :=
  def55_of_defData fun _ _ _ _ _ _ _ ⟨hp3, f, hf, hm⟩ => by
    subst hp3
    exact defData_ree hf hm

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
