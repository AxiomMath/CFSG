module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67L2
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67L2Nine

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem cf67CoreDeriv_L2_nine (Y : Type) [Group Y] [Finite Y]
    (hL : Blueprint.LieModel Y .PSL 2 3 2) : CF67CoreDeriv Y 3 := by
  intro _ _ V Z h2 _
  obtain ⟨-, -, -, hpf3, F, _, _, hFcard, ⟨e0⟩⟩ :=
    ComponentClassification.AutL2Facts.lieModel_psl2_data hL
  have hF9 : Nat.card F = 9 := by rw [hFcard]; norm_num
  have hFL : L2Field F := by
    refine ⟨?_, ?_⟩
    · rw [hF9]; decide
    · rw [hF9]; decide
  exact cf67_L2_nine hFL (e0.trans (L2.equivPSL F).symm) hF9 h2

theorem cf67L2_thm (hGA : CFSG.Open.GriessAllModelsStatement) :
    CF67L2 :=
  cf67L2_of_nine hGA cf67CoreDeriv_L2_nine

end CFSG.GH74.GLS.Stage2.Bender.Thm1
