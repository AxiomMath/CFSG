module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpTKill
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Prop13Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Section

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG.EvenSporadicStandard.HSStd CFSG.Blueprint CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {S : Subgroup G} {z n v s : G}

theorem sporadicInvComp_of_setup
    (h : HSOuterSetup G L t S z n v s) : SporadicInvComp G := by
  have hc : center ↥L = ⊥ := center_eq_bot_of_isSporadic_hs h.setting.2.1
  obtain ⟨e⟩ := h.setting.2.1
  exact ⟨t, L, .HS, h.t_two,
    Prop13.isCompIn_centralizer_singleton h.setting.1.standard h.t_two h.t_mem,
    ⟨((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans e⟩⟩

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
