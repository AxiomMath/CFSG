module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.FactsHS
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.UHered

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Induction

@[expose] def HSSection5At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ L : Subgroup G, HSLemma21Setting G L → False

@[expose] def HSSection5Hered : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Balance.UHered G → HSSection5At G

theorem hs_not_standard_at
    (F : HSFacts) {G : Type} [Group G] [Finite G] (h5 : HSSection5At G) {L : Subgroup G}
    (h : StdHyp G L) : ¬ IsSporadic L .HS := fun hL =>
  h5 L ⟨h, hL, fun S => h.card_sylow_eq_two_hs F hL S,
    fun _ ht ht2 => h.sylowFusion_hs F hL ht ht2,
    fun _ ht ht2 => h.relIndex_dvd_two_hs F hL ht ht2⟩

theorem hs_not_standard_of_section5At
    {G : Type} [Group G]
    [Finite G] (h5 : HSSection5At G) {L : Subgroup G} (h : StdHyp G L) : ¬ IsSporadic L .HS :=
  hs_not_standard_at hsFacts h5 h

end CFSG.EvenSporadicStandard.HSStd
