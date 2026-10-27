module

public import CFSG.LocalAnalysis.OddStandard.L2Ree.ReeStructureAut
public import CFSG.GH74.Generic.S45.KBaseRee
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.SylowTwo

public section

namespace CFSG.OddStandard.L2Ree

open Subgroup CFSG.Blueprint CFSG.GH74.Generic.S45

section Ree


theorem kBase_of_lieModel_twistedG2 {Y : Type} [Group Y] [Finite Y] {f : ℕ}
    (hm : LieModel Y .twistedG2 0 3 f) : KBase Y :=
  kBase_of_reeModel (LieModel.reeTitsModel hm (by decide)).2

theorem card_sylow_centralizer_eq_two {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : CFSG.EvenSporadicStandard.StdHyp G L) {f : ℕ} (hm : LieModel (L ⧸ center L) .twistedG2 0 3 f)
    (S : Sylow 2 (centralizer (L : Set G))) : Nat.card S = 2 := by
  have hK := kBase_of_lieModel_twistedG2 hm
  have : Group.IsPerfect L := Group.isPerfect_def.2 h.standard.1.1
  exact h.card_sylow_eq_two_of_fours (hypothesisOne_of_kBase hK)
    (foursGroupCondition_of_kBase hK) S

end Ree

end CFSG.OddStandard.L2Ree
