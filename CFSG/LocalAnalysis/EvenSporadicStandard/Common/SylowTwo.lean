module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction
public import CFSG.LocalAnalysis.EvenSmallLie.CyclicKernelSylow

public section

namespace CFSG.EvenSporadicStandard

open Subgroup CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem StdHyp.toStandardSetting (h : StdHyp G L) : EvenSmallLie.StandardSetting G L :=
  ⟨h.simple, h.nonabelian, h.kProper, h.standard, h.oddCore, h.cyclicSylow⟩

theorem StdHyp.card_sylow_eq_two_of_fours (h : StdHyp G L)
    (hI : HypothesisOne (L ⧸ center L)) (hFG : EvenSmallLie.FoursGroupCondition L)
    (S : Sylow 2 (centralizer (L : Set G))) : Nat.card S = 2 :=
  EvenSmallLie.card_sylow_eq_two_of_standard h.toStandardSetting hI hFG S

theorem StdHyp.card_sylow_eq_two_of_inner (h : StdHyp G L)
    (hI : HypothesisOne (L ⧸ center L))
    (hinn : ∀ α : MulAut (L ⧸ center L), ∃ q, α = MulAut.conj q)
    (S : Sylow 2 (centralizer (L : Set G))) : Nat.card S = 2 := by
  have : Group.IsPerfect L := Group.isPerfect_def.2 h.standard.1.1
  exact h.card_sylow_eq_two_of_fours hI
    (EvenSmallLie.FoursGroupCondition.of_forall_eq_conj_quotient hinn) S

end CFSG.EvenSporadicStandard
