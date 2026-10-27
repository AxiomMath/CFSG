module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem even_card_of_stdHyp (h : StdHyp G L) : Even (Nat.card G) :=
  even_iff_two_dvd.2 (dvd_trans (even_iff_two_dvd.1 h.standard.2.1)
    (Subgroup.card_subgroup_dvd_card _))

theorem StdHyp_ne_bot (h : StdHyp G L) : L ≠ ⊥ := by
  have h1 : Nontrivial (L ⧸ center L) := h.standard.1.2.toNontrivial
  have : Nontrivial L := (QuotientGroup.mk_surjective (s := center L)).nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot L).1 this

end CFSG.EvenSporadicStandard.M22Std
