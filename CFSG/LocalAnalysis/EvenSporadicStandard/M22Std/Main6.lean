module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.Main3
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutRest4
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.Cov11

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem m22_not_standard_of_split
    (hSol : CFSG.EvenSporadicStandard.Fin76b.SolomonZ2A6) (hX : Fin77aOuterXbar)
    (hR : Fin77aOuterRest₄) (h25 : Finkelstein77.Asc76Lemma25)
    (hSplit : HaradaSolomon08M22Split) (h : StdHyp G L) :
    ¬ IsSporadic (L ⧸ center L) .M22 := by
  intro hq
  by_cases hC : center L = ⊥
  · have hL : IsSporadic L .M22 := by
      obtain ⟨e⟩ := hq
      exact ⟨((QuotientGroup.quotientMulEquivOfEq hC).trans QuotientGroup.quotientBot).symm.trans
        e⟩
    obtain ⟨t, ht, ht2⟩ := h.exists_involution_centralizer
    rcases (Nat.dvd_prime Nat.prime_two).1 (relIndex_dvd_two h hL ht ht2) with h1 | h2
    · exact m22_inner_false hSol h hL ht ht2 (Subgroup.relIndex_eq_one.1 h1 |>.trans
        (sup_le_sup_left le_rfl _))
    · exact false_of_outer_of_rest₃ autSylowEngine_m22 (fin77aOuterRest₃_of_split hX hR) h hL ht
        ht2 h2
  · exact false_of_center_ne_bot_of_split h25 hSplit h hq hC

end CFSG.EvenSporadicStandard.M22Std
