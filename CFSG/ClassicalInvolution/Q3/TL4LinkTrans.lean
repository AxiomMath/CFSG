module

public import CFSG.ClassicalInvolution.Q3.TL4LinkCases
public import CFSG.ClassicalInvolution.Q3.TL4SecOrbit

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem natCard_linkGrp_lt_of_large (hL : TightLargeHypR r n Y R S t) :
    Nat.card ↥(linkGrp R t) < n := by
  have hz := hL.datum.isUniqueInvolution_core
  have hx : ∃ g : Y, g * t ≠ t * g := by
    by_contra hcon
    have htc : t ∈ Subgroup.center Y :=
      Subgroup.mem_center_iff.mpr fun g => by
        by_contra h
        exact hcon ⟨g, h⟩
    rw [hL.center, Subgroup.mem_bot] at htc
    exact hz.ne_one htc
  exact (Subgroup.card_le_card_group _).trans_lt
    ((natCard_secQuot_lt (Ω := CoreAssembly.conjClass (tightCore R)) hx).trans_eq hL.card)

theorem tightLinkTransR_three (n : ℕ) : TightLinkTransR 3 n := by
  intro h4 Y _ _ R S t hL _ _ hnc L hLm L' hL'm
  obtain ⟨g, -, hg⟩ := omegaTransitive_of_not_dConnected h4
    ((typeRFam_coreLinkFam hL).restrict (linkGrp R t)) (oddCore_linkGrp_eq_bot hL)
    (natCard_linkGrp_lt_of_large hL) hLm hnc L' hL'm
  exact ⟨g, hg⟩

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
