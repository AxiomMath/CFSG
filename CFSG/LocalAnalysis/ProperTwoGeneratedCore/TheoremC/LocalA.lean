module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.LocalAEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.LocalARankTwo
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.LocalASylow

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly CFSG.ShultStronglyClosedTI

variable {X : Type} [Group X] [Finite X] {Y : Subgroup X} {u z : X}

theorem quasiHullTwoPointOdd (hI : CaseOneInvolutions) (h3 : QuasiRankThree)
    (IH : TheoremCBelow (Nat.card X)) (hc : CoreConfig Y u z) {a : X ⧸ CFSG.Open.pCore 2 X}
    (ha : orderOf a = 2) (haz : Commute a (QuotientGroup.mk' (CFSG.Open.pCore 2 X) z))
    (hesc : ¬ Subgroup.centralizer ({a} : Set (X ⧸ CFSG.Open.pCore 2 X)) ≤
      Y.map (QuotientGroup.mk' (CFSG.Open.pCore 2 X))) :
    QuasiHullTwoPointOdd Y z (quasiPreimage a) := by
  obtain ⟨R, z', hRN, hRY, hR2, hRmax, hz'R, hz'c, hz'cl, hVR⟩ := exists_sylow_le hc ha haz
  by_cases hrank : 3 ≤ CFSG.Open.pRank 2 R
  · exact h3 X Y u z IH hI hc (quasiPreimage a) R z' (quasiPreimage_isPGroup ha)
      (twoCore_le_quasiPreimage a) (quasiPreimage_not_le ha)
      (mul_self_mem_of_mem_quasiPreimage ha) (pRank_quasiPreimage hc ha haz hesc)
      (normalizer_quasiPreimage_not_le ha hesc) hRN hRY hR2 hRmax hz'R hz'c hz'cl hrank
  · exact quasiHullTwoPointOdd_of_pRank_le_two hc ha hRN hR2 hRmax
      (hVR (twoCore_le_quasiPreimage a hc.mem_twoCore)) hz'R hz'c hz'cl (by omega)

theorem quotientLocalEmbedding (hI : CaseOneInvolutions) (h3 : QuasiRankThree) :
    QuotientLocalEmbedding := by
  intro X _ _ Y u z IH hc
  refine ⟨hc.map_ne_top, Subgroup.mem_map_of_mem _ hc.lever_mem, hc.orderOf_mk_lever,
    hc.mk_lever_mem_rightConjugate_iff, fun a ha haz hesc => ?_⟩
  exact fusionStronglyEmbedded_of_quasiHullTwoPointOdd hc ha haz hesc
    (quasiHullTwoPointOdd hI h3 IH hc ha haz hesc)

end CFSG.ProperTwoGeneratedCore.TheoremC
