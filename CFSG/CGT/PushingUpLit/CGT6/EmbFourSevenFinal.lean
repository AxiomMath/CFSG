module

public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSeven
public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenInd
public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenSmall

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit

theorem fourSevenAlt_of_noCaseB (hB : NoCaseB) : FourSevenAlt := by
  intro V _ _ hV G T Y cfg hshort halt X hXG hX hYX
  obtain ⟨m, hm1, hnat⟩ := halt
  exact le_centralizer_of_small16 hB hV
    (small16_of_natural_alt hV cfg.adm.hperf hshort hm1 hnat)
    (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hX)) hYX

theorem fourSevenL24_of_noCaseB (hB : NoCaseB) : FourSevenL24 := by
  intro V _ _ hV G T Y cfg hshort hnat X hXG hX hYX
  exact le_centralizer_of_small16 hB hV
    (small16_of_natural_sl_four hV cfg.adm.hperf hshort hnat)
    (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hX)) hYX

theorem emb_four_seven_of_noCaseB {V : Type} [CommGroup V] [Finite V] (hM4 : SchurMultL2Two)
    (hB : NoCaseB) (hV : ∀ v : V, v ^ 2 = 1) {G T Y : Subgroup (MulAut V)}
    (cfg : Emb4Cfg G T Y) {X : Subgroup (MulAut V)} (hXG : X ≤ G) (hX : ¬ 2 ∣ Nat.card X)
    (hYX : Y ≤ Subgroup.normalizer (X : Set (MulAut V))) :
    X ≤ Subgroup.centralizer (Y : Set (MulAut V)) :=
  emb_four_seven hM4 (fourSevenAlt_of_noCaseB hB) (fourSevenL24_of_noCaseB hB) hV cfg hXG hX hYX

end CFSG.CGT.PushingUpLit.CGT6
