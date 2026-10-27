module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LocalGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.CSideFacts
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Transport
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.Qz
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Qz
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.QzRank
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.TwoB
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Inter
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem gzNo_inter_twoB (hC : CSideFacts) {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (hF3 : Vert Fusion3Facts a z) (hOrb : Vert GzOrbitFacts a z)
    (hCls : GzClassFacts a z) (x : ↥(Gx z)) (hx2 : (x : G) ^ 2 = 1)
    (hsh : IsShapeTwoTwoTimesA5 ↥(CbarCent z x)) {t : G} (ht : t ∈ Qz z ⊓ Qz (x : G))
    (ht1 : t ≠ 1) : IsConj z t := by
  obtain ⟨hxB, hxQ⟩ := gzNo_twoB hC h hF3 hOrb.self hCls x hx2 hsh
  have hint := gzNo_inter hC h hF3 hOrb hCls x hx2 hsh
  obtain ⟨htz, htQx⟩ := Subgroup.mem_inf.mp ht
  have ht2 : t ^ 2 = 1 := hint.2.2 t ht
  have ht2ord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  rcases hCls.inv_two t ht2ord with hA | hZ
  ·
    exfalso
    have hx' : IsF5Type a (x : G) := isF5Type_of_isConj h (IsConj.refl a) hxB
    have htx : t ≠ (x : G) := fun hEq => hxQ (hEq ▸ htz)
    have htGx : t ∈ Gx (x : G) := gzNo_Qz_le (x : G) htQx
    have hxt_eq : (x : G) * t = t * (x : G) := mem_Gx.mp htGx
    have hisConj : IsConj t (t * (x : G)) :=
      isConj_mul_of_mem_Qz hx'.cent_z hx'.orderOf_z ht2ord htx htQx
    have ha_xt : IsConj a ((x : G) * t) := hA.trans (hxt_eq.symm ▸ hisConj)
    set w : ↥(Gx z) := x * ⟨t, gzNo_Qz_le z htz⟩ with hwdef
    have hcent : CbarCent z w = CbarCent z x := by
      rw [hwdef]
      exact gzNo_cbarCent_mul x ⟨t, gzNo_Qz_le z htz⟩ htz
    have hsh_w : IsShapeTwoTwoTimesA5 ↥(CbarCent z w) := by
      rwa [hcent]
    have hx2w : (w : G) ^ 2 = 1 := by
      rw [hwdef]
      change ((x : G) * t) ^ 2 = 1
      rw [Commute.mul_pow hxt_eq 2, hx2, ht2, mul_one]
    have hz_xt : IsConj z ((x : G) * t) := by
      have hh := (gzNo_twoB hC h hF3 hOrb.self hCls w hx2w hsh_w).1
      simpa [hwdef] using hh
    exact (gzNo_not_isConj h hOrb.self) (ha_xt.trans hz_xt.symm)
  · exact hZ

end CFSG.EvenSporadicStandard.HNRecog.Section3
