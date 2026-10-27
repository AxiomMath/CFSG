module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LocalGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.CSideFacts
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.TwoB
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Five
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Inter
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.InterTwoB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

structure GzNoSpecial {G : Type} [Group G] (z x : G) : Prop where
  twoB : IsConj z x
  not_mem : x ∉ Qz z
  card_cent : Nat.card ↥(Qz z ⊓ Gx x) = 2 ^ 5
  z_not_mem : z ∉ Qz x
  card_inter : Nat.card ↥(Qz z ⊓ Qz x) = 2 ^ 4
  sq_inter : ∀ t ∈ Qz z ⊓ Qz x, t ^ 2 = 1
  twoB_inter : ∀ t ∈ Qz z ⊓ Qz x, t ≠ 1 → IsConj z t

theorem gzNo_special (hC : CSideFacts) {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (hF3 : Vert Fusion3Facts a z) (hOrb : Vert GzOrbitFacts a z)
    (hCls : GzClassFacts a z) (x : ↥(Gx z)) (hx2 : (x : G) ^ 2 = 1)
    (hsh : IsShapeTwoTwoTimesA5 ↥(CbarCent z x)) : GzNoSpecial z (x : G) := by
  obtain ⟨hB, hQ⟩ := gzNo_twoB hC h hF3 hOrb.self hCls x hx2 hsh
  obtain ⟨hzQ, hS, hS2⟩ := gzNo_inter hC h hF3 hOrb hCls x hx2 hsh
  exact ⟨hB, hQ, (gzNo_five hC h hOrb.self hCls x hx2 hsh).1, hzQ, hS, hS2,
    fun t ht ht1 => gzNo_inter_twoB hC h hF3 hOrb hCls x hx2 hsh ht ht1⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
