module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVProof.TableVBasic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem tableV_shape_4B {a z c : G} (h : IsF5Type a z) (hT4 : TableIVFacts a z)
    (hc : c ∈ orb4B a a) : IsShapeZ2TimesSym 6 ↥(Gxy a c) := by
  obtain ⟨hb, hc2⟩ := tableV_orb4B_row h hc
  have hshape := hT4.shape_4B ((a * c) ^ 2) hb c hc2
  rwa [tableV_Gxy_eq_Gxyz_pow a c 2]

theorem tableV_shape_6A {a z c : G} (h : IsF5Type a z) (hT4 : TableIVFacts a z)
    (hc : c ∈ orb6A a a) : IsShapeZ2TimesSym 5 ↥(Gxy a c) := by
  obtain ⟨hb, hc5⟩ := tableV_orb6A_row h hc
  have hshape := hT4.shape_6A ((a * c) ^ 3) hb c hc5
  rwa [tableV_Gxy_eq_Gxyz_pow a c 3]

theorem tableV_card_4B {a z c : G} (h : IsF5Type a z) (hT4 : TableIVFacts a z)
    (hc : c ∈ orb4B a a) : Nat.card ↥(Gxy a c) = 1440 := by
  obtain ⟨hb, hc2⟩ := tableV_orb4B_row h hc
  have hcard := hT4.card_stab ((a * c) ^ 2) hb 2 c hc2
  rw [← Gxyz_eq_inf, ← tableV_Gxy_eq_Gxyz_pow a c 2] at hcard
  simpa using hcard

theorem tableV_card_6A {a z c : G} (h : IsF5Type a z) (hT4 : TableIVFacts a z)
    (hc : c ∈ orb6A a a) : Nat.card ↥(Gxy a c) = 240 := by
  obtain ⟨hb, hc5⟩ := tableV_orb6A_row h hc
  have hcard := hT4.card_stab ((a * c) ^ 3) hb 5 c hc5
  rw [← Gxyz_eq_inf, ← tableV_Gxy_eq_Gxyz_pow a c 3] at hcard
  simpa using hcard

end CFSG.EvenSporadicStandard.HNRecog.Section3
