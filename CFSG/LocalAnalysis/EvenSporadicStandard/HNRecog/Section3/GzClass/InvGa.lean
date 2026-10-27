module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion2.Cover
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem isConj_of_involution_mem_Gx {G : Type} [Group G] {a z : G} (hF1 : Fusion1Facts a z)
    (hF2 : Fusion2Facts a z) {t : G} (ht : t ∈ Gx a) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) :
    IsConj a t ∨ IsConj z t := by
  obtain ⟨z₀, b, u, hF, hz₀, hz₀a, -, -, -, -⟩ := hF1.rep_z
  obtain ⟨⟨hbA, -, -, -⟩, ⟨huB, -, -, -, -, -, -⟩⟩ := hF2.reps_bu z₀ b u hF hz₀
  rcases exists_conj_rep hF ht ht2 ht1 with h | ⟨k, -, hkt⟩ | ⟨k, -, hkt⟩ |
    ⟨k, -, hkt⟩ | ⟨k, -, hkt⟩
  · left; rw [h]
  · right; exact hz₀.trans (isConj_iff.mpr ⟨k, hkt⟩)
  · left; exact hz₀a.trans (isConj_iff.mpr ⟨k, hkt⟩)
  · left; exact hbA.trans (isConj_iff.mpr ⟨k, hkt⟩)
  · right; exact huB.trans (isConj_iff.mpr ⟨k, hkt⟩)

theorem isConj_of_commute {G : Type} [Group G] {a z : G} (hF1 : Vert Fusion1Facts a z)
    (hF2 : Vert Fusion2Facts a z) {y t : G} (hy : IsConj a y) (hty : t * y = y * t)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) : IsConj a t ∨ IsConj z t := by
  have hF1y : Fusion1Facts y z := hF1 y z hy (IsConj.refl z)
  have hF2y : Fusion2Facts y z := hF2 y z hy (IsConj.refl z)
  have hty_mem : t ∈ Gx y := mem_Gx.mpr hty.symm
  rcases isConj_of_involution_mem_Gx hF1y hF2y hty_mem ht2 ht1 with h | h
  · exact Or.inl (hy.trans h)
  · exact Or.inr h

end CFSG.EvenSporadicStandard.HNRecog.Section3
