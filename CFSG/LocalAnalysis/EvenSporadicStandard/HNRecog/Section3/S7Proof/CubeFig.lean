module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Perm
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Decomp
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.Hyps

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem s7_fig_cases {a z b t : G} (H : S7Hyps a z) (hb : b ∈ orb2A a a)
    (ht : t ∈ derivedOf (Gxy a b)) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) :
    (IsConj a t ∧ IsConj z (a * t) ∧ IsConj z (b * t) ∧ IsConj z (a * b * t)) ∨
    (IsConj z t ∧ IsConj a (a * t) ∧ IsConj a (b * t) ∧ IsConj a (a * b * t)) := by
  obtain ⟨φ⟩ := nonempty_mulEquiv_derivedOf_of_isShapeTwoTwoTimesA8 (H.fusion3.self.shape_2A b hb)
  let u : ↥(derivedOf (Gxy a b)) := ⟨t, ht⟩
  obtain ⟨s, hs⟩ := φ.surjective u
  have hφ : (φ s : G) = t := by rw [hs]
  have hu2 : u ^ 2 = 1 := by
    apply Subtype.ext
    simpa [u] using ht2
  have hs2 : s ^ 2 = 1 := by
    apply φ.injective
    rw [map_pow, map_one, hs]
    exact hu2
  have hs1 : s ≠ 1 := by
    intro hs1
    apply ht1
    have h1 : u = 1 := by rw [← hs, hs1, map_one]
    have h1' : (u : G) = 1 := by rw [h1]; rfl
    simpa [u] using h1'
  rcases cycleType_eq_of_sq_eq_one hs2 hs1 with hct | hct
  · left
    simpa [hφ] using H.pic.self.fig8a b hb φ s hct
  · right
    simpa [hφ] using H.pic.self.fig8b b hb φ s hct

end CFSG.EvenSporadicStandard.HNRecog.Section3
