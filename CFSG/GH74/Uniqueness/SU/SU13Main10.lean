module

public import CFSG.GH74.Uniqueness.SU.SU13Ten
public import CFSG.GH74.Uniqueness.SU.SU13TA3Final

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74

theorem thm231_ten_of_ki8b (hKI7d : K.KI7d) (hKI8b : K.KI8b) (G : Type) [Group G] [Finite G]
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) (z : G)
    (hz : orderOf z = 2) : ¬ K.IsTwoAlt ↥(centralizer ({z} : Set G)) 10 := by
  intro hH
  obtain ⟨loc⟩ := loc10_of_isTwoAlt hz hH
  exact false_of_loc10_of_ki8b hKI7d hKI8b hnab hz hH loc

end CFSG.GH74.Uniqueness.SU.SU13
