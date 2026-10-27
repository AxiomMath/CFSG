module

public import CFSG.GH74.Uniqueness.SU.SU13TB3E
public import CFSG.GH74.Uniqueness.SU.SU13TB2Ord
public import CFSG.GH74.Uniqueness.SU.SU13TB3Fin

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB CFSG.GH74

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem false_of_loc10_of_ki8b (hKI7d : K.KI7d) (hKI8b : K.KI8b)
    (hnab : ∃ a b : G, a * b ≠ b * a) {z : G} (hz : orderOf z = 2)
    (hH : K.IsTwoAlt ↥(centralizer ({z} : Set G)) 10) (loc : Loc10 G z) : False := by
  have l : Lem232 z loc.e := lemma232_ten hnab hz loc.e loc.f loc.p3 loc.m
  obtain ⟨R, hR, hzR, hRz⟩ := l.R
  obtain ⟨-, h35⟩ := order_Y_ten hKI8b hz loc.e loc.m l.one hR hzR hRz l.k₁ l.k₂
  have hoc := oc_eq_zpowers hKI7d hH hz loc.e loc.f l
  exact false_of_oc_eq hz loc.e l loc.E hoc h35

end CFSG.GH74.Uniqueness.SU.SU13
