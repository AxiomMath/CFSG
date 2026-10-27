module

public import CFSG.Quasithin.H13.L32AC52b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk2

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open Equiv Equiv.Perm

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem kstar_cases_F4 (h47 : Lemma14_7_47_F4) (h49 : Lemma14_7_49_F4) (h50 : Lemma14_7_50_F4)
    (h51 : Lemma14_7_51_F4) (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H) :
    IsAlt 5 (cStar K) ∨ IsPSU 3 3 1 (cStar K) := by
  rcases (h47 _ T L V H S K hK).2 with ⟨n, hP⟩ | ⟨n, hA⟩ | hU
  · exact absurd hP (h51 _ T L V H S K hK n)
  · rcases (by omega : n ≤ 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ 9 ≤ n) with
      hn | rfl | rfl | rfl | rfl | hn
    · exact (false_of_alt_small hK hn hA).elim
    · exact Or.inl hA
    · exact absurd hA (h49 _ T L V H S K hK).2
    · exact absurd hA (h50 _ T L V H S K hK)
    · obtain ⟨φ⟩ := hA
      exact absurd (Lin.isPSL_of_mulEquiv (m := 4) (by norm_num)
        (φ.trans Lin.slFourEquivAlt8.symm)) (h51 _ T L V H S K hK 4)
    · exact (false_of_alt_nine_le S hK hn hA).elim
  · exact Or.inr hU

end CFSG.Quasithin.H13.L32A.C
