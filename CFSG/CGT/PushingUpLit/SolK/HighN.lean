module

public import CFSG.CGT.PushingUpLit.SolK.TwoD

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

namespace SolCfg

include S

theorem centInM_of_four_le (hT : TightData S) (hQe : QElem S) (hR : RSmall S) (hn4 : 4 ≤ n) :
    CentInM S := by
  intro x hx hx1 k hk
  obtain ⟨l, hl⟩ := S.exists_hasLen hx
  have hkC : k ∈ CGOf x := by
    rw [CGOf, ← centralizer_singleton_eq_zpowers]
    exact hk
  by_cases hl2 : l = 2
  · subst hl2
    obtain ⟨w, hw, r, hr, rfl, hcard⟩ := hl
    exact S.centralizer_le_M_of_len_two hT hQe hR hn4 hw hr hcard hkC
  · exact S.hAway_of_four_le hT hQe hR hn4 x hx hx1 (fun h2 => hl2 (SolCfg.HasLen.unique S hl h2)) k
      (mem_centralizer_zpowers_iff.1 hkC)

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
