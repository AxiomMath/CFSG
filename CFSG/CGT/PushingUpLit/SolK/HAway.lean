module

public import CFSG.CGT.PushingUpLit.SolK.FourE
public import CFSG.CGT.PushingUpLit.SolK.LocalTI

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

namespace SolCfg

include S

theorem hAway_of_four_le (hT : TightData S) (hQe : QElem S) (hR : RSmall S) (hn4 : 4 ≤ n) :
    S.HAway := by
  intro z hz hz1 hlen k hk
  obtain ⟨l, hl⟩ := S.exists_hasLen hz
  have hkC : k ∈ CGOf z := mem_centralizer_zpowers_iff.2 hk
  by_cases hl4 : l = 4
  · subst hl4
    obtain ⟨w, hw, r, hr, rfl, hcard⟩ := hl
    exact S.centralizer_le_M_of_len_four hT hQe hR hw hr hcard hn4 hkC
  · have hl2 : l ≠ 2 := fun h2 => hlen (h2 ▸ hl)
    exact (S.centralizer_eq_of_len S.hyp.charTwo hT hz hz1 hl hl2 hl4).2
      (Subgroup.centralizer_le_normalizer _ hkC)

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
