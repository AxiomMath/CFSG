module

public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG

theorem pRank_le_one_of_isCyclic {G : Type} [Group G] [Finite G] {p : Nat} (hp : p.Prime)
    (hG : IsCyclic G) : CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 1 := by
  haveI : IsCyclic G := hG
  refine CFSG.SectionRank.pRank_le hp.one_lt (H := ⊤) (k := 1) ?_
  intro E _ hE
  haveI : IsCyclic E := inferInstance
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic E)
  have hcard : Nat.card E = orderOf g := (orderOf_eq_card_of_zpowers_eq_top hg).symm
  have hgp : g ^ p = 1 := by
    ext
    exact hE.2 (g : G) g.2
  have hdvd : orderOf g ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hgp
  rw [hcard]
  simpa only [pow_one] using Nat.le_of_dvd hp.pos hdvd

end CFSG

end
