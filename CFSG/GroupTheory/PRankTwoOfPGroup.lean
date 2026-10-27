module

public import CFSG.GroupTheory.PGroup.RankTwoCommute

public section

namespace CFSG

theorem one_lt_pRank_of_isPGroup {D : Type} [Group D] [Finite D] {p : Nat} (hp : p.Prime)
    (hD : IsPGroup p D) (hcard : p < Nat.card D) (hDexp : ∀ x : D, x ^ p = 1) :
    1 < CFSG.Open.pRank p (⊤ : Subgroup D) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hnt : Nontrivial D :=
    Finite.one_lt_card_iff_nontrivial.mp (lt_trans hp.one_lt hcard)
  obtain ⟨c, hc_mem, hc_ne⟩ :=
    (Subgroup.nontrivial_iff_exists_ne_one (Subgroup.center D)).mp hD.center_nontrivial
  have hcord : orderOf c = p := orderOf_eq_prime (hDexp c) hc_ne
  have hnotle : ¬ (⊤ : Subgroup D) ≤ Subgroup.zpowers c := by
    intro h
    have htop : Subgroup.zpowers c = ⊤ := le_antisymm le_top h
    have hcard' : Nat.card (Subgroup.zpowers c) = Nat.card D := by
      rw [htop, Subgroup.card_top]
    rw [Nat.card_zpowers, hcord] at hcard'
    omega
  obtain ⟨y, -, hyc⟩ := SetLike.not_le_iff_exists.mp hnotle
  have hy_ne : y ≠ 1 := by
    intro h
    exact hyc (h ▸ Subgroup.one_mem (Subgroup.zpowers c))
  have hyord : orderOf y = p := orderOf_eq_prime (hDexp y) hy_ne
  have hcomm : Commute c y := by
    rw [Commute]
    exact (Subgroup.mem_center_iff.mp hc_mem y).symm
  exact CFSG.GroupTheory.two_le_pRank_of_commute (p := p) (H := ⊤) (x := c) (y := y)
    (Subgroup.mem_top c) (Subgroup.mem_top y) hcord hyord hcomm hyc

end CFSG
