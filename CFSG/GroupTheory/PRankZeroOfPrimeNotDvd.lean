module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG

theorem pRank_eq_zero_of_not_dvd_card {G : Type} [Group G] [Finite G] {p : Nat} (hp : p.Prime)
    (h : ¬ p ∣ Nat.card G) : CFSG.Open.pRank p (⊤ : Subgroup G) = 0 := by
  refine le_antisymm ?_ (Nat.zero_le _)
  refine CFSG.SectionRank.pRank_le hp.one_lt (k := 0) (fun E _ hE => ?_)
  rw [pow_zero]
  haveI : Fact p.Prime := ⟨hp⟩
  rcases hE.isPGroup.card_eq_or_dvd with h1 | hdvd
  · exact h1.le
  · exact absurd (hdvd.trans (Subgroup.card_subgroup_dvd_card E)) h

theorem one_le_pRank_of_dvd_card {G : Type} [Group G] [Finite G] {p : Nat} (hp : p.Prime)
    (h : p ∣ Nat.card G) : 1 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := G) p h
  have hx : x ^ p = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
  have hE : CFSG.Open.IsElemAbelian p (Subgroup.zpowers x) :=
    CFSG.Open.isElemAbelian_zpowers hx
  have hcard : Nat.card (Subgroup.zpowers x) = p ^ 1 := by
    rw [Nat.card_zpowers, hxord, pow_one]
  exact CFSG.SectionRank.le_pRank hp.one_lt (H := ⊤) le_top hE hcard

end CFSG
