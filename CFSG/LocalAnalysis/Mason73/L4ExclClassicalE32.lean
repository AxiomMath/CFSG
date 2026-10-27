module

public import CFSG.LocalAnalysis.Mason73.L4SylowTransport
public import CFSG.RankThree.PartOne.SLB4A.TypeA
public import CFSG.RankThree.PartOne.SLB4A.TypeSU
public import CFSG.RankThree.PartOne.SLB4A.ClassSp
public import CFSG.RankThree.PartOne.SLB4A.OrthB
public import CFSG.RankThree.PartOne.SLB4A.OrthD

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.Open CFSG.RankThree.PartOne.SLB4A

variable {G : Type} [Group G] [Finite G] {n r p f : ℕ}

theorem natCard_mod_two_of_eq_pow {K : Type} [Field K] [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) : Nat.card K % 2 = 1 := by
  rw [hK]
  exact Nat.odd_iff.1 ((hp.eq_two_or_odd'.resolve_left hp2).pow)

theorem exists_unit_sq_neg_one_of_mod_four_three {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : q % 4 = 3) :
    ∃ u : Kˣ, (u : K) * u = -1 ∧ (u : K) ^ q * u = 1 := by
  have hK4 : Nat.card K % 4 = 1 := by
    rw [hK, Nat.pow_mod, hq]
  obtain ⟨u, hu⟩ := exists_sq_neg_one K hK4
  refine ⟨u, hu, ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, q = 4 * k + 3 := ⟨q / 4, by omega⟩
  have h4 : (u : K) ^ 4 = 1 := by
    calc (u : K) ^ 4 = ((u : K) * u) * ((u : K) * u) := by ring
      _ = 1 := by rw [hu]; ring
  calc (u : K) ^ (4 * k + 3) * u = ((u : K) ^ 4) ^ (k + 1) := by ring
    _ = 1 := by rw [h4, one_pow]

theorem false_of_lieModel_psl_of_l4Sylow (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : CFSG.Blueprint.LieModel G .PSL r p f) (hr : 7 ≤ r ∨ (r = 6 ∧ p ^ f % 4 = 1)) :
    False := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hL.statedClassicalModel (by decide)
  have hodd := natCard_mod_two_of_eq_pow hp hp2 hK
  rcases hr with hr | ⟨rfl, hq⟩
  · obtain ⟨U, hU, hc⟩ := exists_two_pow_five_psl_odd r hr (neg_one_ne_one_of_card_odd K hodd)
    exact false_of_elementary_abelian_of_l4Sylow_of_mulEquiv hn P hP e U hc
  · obtain ⟨u, hu⟩ := exists_sq_neg_one K (by rw [hK]; exact hq)
    obtain ⟨U, hU, hc⟩ := exists_two_pow_five_psl_six (neg_one_ne_one_of_card_odd K hodd) u hu
    exact false_of_elementary_abelian_of_l4Sylow_of_mulEquiv hn P hP e U hc

theorem false_of_lieModel_psu_of_l4Sylow (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : CFSG.Blueprint.LieModel G .PSU r p f) (hr : 7 ≤ r ∨ (r = 6 ∧ p ^ f % 4 = 3)) :
    False := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hL.statedClassicalModel (by decide)
  have hqodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hodd : Nat.card K % 2 = 1 := by
    rw [hK]
    exact Nat.odd_iff.1 hqodd.pow
  rcases hr with hr | ⟨rfl, hq⟩
  · obtain ⟨U, hU, hc⟩ :=
      exists_two_pow_five_psu_odd hqodd r hr (neg_one_ne_one_of_card_odd K hodd)
    exact false_of_elementary_abelian_of_l4Sylow_of_mulEquiv hn P hP e U hc
  · obtain ⟨u, hu, huq⟩ := exists_unit_sq_neg_one_of_mod_four_three hK hq
    obtain ⟨U, hU, hc⟩ :=
      exists_two_pow_five_psu_six hqodd (neg_one_ne_one_of_card_odd K hodd) u hu huq
    exact false_of_elementary_abelian_of_l4Sylow_of_mulEquiv hn P hP e U hc

theorem false_of_lieModel_psp_of_l4Sylow (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) (hp : p.Prime)
    (hL : CFSG.Blueprint.LieModel G .PSp r p f) (hr : 4 ≤ r) : False := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hL.statedClassicalModel (by decide)
  obtain ⟨U, hU, hc⟩ := exists_two_pow_five_psp hp hK hr
  exact false_of_elementary_abelian_of_l4Sylow_of_mulEquiv hn P hP e U hc

theorem false_of_lieModel_pOmegaOdd_of_l4Sylow (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : CFSG.Blueprint.LieModel G .POmegaOdd r p f) (hr : 3 ≤ r) : False := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hL.statedClassicalModel (by decide)
  have hodd := natCard_mod_two_of_eq_pow hp hp2 hK
  obtain ⟨U, hU, hc⟩ := exists_two_pow_five_pomega_odd r hr (two_ne_zero_of_card_odd K hodd)
  exact false_of_elementary_abelian_of_l4Sylow_of_mulEquiv hn P hP e U hc

theorem false_of_lieModel_pOmegaPlus_of_l4Sylow (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : CFSG.Blueprint.LieModel G .POmegaPlus r p f) (hr : 4 ≤ r) : False := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hL.statedClassicalModel (by decide)
  have hodd := natCard_mod_two_of_eq_pow hp hp2 hK
  obtain ⟨U, hU, hc⟩ :=
    exists_two_pow_five_pomega_plus_odd r hr (two_ne_zero_of_card_odd K hodd)
  exact false_of_elementary_abelian_of_l4Sylow_of_mulEquiv hn P hP e U hc

theorem false_of_lieModel_pOmegaMinus_of_l4Sylow (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : CFSG.Blueprint.LieModel G .POmegaMinus r p f) (hr : 4 ≤ r) : False := by
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hL.statedClassicalModel (by decide)
  have hodd := natCard_mod_two_of_eq_pow hp hp2 hK
  obtain ⟨U, hU, hc⟩ :=
    exists_two_pow_five_pomega_minus_odd r hr b c hirr (two_ne_zero_of_card_odd K hodd)
  exact false_of_elementary_abelian_of_l4Sylow_of_mulEquiv hn P hP e U hc

end CFSG.LocalAnalysis.Mason73
