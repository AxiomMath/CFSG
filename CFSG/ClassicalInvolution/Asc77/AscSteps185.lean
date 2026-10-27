module

public import CFSG.ClassicalInvolution.Asc77.ModOApi
public import CFSG.ClassicalInvolution.Asc77.WP1Section18

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

theorem exists_orderOf_eq_four_of_isPGroup_of_isCyclic {G : Type} [Group G] [Finite G]
    {C : Subgroup G} (hC : IsPGroup 2 C) (hcyc : IsCyclic C) (h4 : 4 ≤ Nat.card C) :
    ∃ x ∈ C, orderOf x = 4 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥C)
  have hgord : orderOf g = Nat.card C := orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨n, hn⟩ := hC.exists_card_eq
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn2
  refine ⟨((g ^ 2 ^ m : ↥C) : G), (g ^ 2 ^ m).2, ?_⟩
  have hdvd : 2 ^ m ∣ orderOf g := by
    rw [hgord, hn]
    exact pow_dvd_pow 2 (by omega)
  rw [Subgroup.orderOf_coe, orderOf_pow_of_dvd (by positivity) hdvd, hgord, hn, pow_add,
    Nat.mul_div_cancel_left _ (by positivity)]
  norm_num

theorem HypOmegaMod.exists_orderOf_eq_four_of_mem_RSet {G : Type} [Group G] [Finite G] {p f : ℕ}
    [Fact p.Prime] {Ω : Set (Subgroup G)} (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {R : Subgroup G}
    (hR : R ∈ RSet Ω) : ∃ u ∈ R, orderOf u = 4 := by
  have hquat := hΩ.isQuatSub_of_mem_RSet hp hR
  obtain ⟨C, hCR, hC, hcard, -⟩ := hquat.exists_cyclic_max
  obtain ⟨J, -, -, hR2, -⟩ := mem_RSet_iff.mp hR
  have h8 := hquat.eight_le
  obtain ⟨x, hxC, hx⟩ := exists_orderOf_eq_four_of_isPGroup_of_isCyclic (hR2.to_le hCR) hC
    (by omega)
  exact ⟨x, hCR hxC, hx⟩

variable (p f : ℕ) [Fact p.Prime]

theorem e18_5 (h2 : E18_2 p f) (h4 : E18_4 p f) : E18_5 p f := by
  intro G _ _ Ω K S R W H c
  by_contra hX
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  obtain ⟨K', hK'tw, hK'ne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  have hKX : K ≤ ⨆ J ∈ Ω, J := le_iSup₂_of_le K c.stand.mem le_rfl
  have hK'X : K' ≤ ⨆ J ∈ Ω, J := le_iSup₂_of_le K' hK'tw.1 le_rfl
  have hXH : (⨆ J ∈ Ω, J) ≤ H :=
    h4 G Ω K S R W H c K' hK'tw hK'ne R' hR' hR'K' hR'S _
      (sup_le (hRK.trans hKX) (hR'K'.trans hK'X)) hX
  obtain ⟨u, huR, hu4⟩ := hΩ.exists_orderOf_eq_four_of_mem_RSet c.stand.odd hRR
  refine c.proper (eq_top_iff.mpr fun g _ => ?_)
  have hle : conjSub g K ≤ ⨆ J ∈ Ω, J :=
    le_iSup₂_of_le (conjSub g K) (hΩ.conjInvariant g K c.stand.mem) le_rfl
  exact h2 G Ω K S R W H c u (hRK huR) hu4 g (hXH (hle (conj_mem_conjSub (hRK huR))))

end CFSG.ClassicalInvolution.Asc77
