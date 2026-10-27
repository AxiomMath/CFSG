module

public import CFSG.LocalAnalysis.AGLEmbedding.IIIaLists

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms

theorem JStarElimData.card_psl2GF_dvd {L : Type} [Group L] [Finite L] {p n : ℕ} [Fact p.Prime]
    (h : JStarElimData L p n) :
    Nat.card (PSL2GF p n) ∣ Nat.card L * Nat.card (Outer L) := by
  obtain ⟨-, J, -, -, -, φ, hφ, -⟩ := h
  have h1 : Nat.card (PSL2GF p n) ∣ Nat.card (MulAut L) :=
    (Subgroup.card_dvd_of_surjective hφ).trans (Subgroup.card_subgroup_dvd_card J)
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (inner L), mul_comm] at h1
  exact h1.trans (mul_dvd_mul_right (Subgroup.card_range_dvd _) _)

theorem JStarElimData.dvd_card_mul {L : Type} [Group L] [Finite L] {p n : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hn : n ≠ 0) (h : JStarElimData L p n) :
    p ^ n * (((p ^ n) ^ 2 - 1) / 2) ∣ Nat.card L * Nat.card (Outer L) := by
  rw [← CFSG.SectionRank.OddCover.card_psl_two Fact.out hp2 (GaloisField.card p n hn)]
  exact h.card_psl2GF_dvd

theorem JStarElimData.pow_dvd_card {L : Type} [Group L] [Finite L] {p n : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hn : n ≠ 0) (hOut : ¬ p ∣ Nat.card (Outer L)) (h : JStarElimData L p n) :
    p ^ n ∣ Nat.card L :=
  (Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hOut)).dvd_of_dvd_mul_right
    ((Dvd.intro _ rfl).trans (h.dvd_card_mul hp2 hn))

theorem JStarElimData.dvd_card {L : Type} [Group L] [Finite L] {p n : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hn : n ≠ 0) (hOut : ∀ q : ℕ, q.Prime → q ≠ 2 → ¬ q ∣ Nat.card (Outer L))
    (h : JStarElimData L p n) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hqd : q ∣ (p ^ n) ^ 2 - 1) : q ∣ Nat.card L := by
  have hp : p.Prime := Fact.out
  have hodd : Odd ((p ^ n) ^ 2) := ((hp.odd_of_ne_two hp2).pow).pow
  have h2 : 2 * (((p ^ n) ^ 2 - 1) / 2) = (p ^ n) ^ 2 - 1 :=
    Nat.mul_div_cancel' (Nat.Odd.sub_odd hodd odd_one).two_dvd
  have hq' : q ∣ ((p ^ n) ^ 2 - 1) / 2 := by
    rw [← h2] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h) hq2
    · exact h
  rcases (Nat.Prime.dvd_mul hq).mp
      ((hq'.trans (Dvd.intro_left _ rfl)).trans (h.dvd_card_mul hp2 hn)) with h | h
  · exact h
  · exact absurd h (hOut q hq hq2)

theorem JStarElimData.pow_dvd_of_center_eq_bot {L : Type} [Group L] [Finite L] {p n : ℕ}
    [Fact p.Prime] (hZ : Subgroup.center L = ⊥) (h : JStarElimData L p n) {k : ℕ}
    (hk : p ^ k ∣ Nat.card L) : p ^ k ∣ p ^ n * n := by
  obtain ⟨A, -, hInn, -, hpA, -⟩ := h
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime p hk
  have hinj : Function.Injective (MulAut.conj : L →* MulAut L) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← hZ]
    refine le_antisymm (fun x hx => Subgroup.mem_center_iff.mpr fun g => ?_) ?_
    · have hxg : x * g * x⁻¹ = g := by
        simpa using congrArg (fun f : MulAut L => f g) (MonoidHom.mem_ker.mp hx)
      calc g * x = x * g * x⁻¹ * x := by rw [hxg]
        _ = x * g := by group
    · intro x hx
      rw [MonoidHom.mem_ker]
      ext g
      simp [(Subgroup.mem_center_iff.mp hx g).symm]
  have hcard : Nat.card (H.map (MulAut.conj : L →* MulAut L)) = p ^ k := by
    rw [Subgroup.card_map_of_injective hinj, hH]
  have hS := hpA _ ((Subgroup.map_le_range _ _).trans hInn) (IsPGroup.of_card hcard)
  rwa [hcard] at hS

theorem center_eq_bot_of_sq_dvd {G : Type*} [Group G] [IsSimpleGroup G] {q : ℕ}
    (hq : q.Prime) (h : q ^ 2 ∣ Nat.card G) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h' | h'
  · exact h'
  · exfalso
    have : IsMulCommutative G := ⟨⟨fun a b =>
      (Subgroup.mem_center_iff.mp (h' ▸ Subgroup.mem_top a : a ∈ Subgroup.center G) b).symm⟩⟩
    have hpr : (Nat.card G).Prime := Group.is_simple_iff_prime_card.mp inferInstance
    rcases hpr.eq_one_or_self_of_dvd q ((dvd_pow_self q two_ne_zero).trans h) with h1 | h1
    · exact hq.one_lt.ne' h1
    · rw [h1] at h
      have h2 := Nat.le_of_dvd hpr.pos h
      have h3 := hpr.two_le
      nlinarith

@[expose] def jStarSporBound : ℕ :=
  2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3 * 17 * 19 * 23 * 29 * 31 * 37 * 41 * 47 * 59 *
    67 * 71

theorem false_of_prime_dvd {p n N q : ℕ} (hN : N ∣ jStarSporBound)
    (h2 : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ (p ^ n) ^ 2 - 1 → r ∣ N) (hq : q.Prime)
    (hqd : q ∣ (p ^ n) ^ 2 - 1) (hqD : ¬ q ∣ jStarSporBound) : False :=
  hqD ((h2 q hq (by rintro rfl; exact hqD (by decide)) hqd).trans hN)

theorem le_four_of_orders_three {n N : ℕ} (hN : N ∣ jStarSporBound) (h1 : 3 ^ n ∣ N)
    (h2 : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ (3 ^ n) ^ 2 - 1 → q ∣ N) : n ≤ 4 := by
  have h20 : n ≤ 20 := by
    by_contra h
    exact (by decide : ¬ 3 ^ 21 ∣ jStarSporBound) ((pow_dvd_pow 3 (by omega)).trans (h1.trans hN))
  by_contra h4
  have h5 : 5 ≤ n := by omega
  have key := fun q (hq : q.Prime) hqd hqD => false_of_prime_dvd (q := q) hN h2 hq hqd hqD
  interval_cases n
  · exact key 61 (by norm_num) (by norm_num) (by decide)
  · exact key 73 (by norm_num) (by norm_num) (by decide)
  · exact key 547 (by norm_num) (by norm_num) (by decide)
  · exact key 193 (by norm_num) (by norm_num) (by decide)
  · exact key 757 (by norm_num) (by norm_num) (by decide)
  · exact key 61 (by norm_num) (by norm_num) (by decide)
  · exact key 661 (by norm_num) (by norm_num) (by decide)
  · exact key 73 (by norm_num) (by norm_num) (by decide)
  · exact key 398581 (by norm_num) (by norm_num) (by decide)
  · exact key 547 (by norm_num) (by norm_num) (by decide)
  · exact key 61 (by norm_num) (by norm_num) (by decide)
  · exact key 193 (by norm_num) (by norm_num) (by decide)
  · exact key 103 (by norm_num) (by norm_num) (by decide)
  · exact key 757 (by norm_num) (by norm_num) (by decide)
  · exact key 1597 (by norm_num) (by norm_num) (by decide)
  · exact key 61 (by norm_num) (by norm_num) (by decide)

theorem le_three_of_orders_five {n N : ℕ} (hN : N ∣ jStarSporBound) (h1 : 5 ^ n ∣ N)
    (h2 : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ (5 ^ n) ^ 2 - 1 → q ∣ N) : n ≤ 3 := by
  have h9 : n ≤ 9 := by
    by_contra h
    exact (by decide : ¬ 5 ^ 10 ∣ jStarSporBound) ((pow_dvd_pow 5 (by omega)).trans (h1.trans hN))
  by_contra h3
  have h4 : 4 ≤ n := by omega
  have key := fun q (hq : q.Prime) hqd hqD => false_of_prime_dvd (q := q) hN h2 hq hqd hqD
  interval_cases n
  · exact key 313 (by norm_num) (by norm_num) (by decide)
  · exact key 521 (by norm_num) (by norm_num) (by decide)
  · exact key 601 (by norm_num) (by norm_num) (by decide)
  · exact key 449 (by norm_num) (by norm_num) (by decide)
  · exact key 313 (by norm_num) (by norm_num) (by decide)
  · exact key 829 (by norm_num) (by norm_num) (by decide)

theorem false_of_orders_seven {n N : ℕ} (hn : 3 ≤ n) (hN : N ∣ jStarSporBound) (h1 : 7 ^ n ∣ N)
    (h2 : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ (7 ^ n) ^ 2 - 1 → q ∣ N) : False := by
  have h6 : n ≤ 6 := by
    by_contra h
    exact (by decide : ¬ 7 ^ 7 ∣ jStarSporBound) ((pow_dvd_pow 7 (by omega)).trans (h1.trans hN))
  have key := fun q (hq : q.Prime) hqd hqD => false_of_prime_dvd (q := q) hN h2 hq hqd hqD
  interval_cases n
  · exact key 43 (by norm_num) (by norm_num) (by decide)
  · exact key 1201 (by norm_num) (by norm_num) (by decide)
  · exact key 191 (by norm_num) (by norm_num) (by decide)
  · exact key 43 (by norm_num) (by norm_num) (by decide)

theorem false_of_orders_thirteen {n N : ℕ} (hn : 3 ≤ n) (hN : N ∣ jStarSporBound)
    (h1 : 13 ^ n ∣ N) (h2 : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ (13 ^ n) ^ 2 - 1 → q ∣ N) : False := by
  have h3 : n ≤ 3 := by
    by_contra h
    exact (by decide : ¬ 13 ^ 4 ∣ jStarSporBound)
      ((pow_dvd_pow 13 (by omega)).trans (h1.trans hN))
  obtain rfl : n = 3 := le_antisymm h3 hn
  exact false_of_prime_dvd (q := 61) hN h2 (by norm_num) (by norm_num) (by decide)

theorem false_of_orders_three {n N : ℕ} (hn : 3 ≤ n) (hN : N ∣ jStarSporBound) (h1 : 3 ^ n ∣ N)
    (h2 : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ (3 ^ n) ^ 2 - 1 → q ∣ N)
    (h3 : (¬ 13 ∣ N ∧ ¬ 41 ∣ N) ∨ 3 ^ 5 ∣ 3 ^ n * n) : False := by
  have h4 := le_four_of_orders_three hN h1 h2
  interval_cases n
  · rcases h3 with ⟨h13, -⟩ | h3
    · exact h13 (h2 13 (by norm_num) (by norm_num) (by norm_num))
    · exact absurd h3 (by decide)
  · rcases h3 with ⟨-, h41⟩ | h3
    · exact h41 (h2 41 (by norm_num) (by norm_num) (by norm_num))
    · exact absurd h3 (by decide)

theorem false_of_orders_five {n N : ℕ} (hn : 3 ≤ n) (hN : N ∣ jStarSporBound) (h1 : 5 ^ n ∣ N)
    (h2 : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ (5 ^ n) ^ 2 - 1 → q ∣ N)
    (h3 : ¬ 31 ∣ N ∨ 5 ^ 4 ∣ 5 ^ n * n) : False := by
  obtain rfl : n = 3 := le_antisymm (le_three_of_orders_five hN h1 h2) hn
  rcases h3 with h31 | h3
  · exact h31 (h2 31 (by norm_num) (by norm_num) (by norm_num))
  · exact absurd h3 (by decide)

theorem not_jStarElimData_of_card {L : Type} [Group L] [Finite L] {p n N : ℕ} [Fact p.Prime]
    (hn : 3 ≤ n) (hN : Nat.card L = N) (hND : N ∣ jStarSporBound)
    (hOut : ∀ q : ℕ, q.Prime → q ≠ 2 → ¬ q ∣ Nat.card (Outer L))
    (hcase : (p = 3 ∧ ((¬ 13 ∣ N ∧ ¬ 41 ∣ N) ∨ (Subgroup.center L = ⊥ ∧ 3 ^ 5 ∣ N))) ∨
      (p = 5 ∧ (¬ 31 ∣ N ∨ (Subgroup.center L = ⊥ ∧ 5 ^ 4 ∣ N))) ∨ p = 7 ∨ p = 13) :
    ¬ JStarElimData L p n := by
  intro h
  have hn0 : n ≠ 0 := by omega
  rcases hcase with ⟨rfl, hc⟩ | ⟨rfl, hc⟩ | rfl | rfl
  · have h1 := h.pow_dvd_card (by norm_num) hn0 (hOut 3 Nat.prime_three (by norm_num))
    rw [hN] at h1
    refine false_of_orders_three hn hND h1 (fun q hq hq2 hqd => ?_) ?_
    · exact hN ▸ h.dvd_card (by norm_num) hn0 hOut hq hq2 hqd
    · rcases hc with hc | ⟨hZ, h5⟩
      · exact Or.inl hc
      · exact Or.inr (h.pow_dvd_of_center_eq_bot hZ (hN ▸ h5))
  · have h1 := h.pow_dvd_card (by norm_num) hn0 (hOut 5 Nat.prime_five (by norm_num))
    rw [hN] at h1
    refine false_of_orders_five hn hND h1 (fun q hq hq2 hqd => ?_) ?_
    · exact hN ▸ h.dvd_card (by norm_num) hn0 hOut hq hq2 hqd
    · rcases hc with hc | ⟨hZ, h5⟩
      · exact Or.inl hc
      · exact Or.inr (h.pow_dvd_of_center_eq_bot hZ (hN ▸ h5))
  · have h1 := h.pow_dvd_card (by norm_num) hn0 (hOut 7 (by norm_num) (by norm_num))
    rw [hN] at h1
    exact false_of_orders_seven hn hND h1 fun q hq hq2 hqd =>
      hN ▸ h.dvd_card (by norm_num) hn0 hOut hq hq2 hqd
  · have h1 := h.pow_dvd_card (by norm_num) hn0 (hOut 13 (by norm_num) (by norm_num))
    rw [hN] at h1
    exact false_of_orders_thirteen hn hND h1 fun q hq hq2 hqd =>
      hN ▸ h.dvd_card (by norm_num) hn0 hOut hq hq2 hqd

theorem not_jStarElimData_of_mulEquiv {L S : Type} [Group L] [Finite L] [Group S] {p n N : ℕ}
    [Fact p.Prime] (g : L ≃* S) (hn : 3 ≤ n) (hN : Nat.card S = N) (hND : N ∣ jStarSporBound)
    (hOut : ∀ q : ℕ, q.Prime → q ≠ 2 → ¬ q ∣ Nat.card (Outer L))
    (hcase : (p = 3 ∧ ((¬ 13 ∣ N ∧ ¬ 41 ∣ N) ∨ (IsSimpleGroup S ∧ 3 ^ 5 ∣ N))) ∨
      (p = 5 ∧ (¬ 31 ∣ N ∨ (IsSimpleGroup S ∧ 5 ^ 4 ∣ N))) ∨ p = 7 ∨ p = 13) :
    ¬ JStarElimData L p n := by
  have hL : Nat.card L = N := (Nat.card_congr g.toEquiv).trans hN
  have hZ {q k : ℕ} (hq : q.Prime) (hS : IsSimpleGroup S) (hk : 2 ≤ k) (hqk : q ^ k ∣ N) :
      Subgroup.center L = ⊥ := by
    have : IsSimpleGroup L := g.isSimpleGroup
    exact center_eq_bot_of_sq_dvd hq (hL ▸ (pow_dvd_pow q hk).trans hqk)
  refine not_jStarElimData_of_card hn hL hND hOut ?_
  rcases hcase with ⟨rfl, hc | ⟨hS, h5⟩⟩ | ⟨rfl, hc | ⟨hS, h4⟩⟩ | rfl | rfl
  · exact Or.inl ⟨rfl, Or.inl hc⟩
  · exact Or.inl ⟨rfl, Or.inr ⟨hZ Nat.prime_three hS (by norm_num) h5, h5⟩⟩
  · exact Or.inr (Or.inl ⟨rfl, Or.inl hc⟩)
  · exact Or.inr (Or.inl ⟨rfl, Or.inr ⟨hZ Nat.prime_five hS (by norm_num) h4, h4⟩⟩)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

end CFSG.AGLEmbedding
