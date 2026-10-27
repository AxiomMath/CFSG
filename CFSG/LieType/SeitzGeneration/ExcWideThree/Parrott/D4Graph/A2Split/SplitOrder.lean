module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Split.Torus3

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Timmesfeld.ExceptionalOrders CFSG.LieType.SeitzGeneration.ExcWideThree

section Units

variable {K : Type} [Field K] [Finite K]

theorem card_units_K : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K

theorem exists_orderOf_eq_three_pow :
    ∃ ζ : Kˣ, orderOf ζ = 3 ^ (Nat.card K - 1).factorization 3 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [card_units_K] at hg
  set N := Nat.card K - 1 with hN
  have hN0 : N ≠ 0 := by
    have h := Nat.card_pos (α := Kˣ)
    rw [card_units_K] at h
    omega
  have hd : 3 ^ N.factorization 3 ∣ N := Nat.ordProj_dvd N 3
  have hd' : N / 3 ^ N.factorization 3 ∣ N := Nat.div_dvd_of_dvd hd
  have hpos : 0 < N / 3 ^ N.factorization 3 :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hd) (by positivity)
  refine ⟨g ^ (N / 3 ^ N.factorization 3), ?_⟩
  rw [orderOf_pow_of_dvd hpos.ne' (hg ▸ hd'), hg, Nat.div_div_self hd hN0]

theorem mu_sq {ζ : Kˣ} {n : ℕ} (hn : Odd n) (hζ : orderOf ζ = n) :
    ∀ u ∈ Subgroup.zpowers ζ, ∃ b : Kˣ, u = b ^ 2 := by
  intro u hu
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
  refine exists_sq_of_pow_odd hn ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hζ, pow_orderOf_eq_one,
    one_zpow]

end Units

section Order

theorem geomSum_mod (n q m : ℕ) :
    geomSum n 1 q % m = (∑ i ∈ Finset.range n, (q % m) ^ i) % m := by
  simp only [geomSum, one_mul]
  rw [Finset.sum_nat_mod]
  conv_rhs => rw [Finset.sum_nat_mod]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.pow_mod]

theorem geomSum_two_mod (q : ℕ) (hq : q % 3 = 1) : ¬ 3 ∣ geomSum 2 1 q := by
  intro h
  have h' := Nat.mod_eq_zero_of_dvd h
  rw [geomSum_mod, hq] at h'
  norm_num [Finset.sum_range_succ] at h'

theorem geomSum_four_mod (q : ℕ) (hq : q % 3 = 1) : ¬ 3 ∣ geomSum 4 1 q := by
  intro h
  have h' := Nat.mod_eq_zero_of_dvd h
  rw [geomSum_mod, hq] at h'
  norm_num [Finset.sum_range_succ] at h'

theorem geomSum_six_mod (q : ℕ) (hq : q % 3 = 1) : ¬ 9 ∣ geomSum 6 1 q := by
  intro h
  have h' := Nat.mod_eq_zero_of_dvd h
  rw [geomSum_mod] at h'
  have h9 : q % 9 = 1 ∨ q % 9 = 4 ∨ q % 9 = 7 := by omega
  rcases h9 with h9 | h9 | h9 <;> rw [h9] at h' <;> norm_num [Finset.sum_range_succ] at h'

variable {K : Type} [Field K] [Finite K]

theorem factorization_card_D4_le (hq : Nat.card K % 3 = 1) :
    (Nat.card (adjointGroup Tag.D4 K)).factorization 3 ≤
      4 * (Nat.card K - 1).factorization 3 + 1 := by
  have hq0 := Nat.card_pos (α := K)
  set q := Nat.card K with hqdef
  have hH : Nat.card (torusGroup Tag.D4 K) ∣ (q - 1) ^ 4 :=
    Dvd.intro _ (card_torusGroup_mul (τ := Tag.D4) (K := K))
  have hH0 : Nat.card (torusGroup Tag.D4 K) ≠ 0 := Nat.card_pos.ne'
  have hq1 : 1 < q := Finite.one_lt_card
  have hq10 : q - 1 ≠ 0 := by omega
  have h2 : geomSum 2 1 q ≠ 0 := by simp [geomSum, Finset.sum_range_succ]
  have h4 : geomSum 4 1 q ≠ 0 := by simp [geomSum, Finset.sum_range_succ]
  have h6 : geomSum 6 1 q ≠ 0 := by simp [geomSum, Finset.sum_range_succ]
  have hq12 : q ^ 12 ≠ 0 := pow_ne_zero _ hq0.ne'
  rw [card_adjointGroup_D4_eq]
  rw [Nat.factorization_mul (Nat.mul_ne_zero hH0 hq12)
      (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero h2 h4) h4) h6),
    Nat.factorization_mul hH0 hq12,
    Nat.factorization_mul (Nat.mul_ne_zero (Nat.mul_ne_zero h2 h4) h4) h6,
    Nat.factorization_mul (Nat.mul_ne_zero h2 h4) h4, Nat.factorization_mul h2 h4]
  simp only [Finsupp.add_apply]
  have eH : (Nat.card (torusGroup Tag.D4 K)).factorization 3 ≤ 4 * (q - 1).factorization 3 := by
    have := (Nat.factorization_le_iff_dvd hH0 (pow_ne_zero 4 hq10)).2 hH 3
    rwa [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at this
  have eq12 : (q ^ 12).factorization 3 = 0 := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_eq_zero_of_not_dvd (by omega : ¬ 3 ∣ q), mul_zero]
  have e2 : (geomSum 2 1 q).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (geomSum_two_mod q hq)
  have e4 : (geomSum 4 1 q).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (geomSum_four_mod q hq)
  have e6 : (geomSum 6 1 q).factorization 3 ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have := (Nat.prime_three.pow_dvd_iff_le_factorization h6).2 hlt
    exact geomSum_six_mod q hq (by simpa using this)
  omega

end Order

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
