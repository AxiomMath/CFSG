module

public import CFSG.LieType.Chevalley.ChevalleySplitBN
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.GLValuation

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Timmesfeld.ExceptionalOrders CFSG.Open CFSG.HardMathSupport.Timmesfeld.LinearRank

section Arith

theorem factorization_three_numerator_E6 {q : ℕ} (hq : 1 < q) (h3 : 3 ∣ q - 1) :
    (q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) *
      (q ^ 2 - 1)).factorization 3 = 6 * (q - 1).factorization 3 + 4 := by
  have key : ∀ d : ℕ, d ≠ 0 →
      (q ^ d - 1).factorization 3 = (q - 1).factorization 3 + d.factorization 3 :=
    fun d hd => factorization_pow_sub_one Nat.prime_three (by norm_num) hq h3 hd
  have hne : ∀ d : ℕ, d ≠ 0 → q ^ d - 1 ≠ 0 := fun d hd => by
    have := Nat.one_lt_pow hd hq
    omega
  have hq0 : q ^ 36 ≠ 0 := pow_ne_zero _ (by omega)
  have f12 : (12 : ℕ).factorization 3 = 1 := by decide +kernel
  have f9 : (9 : ℕ).factorization 3 = 2 := by decide +kernel
  have f8 : (8 : ℕ).factorization 3 = 0 := by decide +kernel
  have f6 : (6 : ℕ).factorization 3 = 1 := by decide +kernel
  have f5 : (5 : ℕ).factorization 3 = 0 := by decide +kernel
  have f2 : (2 : ℕ).factorization 3 = 0 := by decide +kernel
  have h12 := hne 12 (by norm_num)
  have h9 := hne 9 (by norm_num)
  have h8 := hne 8 (by norm_num)
  have h6 := hne 6 (by norm_num)
  have h5 := hne 5 (by norm_num)
  have h2 := hne 2 (by norm_num)
  have k12 := key 12 (by norm_num)
  have k9 := key 9 (by norm_num)
  have k8 := key 8 (by norm_num)
  have k6 := key 6 (by norm_num)
  have k5 := key 5 (by norm_num)
  have k2 := key 2 (by norm_num)
  have h3q : (q ^ 36).factorization 3 = 0 := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_eq_zero_of_not_dvd (not_dvd_of_dvd_sub_one Nat.prime_three hq h3), mul_zero]
  simp only [Nat.factorization_mul, mul_ne_zero_iff, ne_eq, hq0, h12, h9, h8, h6, h5, h2,
    not_false_eq_true, and_self, Finsupp.add_apply, h3q, k12, k9, k8, k6, k5, k2, f12, f9, f8,
    f6, f5, f2]
  ring

theorem factorization_three_mul_51840 {q : ℕ} (h3 : 3 ∣ q - 1) (hq : 1 < q) :
    ((q - 1) ^ 6 * 51840).factorization 3 = 6 * (q - 1).factorization 3 + 4 := by
  have h0 : q - 1 ≠ 0 := by omega
  have h : (51840 : ℕ).factorization 3 = 4 := by decide +kernel
  rw [Nat.factorization_mul (pow_ne_zero _ h0) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, h]

end Arith

section Index

variable {K : Type} [Field K] [Finite K]

theorem card_weylGroup_E6 : Nat.card (WeylGroup .E6) = 51840 := by
  classical
  have : Fintype (WeylGroup .E6) := Fintype.ofFinite _
  have h := sum_length_E6 1
  simp only [one_pow, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ] at h
  rw [Nat.card_eq_fintype_card, h]
  simp [geomSum]

omit [Finite K] in
theorem card_torusSub_E6 :
    Nat.card (torusSub .E6 K) = Nat.card (torusGroup .E6 K) :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (torusGroup_le_borelGroup.trans borelGroup_le_adjointGroup')).toEquiv

omit [Finite K] in
theorem card_monomialSub_E6 :
    Nat.card (monomialSub .E6 K) = Nat.card (torusGroup .E6 K) * 51840 := by
  have h := Subgroup.card_ker_mul_card_range (monomialSubHom (τ := .E6) (K := K))
  rw [MonoidHom.range_eq_top.2 monomialSubHom_surjective, Subgroup.card_top,
    card_weylGroup_E6, monomialSubHom_ker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : borelSub .E6 K ⊓ monomialSub .E6 K ≤ monomialSub .E6 K)).toEquiv,
    borelSub_inf_monomialSub, card_torusSub_E6] at h
  exact h.symm

theorem index_monomialSub_not_dvd_three (h3 : 3 ∣ Nat.card K - 1) :
    ¬ 3 ∣ (monomialSub .E6 K).index := by
  have hfin : Finite (adjointGroup .E6 K) := generated_group_finite .E6 K
  have hq : 1 < Nat.card K := Finite.one_lt_card
  refine not_dvd_index_of_card_eq Nat.prime_three _ ?_
  set q := Nat.card K with hqdef
  have hg3 : Nat.gcd 3 (q - 1) = 3 := Nat.gcd_eq_left h3
  have hg3' : Nat.gcd (q - 1) 3 = 3 := Nat.gcd_eq_right h3
  have hH : Nat.card (torusGroup .E6 K) * 3 = (q - 1) ^ 6 := by
    have := card_torusGroup_E6 (K := K)
    rwa [hg3'] at this
  have hX : (q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) *
      (q ^ 2 - 1)) = (q - 1) ^ 6 * q ^ 36 * (geomSum 2 1 q * geomSum 3 1 q * geomSum 4 1 q *
        geomSum 5 1 q * (geomSum 2 3 q * geomSum 8 1 q) * (geomSum 9 1 q * geomSum 3 4 q)) :=
    (ordE6_mul q hq.le).symm
  have hdvd : 3 ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) *
      (q ^ 2 - 1) := by
    rw [hX]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow h3 (by norm_num)) _) _
  have hS : Nat.card (adjointGroup .E6 K) * 3 = q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) *
      (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) * (q ^ 2 - 1) := by
    rw [card_adjointGroup_E6, ordE6, hg3]
    exact Nat.div_mul_cancel hdvd
  have hN : Nat.card (monomialSub .E6 K) * 3 = (q - 1) ^ 6 * 51840 := by
    rw [card_monomialSub_E6, mul_right_comm, hH]
  have e1 := congrArg (fun n => n.factorization 3) hS
  have e2 := congrArg (fun n => n.factorization 3) hN
  have hS0 : Nat.card (adjointGroup .E6 K) ≠ 0 := Nat.card_pos.ne'
  have hN0 : Nat.card (monomialSub .E6 K) ≠ 0 := Nat.card_pos.ne'
  rw [Nat.factorization_mul hS0 (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_three,
    factorization_three_numerator_E6 hq h3] at e1
  rw [Nat.factorization_mul hN0 (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_three,
    factorization_three_mul_51840 h3 hq] at e2
  omega

end Index

theorem finite_adjointGroup_E6 {K : Type} [Field K] [Finite K] : Finite (adjointGroup .E6 K) :=
  generated_group_finite .E6 K

theorem torusSub_comm {τ : Tag} {K : Type} [Field K] :
    ∀ a ∈ torusSub τ K, ∀ b ∈ torusSub τ K, a * b = b * a := by
  intro a ha b hb
  obtain ⟨x, hx⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (Subgroup.mem_subgroupOf.1 ha)
  obtain ⟨y, hy⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (Subgroup.mem_subgroupOf.1 hb)
  refine Subtype.ext ?_
  change (a : ModGL τ K) * b = b * a
  rw [hx, hy, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

theorem monomialSubHom_ker_iff {τ : Tag} {K : Type} [Field K]
    (n : monomialSub τ K) : monomialSubHom n = 1 ↔ (n : adjointGroup τ K) ∈ torusSub τ K := by
  have h : n ∈ (monomialSubHom (τ := τ) (K := K)).ker ↔
      n ∈ (borelSub τ K ⊓ monomialSub τ K).subgroupOf (monomialSub τ K) := by
    rw [monomialSubHom_ker]
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, borelSub_inf_monomialSub] at h
  exact h

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
