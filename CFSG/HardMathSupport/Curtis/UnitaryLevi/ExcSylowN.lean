module

public import CFSG.LieType.Chevalley.ChevalleySplitBN
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.RankThree.PartOne.K133H.F4Weyl

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

theorem exists_sylow_three_le_of_factorization_eq {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) (h : (Nat.card N).factorization 3 = (Nat.card G).factorization 3) :
    ∃ P : Sylow 3 G, (P : Subgroup G) ≤ N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 3 N) := inferInstance
  have hQ : Nat.card ((Q : Subgroup N).map N.subtype) = 3 ^ (Nat.card G).factorization 3 := by
    rw [Subgroup.card_map_of_injective N.subtype_injective, Q.card_eq_multiplicity, h]
  exact ⟨Sylow.ofCard _ hQ, fun x hx => by
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2⟩

theorem padicValNat_three_pow_sub_one {q n : ℕ} (hq : 1 < q) (h3 : 3 ∣ q - 1) (hn : n ≠ 0) :
    padicValNat 3 (q ^ n - 1) = padicValNat 3 (q - 1) + padicValNat 3 n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnq : ¬ 3 ∣ q := by omega
  simpa using padicValNat.pow_sub_pow (p := 3) (x := q) (y := 1) (by decide) hq
    (by simpa using h3) hnq hn

theorem padicValNat_three_ordF4 {q : ℕ} (hq : 1 < q) (h3 : 3 ∣ q - 1) :
    padicValNat 3 (CFSG.Open.ordF4 q) = 4 * padicValNat 3 (q - 1) + 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnq : ¬ 3 ∣ q := by omega
  have hp : ∀ n, 0 < q ^ n - 1 → n ≠ 0 → q ^ n - 1 ≠ 0 := fun _ h _ => h.ne'
  have h12 : 0 < q ^ 12 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) hq)
  have h8 : 0 < q ^ 8 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) hq)
  have h6 : 0 < q ^ 6 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) hq)
  have h2 : 0 < q ^ 2 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) hq)
  unfold CFSG.Open.ordF4
  rw [padicValNat.mul (by positivity) h2.ne', padicValNat.mul (by positivity) h6.ne',
    padicValNat.mul (by positivity) h8.ne', padicValNat.mul (by positivity) h12.ne',
    padicValNat.pow q 24, padicValNat.eq_zero_of_not_dvd hnq,
    padicValNat_three_pow_sub_one hq h3 (by norm_num), padicValNat_three_pow_sub_one hq h3 (by norm_num),
    padicValNat_three_pow_sub_one hq h3 (by norm_num), padicValNat_three_pow_sub_one hq h3 (by norm_num)]
  have e12 : padicValNat 3 12 = 1 := by
    rw [show (12 : ℕ) = 3 * 4 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat_self, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have e6 : padicValNat 3 6 = 1 := by
    rw [show (6 : ℕ) = 3 * 2 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat_self, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have e8 : padicValNat 3 8 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  have e2 : padicValNat 3 2 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [e12, e6, e8, e2]
  omega

theorem card_monomialSub_eq (τ : Tag) (K : Type) [Field K] [Finite K] :
    Nat.card (monomialSub τ K) = Nat.card (torusGroup τ K) * Nat.card (WeylGroup τ) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((borelSub τ K ⊓ monomialSub τ K).subgroupOf (monomialSub τ K)),
    Nat.card_congr (monomialSubQuotientEquiv (τ := τ) (K := K)).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : borelSub τ K ⊓ monomialSub τ K ≤ monomialSub τ K)).toEquiv,
    borelSub_inf_monomialSub,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_sup_left.trans borelGroup_le_adjointGroup' : torusGroup τ K ≤ adjointGroup τ K)).toEquiv,
    mul_comm]

theorem exists_sylow_three_le_monomialSub_F4 (K : Type) [Field K] [Finite K]
    (h3 : 3 ∣ Nat.card K - 1) :
    ∃ P : Sylow 3 (adjointGroup .F4 K), (P : Subgroup (adjointGroup .F4 K)) ≤ monomialSub .F4 K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : 1 < Nat.card K := Finite.one_lt_card
  refine exists_sylow_three_le_of_factorization_eq _ ?_
  rw [Nat.factorization_def _ Nat.prime_three, Nat.factorization_def _ Nat.prime_three,
    card_monomialSub_eq, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4,
    CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_F4,
    CFSG.RankThree.PartOne.K133H.card_weylGroup_F4, padicValNat_three_ordF4 hq h3,
    padicValNat.mul (pow_ne_zero _ (by omega)) (by norm_num), padicValNat.pow (Nat.card K - 1) 4]
  have e : padicValNat 3 1152 = 2 := by
    rw [show (1152 : ℕ) = 3 ^ 2 * 128 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  rw [e]

end CFSG.HardMathSupport.Curtis.UnitaryLevi

end
