module

public import CFSG.LieType.SeitzGeneration.ExcHigh.Generic
public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.HardMathSupport.Lang.AnisoF4.B4Planes
public import CFSG.Timmesfeld.Orders.ClassicalOmega
public import CFSG.ClassicalInvolution.Orders.Orthogonal

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open scoped MatrixGroups
open CFSG.Open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Lang.AnisoF4 CFSG.ClassicalInvolution.ModelFacts.OrthAut

theorem factorization_pow_two_mul_sub_one_five {q : ℕ} (hq : 5 ∣ q + 1) {k : ℕ} (hk : k ≠ 0) :
    (q ^ (2 * k) - 1).factorization 5 = (q + 1).factorization 5 + k.factorization 5 := by
  have hq5 : (q : ZMod 5) = -1 := by
    have h0 : ((q + 1 : ℕ) : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hq
    rw [Nat.cast_add, Nat.cast_one] at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hord : orderOf (q : ZMod 5) = 2 := by
    rw [hq5]
    exact orderOf_eq_prime (by decide) (by decide)
  have hsq : (q ^ 2 - 1).factorization 5 = (q + 1).factorization 5 := by
    have h1 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      zify [(by omega : 1 ≤ q), Nat.one_le_pow 2 q (by omega)]
      ring
    rw [h1, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by omega : ¬ 5 ∣ q - 1), zero_add]
  have h := ordProj_pow_sub_one_of_dvd (by norm_num) (by norm_num) (by omega) (by omega) hord hk
  rw [hsq, ← pow_add] at h
  exact Nat.pow_right_injective (by norm_num) h

private theorem prod_map_pow_two_mul_sub_one_ne_zero {q : ℕ} (hq : 2 ≤ q) {ks : List ℕ}
    (hks : ∀ k ∈ ks, k ≠ 0) : (ks.map fun k => q ^ (2 * k) - 1).prod ≠ 0 :=
  List.prod_ne_zero fun h => by
    obtain ⟨k, hk, hk0⟩ := List.mem_map.1 h
    exact Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by have := hks k hk; omega) (by omega)) hk0

private theorem factorization_prod_map_pow_two_mul_sub_one_five {q : ℕ} (hq : 5 ∣ q + 1)
    (ks : List ℕ) (hks : ∀ k ∈ ks, k ≠ 0 ∧ ¬ 5 ∣ k) :
    (ks.map fun k => q ^ (2 * k) - 1).prod.factorization 5 =
      ks.length * (q + 1).factorization 5 := by
  induction ks with
  | nil => simp
  | cons k ks ih =>
    obtain ⟨hk0, hk5⟩ := hks k List.mem_cons_self
    have hks' : ∀ j ∈ ks, j ≠ 0 ∧ ¬ 5 ∣ j := fun j hj => hks j (List.mem_cons_of_mem _ hj)
    rw [List.map_cons, List.prod_cons,
      Nat.factorization_mul (Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by omega) (by omega)))
        (prod_map_pow_two_mul_sub_one_ne_zero (by omega) fun j hj => (hks' j hj).1),
      Finsupp.add_apply, factorization_pow_two_mul_sub_one_five hq hk0,
      Nat.factorization_eq_zero_of_not_dvd hk5, ih hks', List.length_cons]
    ring

private theorem factorization_pow_mul_prod_mul_five {q : ℕ} (hq : 5 ∣ q + 1) (a : ℕ)
    (ks : List ℕ) (hks : ∀ k ∈ ks, k ≠ 0 ∧ ¬ 5 ∣ k) :
    (q ^ a * (ks.map fun k => q ^ (2 * k) - 1).prod * (q ^ 10 - 1)).factorization 5 =
      (ks.length + 1) * (q + 1).factorization 5 + 1 := by
  have hP := prod_map_pow_two_mul_sub_one_ne_zero (q := q) (by omega) fun j hj => (hks j hj).1
  have ha : q ^ a ≠ 0 := pow_ne_zero _ (by omega)
  have h10 : (q ^ 10 - 1).factorization 5 = (q + 1).factorization 5 + 1 := by
    have h := factorization_pow_two_mul_sub_one_five hq (k := 5) (by norm_num)
    rwa [Nat.Prime.factorization_self Nat.prime_five] at h
  rw [Nat.factorization_mul (mul_ne_zero ha hP)
      (Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by norm_num) (by omega))),
    Nat.factorization_mul ha hP, Finsupp.add_apply, Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.factorization_eq_zero_of_not_dvd (by omega : ¬ 5 ∣ q), smul_zero,
    zero_add, factorization_prod_map_pow_two_mul_sub_one_five hq ks hks, h10]
  ring

theorem factorization_card_proj_quadPlus {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {n : ℕ} (hn : 4 ≤ n) :
    (Nat.card (StatedProj (StatedOmega (StatedQuadPlus n K)))).factorization p =
      (Nat.card K ^ (n * (n - 1)) * (Nat.card K ^ n - 1) *
        ∏ i ∈ Finset.Icc 1 (n - 1), (Nat.card K ^ (2 * i) - 1)).factorization p := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  by_cases h2 : ringChar K = 2
  · have : CharP K 2 := h2 ▸ ringChar.charP K
    have hq1 : 1 ≤ Nat.card K := Nat.card_pos
    have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadPlus (K := K) hn
    have e1 : ((Nat.card K ^ n - 1 : ℕ) : ℤ) = (Nat.card K : ℤ) ^ n - 1 := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ hq1)]
      push_cast
      ring
    have e2 : ((∏ i ∈ Finset.Icc 1 (n - 1), (Nat.card K ^ (2 * i) - 1) : ℕ) : ℤ) =
        ∏ i ∈ Finset.Icc 1 (n - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
      rw [Nat.cast_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Nat.cast_sub (Nat.one_le_pow _ _ hq1)]
      push_cast
      ring
    have key : (Nat.card (StatedProj (StatedOmega (StatedQuadPlus n K))) : ℤ) =
        ((Nat.card K ^ (n * (n - 1)) * (Nat.card K ^ n - 1) *
          ∏ i ∈ Finset.Icc 1 (n - 1), (Nat.card K ^ (2 * i) - 1) : ℕ) : ℤ) := by
      rw [h, Nat.cast_mul, Nat.cast_mul, e1, e2]
      push_cast
      ring
    have key' : Nat.card (StatedProj (StatedOmega (StatedQuadPlus n K))) =
        Nat.card K ^ (n * (n - 1)) * (Nat.card K ^ n - 1) *
          ∏ i ∈ Finset.Icc 1 (n - 1), (Nat.card K ^ (2 * i) - 1) := by
      exact_mod_cast key
    rw [key']
  · rw [CFSG.ClassicalInvolution.card_statedProj_statedOmega_quadPlus_eq_ordD hℓ h2 hK hn, ← hK]
    set q := Nat.card K
    have hdef : ordD n q = q ^ (n * (n - 1)) * (q ^ n - 1) *
        (∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1)) / Nat.gcd 4 (q ^ n - 1) := rfl
    have hg : Nat.gcd 4 (q ^ n - 1) ∣ q ^ (n * (n - 1)) * (q ^ n - 1) *
        ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1) :=
      (Nat.gcd_dvd_right _ _).trans (Dvd.dvd.mul_right (Dvd.dvd.mul_left dvd_rfl _) _)
    have hgf : (Nat.gcd 4 (q ^ n - 1)).factorization p = 0 := by
      refine Nat.factorization_eq_zero_of_not_dvd fun hdv => hp2 ?_
      have h4 : p ∣ 2 ^ 2 := hdv.trans (Nat.gcd_dvd_left 4 _)
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4)
    rw [hdef, Nat.factorization_div hg, Finsupp.coe_tsub, Pi.sub_apply, hgf, Nat.sub_zero]

theorem factorization_card_proj_quadPlus_six_five {K : Type} [Field K] [Finite K]
    (hpq : 5 ∣ Nat.card K + 1) :
    (Nat.card (StatedProj (StatedOmega (StatedQuadPlus 6 K)))).factorization 5 =
      6 * (Nat.card K + 1).factorization 5 + 1 := by
  rw [factorization_card_proj_quadPlus Nat.prime_five (by norm_num) (by norm_num)]
  set q := Nat.card K
  have e : q ^ (6 * (6 - 1)) * (q ^ 6 - 1) * ∏ i ∈ Finset.Icc 1 (6 - 1), (q ^ (2 * i) - 1) =
      q ^ 30 * ([3, 1, 2, 3, 4].map fun k => q ^ (2 * k) - 1).prod * (q ^ 10 - 1) := by
    simp [Finset.prod_Icc_succ_top]
    ring
  rw [e, factorization_pow_mul_prod_mul_five hpq _ _ (by decide)]
  rfl

theorem card_spinGroup_quadPlus_eq_mul {K : Type} [Field K] {n : ℕ} (hn : 3 ≤ n) :
    Nat.card (spinGroup (Spin.quadPlus n K)) =
      Nat.card (StatedProj (StatedOmega (StatedQuadPlus n K))) *
        Nat.card (Subgroup.center (spinGroup (Spin.quadPlus n K))) := by
  obtain ⟨hπ, -, hZ⟩ := spinToStatedProj_quadPlus (n := n) (K := K) hn
  rw [← Subgroup.card_ker_mul_card_of_surjective hπ, hZ, mul_comm]

theorem factorization_card_spin_quadPlus_six_five {K : Type} [Field K] [Finite K]
    (hpq : 5 ∣ Nat.card K + 1) :
    (Nat.card (spinGroup (Spin.quadPlus 6 K))).factorization 5 =
      6 * (Nat.card K + 1).factorization 5 + 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hn3 : 3 ≤ 6 := by norm_num
  have : Finite (spinGroup (Spin.quadPlus 6 K)) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  obtain ⟨-, hcomap, hZ⟩ := spinToStatedProj_quadPlus (n := 6) (K := K) hn3
  have hcen : ¬ 5 ∣ Nat.card (Subgroup.center (spinGroup (Spin.quadPlus 6 K))) :=
    not_dvd_card_center_spin_of_not_dvd_pred (Spin.quadPlus 6 K) (range_spinMatrix_quadPlus hn3)
      hZ hcomap (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadPlus_iff x).mp hx))
      (by norm_num) (by omega)
  have h1 := card_spinGroup_quadPlus_eq_mul (K := K) hn3
  have h0 : Nat.card (StatedProj (StatedOmega (StatedQuadPlus 6 K))) *
      Nat.card (Subgroup.center (spinGroup (Spin.quadPlus 6 K))) ≠ 0 := h1 ▸ Nat.card_pos.ne'
  rw [h1, Nat.factorization_mul (left_ne_zero_of_mul h0) (right_ne_zero_of_mul h0),
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hcen, add_zero,
    factorization_card_proj_quadPlus_six_five hpq]

theorem factorization_card_range_SL2_spin_five {K : Type} [Field K] [Finite K] {G : Type*}
    [Group G] (hpq : 5 ∣ Nat.card K + 1) (ψ : SL(2, K) × spinGroup (Spin.quadPlus 6 K) →* G)
    (hψ : ¬ 5 ∣ Nat.card ψ.ker) :
    (Nat.card ψ.range).factorization 5 = 7 * (Nat.card K + 1).factorization 5 + 1 := by
  have : Finite (spinGroup (Spin.quadPlus 6 K)) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have h := Subgroup.card_ker_mul_card_range ψ
  rw [Nat.card_prod] at h
  have h0 : Nat.card ψ.ker * Nat.card ψ.range ≠ 0 := by
    rw [h]
    exact mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'
  have hv : (Nat.card ψ.ker * Nat.card ψ.range).factorization 5 =
      (Nat.card SL(2, K) * Nat.card (spinGroup (Spin.quadPlus 6 K))).factorization 5 := by
    rw [h]
  rw [Nat.factorization_mul (left_ne_zero_of_mul h0) (right_ne_zero_of_mul h0),
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hψ, zero_add,
    factorization_card_SL2_of_dvd_add_one Nat.prime_five le_rfl hpq,
    factorization_card_spin_quadPlus_six_five hpq] at hv
  omega

section SylowFive


theorem factorization_card_E7_five {K : Type} [Field K] [Finite K] (hpq : 5 ∣ Nat.card K + 1) :
    (Nat.card (adjointGroup .E7 K)).factorization 5 = 7 * (Nat.card K + 1).factorization 5 + 1 := by
  have hlte : ∀ k : ℕ, k ≠ 0 → 5 ^ (Nat.card K ^ (2 * k) - 1).factorization 5 =
      5 ^ (Nat.card K + 1).factorization 5 * 5 ^ k.factorization 5 := fun k hk => by
    rw [factorization_pow_two_mul_sub_one_five hpq hk, pow_add]
  have h := ordProj_card_adjointGroup_E (τ := .E7) (K := K) (by simp) Nat.prime_five
    (by norm_num) (by omega)
  simp only [degreesE, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  rw [hlte 1 one_ne_zero, hlte 3 (by norm_num), hlte 4 (by norm_num), hlte 5 (by norm_num),
    hlte 6 (by norm_num), hlte 7 (by norm_num), hlte 9 (by norm_num),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 1),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 3),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 4),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 6),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 7),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 9),
    Nat.Prime.factorization_self Nat.prime_five] at h
  refine Nat.pow_right_injective (by norm_num : 2 ≤ 5) ?_
  change 5 ^ _ = 5 ^ _
  rw [h]
  ring

theorem factorization_card_E7_le_card_range_five {K : Type} [Field K] [Finite K]
    (hpq : 5 ∣ Nat.card K + 1)
    (ψ : SL(2, K) × spinGroup (Spin.quadPlus 6 K) →* adjointGroup .E7 K)
    (hψ : ¬ 5 ∣ Nat.card ψ.ker) :
    (Nat.card (adjointGroup .E7 K)).factorization 5 ≤ (Nat.card ψ.range).factorization 5 := by
  rw [factorization_card_E7_five hpq, factorization_card_range_SL2_spin_five hpq ψ hψ]

theorem exists_conj_le_range_of_sylow_E7_five {K : Type} [Field K] [Finite K]
    (hpq : 5 ∣ Nat.card K + 1)
    (ψ : SL(2, K) × spinGroup (Spin.quadPlus 6 K) →* adjointGroup .E7 K)
    (hψ : ¬ 5 ∣ Nat.card ψ.ker)
    (E₀ : Subgroup (adjointGroup .E7 K)) (hE₀ : ∀ x ∈ E₀, x ^ 5 = 1) :
    ∃ g : adjointGroup .E7 K, E₀.map (MulAut.conj g).toMonoidHom ≤ ψ.range := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hge : (Nat.card ψ.range).factorization 5 ≤
      (Nat.card (adjointGroup .E7 K)).factorization 5 :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
      (Subgroup.card_subgroup_dvd_card ψ.range) 5
  obtain ⟨g, -, hg⟩ := CFSG.RankThree.PartOne.K133H.exists_conj_le_of_sylow (Y := ⊤)
    (H := ψ.range) le_top le_top hE₀ (by
      rw [Subgroup.card_top]
      exact le_antisymm (factorization_card_E7_le_card_range_five hpq ψ hψ) hge)
  exact ⟨g, hg⟩

end SylowFive

end CFSG.LieType.SeitzGeneration.ExcHigh
