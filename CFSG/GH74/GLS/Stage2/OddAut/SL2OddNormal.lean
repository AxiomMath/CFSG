module

public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.GH74.GLS.Stage2.OddAut

open scoped MatrixGroups commutatorElement

namespace SL2Odd

variable {K : Type} [Field K]

theorem card_sl2 [Finite K] : Nat.card SL(2, K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  let := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card K ^ 2 - Fintype.card K =
      Fintype.card K * (Fintype.card K - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem even_card_sl2 [Finite K] : Even (Nat.card SL(2, K)) := by
  rw [card_sl2]
  by_cases hq : Even (Nat.card K)
  · exact hq.mul_right _
  · rw [Nat.not_even_iff_odd] at hq
    exact Even.mul_left (Nat.Odd.sub_odd hq.pow odd_one) _

theorem mul_self_eq_one_of_mem_center {z : SL(2, K)} (hz : z ∈ Subgroup.center SL(2, K)) :
    z * z = 1 := by
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  rw [Fintype.card_fin] at hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, ← hrz, ← map_mul, ← sq, hr, map_one]
  rfl

theorem eq_bot_of_four_le [Finite K] (h4 : 4 ≤ Nat.card K) (N : Subgroup SL(2, K)) [N.Normal]
    (hN : Odd (Nat.card N)) : N = ⊥ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h4' : ∃ s : Finset K, s.card = 4 := by
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
    exact ⟨t, ht⟩
  have hperf := CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := 2) le_rfl (Or.inr h4')
  have hsimple := (CFSG.LinearGroups.linear_projective_simple (K := K) (n := 2) le_rfl
    (Or.inr h4')).2.1
  have : (N.map (QuotientGroup.mk' (Subgroup.center SL(2, K)))).Normal :=
    Subgroup.Normal.map ‹N.Normal› _ (QuotientGroup.mk'_surjective _)
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (Subgroup.center SL(2, K))))
    with hbot | htop
  · have hle : N ≤ Subgroup.center SL(2, K) := by
      intro n hn
      have hmem : QuotientGroup.mk' (Subgroup.center SL(2, K)) n ∈
          N.map (QuotientGroup.mk' (Subgroup.center SL(2, K))) := Subgroup.mem_map_of_mem _ hn
      rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
      exact hmem
    refine (Subgroup.eq_bot_iff_forall N).2 fun n hn => ?_
    have hsq : n * n = 1 := mul_self_eq_one_of_mem_center (hle hn)
    obtain ⟨m, hm⟩ := hN
    have hpow : n ^ Nat.card N = 1 :=
      congrArg Subtype.val (pow_card_eq_one' (G := N) (x := ⟨n, hn⟩))
    calc n = n ^ (2 * m + 1) := by rw [pow_succ, pow_mul, sq, hsq, one_pow, one_mul]
      _ = 1 := hm ▸ hpow
  · exfalso
    have hdecomp : ∀ g : SL(2, K), ∃ n ∈ N, ∃ z ∈ Subgroup.center SL(2, K), g = n * z := by
      intro g
      have hmem : QuotientGroup.mk' (Subgroup.center SL(2, K)) g ∈
          N.map (QuotientGroup.mk' (Subgroup.center SL(2, K))) := by
        rw [htop]; exact Subgroup.mem_top _
      obtain ⟨n, hn, hng⟩ := Subgroup.mem_map.mp hmem
      exact ⟨n, hn, n⁻¹ * g, QuotientGroup.eq.mp hng, by group⟩
    have hcomm : ∀ a b : SL(2, K), ⁅a, b⁆ ∈ N := by
      intro a b
      obtain ⟨n₁, hn₁, z₁, hz₁, rfl⟩ := hdecomp a
      obtain ⟨n₂, hn₂, z₂, hz₂, rfl⟩ := hdecomp b
      have e1 : QuotientGroup.mk' N n₁ = 1 := (QuotientGroup.eq_one_iff n₁).2 hn₁
      have e2 : QuotientGroup.mk' N n₂ = 1 := (QuotientGroup.eq_one_iff n₂).2 hn₂
      have h1 : QuotientGroup.mk' N (n₁ * z₁) = QuotientGroup.mk' N z₁ := by
        rw [map_mul, e1, one_mul]
      have h2 : QuotientGroup.mk' N (n₂ * z₂) = QuotientGroup.mk' N z₂ := by
        rw [map_mul, e2, one_mul]
      rw [← QuotientGroup.eq_one_iff (N := N)]
      change QuotientGroup.mk' N ⁅n₁ * z₁, n₂ * z₂⁆ = 1
      rw [map_commutatorElement, h1, h2, ← map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.mp hz₂ z₁), map_one]
    have hNtop : N = ⊤ := by
      rw [eq_top_iff]
      have h := Group.isPerfect_def.mp hperf
      rw [commutator_def] at h
      rw [← h]
      exact Subgroup.commutator_le.2 fun a _ b _ => hcomm a b
    rw [hNtop, Subgroup.card_top] at hN
    exact (Nat.not_even_iff_odd.mpr hN) even_card_sl2

theorem three_eq_zero [Finite K] (h3 : Nat.card K = 3) : (3 : K) = 0 := by
  have := card_nsmul_eq_zero' (G := K) (x := (1 : K))
  rw [h3, nsmul_eq_mul, mul_one] at this
  exact_mod_cast this

theorem mem_of_pow_three_eq_one {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 24)
    (N : Subgroup G) [N.Normal] (hN : Nat.card N = 3) {x : G} (hx : x ^ 3 = 1) : x ∈ N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNp : IsPGroup 3 N := IsPGroup.of_card (n := 1) (by rw [hN, pow_one])
  have hindex : ¬ 3 ∣ N.index := by
    have := N.card_mul_index
    rw [hN, hG] at this
    omega
  let P : Sylow 3 G := hNp.toSylow hindex
  have hPn : (P : Subgroup G).Normal := by
    rw [show (P : Subgroup G) = N from IsPGroup.toSylow_coe hNp hindex]
    infer_instance
  let _ := Sylow.unique_of_normal P hPn
  have hzp : IsPGroup 3 (Subgroup.zpowers x) := by
    rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hx) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  rw [Subsingleton.elim Q P] at hQ
  exact (IsPGroup.mem_toSylow hNp hindex).1 (hQ (Subgroup.mem_zpowers x))

theorem exists_pow_three_eq_one_mul_ne (h3 : (3 : K) = 0) :
    ∃ u v : SL(2, K), u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ u * v ≠ v * u := by
  obtain ⟨u, hu⟩ : ∃ u : SL(2, K), (u : Matrix (Fin 2) (Fin 2) K) = !![1, 1; 0, 1] :=
    ⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : SL(2, K), (v : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 1, 1] :=
    ⟨⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩, rfl⟩
  have h111 : (1 : K) + 1 + 1 = 0 := by
    have : (1 : K) + 1 + 1 = 3 := by norm_num
    rw [this, h3]
  have h111' : (1 : K) + (1 + 1) = 0 := by rw [← add_assoc, h111]
  refine ⟨u, v, ?_, ?_, ?_⟩
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hu, pow_succ, pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h111']
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hv, pow_succ, pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h111]
  · intro h
    have := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp [Matrix.SpecialLinearGroup.coe_mul, hu, hv, Matrix.mul_apply, Fin.sum_univ_two] at this

theorem eq_one_or_three_of_odd_dvd {c : ℕ} (hc : Odd c) (hd : c ∣ 24) : c = 1 ∨ c = 3 := by
  obtain ⟨m, rfl⟩ := hc
  have hle : 2 * m + 1 ≤ 24 := Nat.le_of_dvd (by norm_num) hd
  have hm : m ≤ 11 := by omega
  interval_cases m <;> omega

theorem eq_bot_of_card_three [Finite K] (h3 : Nat.card K = 3) (N : Subgroup SL(2, K)) [N.Normal]
    (hN : Odd (Nat.card N)) : N = ⊥ := by
  have hcard : Nat.card SL(2, K) = 24 := by rw [card_sl2, h3]; norm_num
  rcases eq_one_or_three_of_odd_dvd hN (hcard ▸ N.card_subgroup_dvd_card) with h1 | h3'
  · exact Subgroup.eq_bot_of_card_eq N h1
  · exfalso
    obtain ⟨u, v, hu, hv, huv⟩ := exists_pow_three_eq_one_mul_ne (three_eq_zero h3)
    have huN := mem_of_pow_three_eq_one hcard N h3' hu
    have hvN := mem_of_pow_three_eq_one hcard N h3' hv
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : IsCyclic N := isCyclic_of_prime_card h3'
    have hcomm : (⟨u, huN⟩ : N) * ⟨v, hvN⟩ = ⟨v, hvN⟩ * ⟨u, huN⟩ := by
      let _ := IsCyclic.commGroup (α := N)
      exact mul_comm _ _
    exact huv (congrArg Subtype.val hcomm)

end SL2Odd

theorem sl2_eq_bot_of_normal_odd {K : Type} [Field K] [Finite K] (h3 : 3 ≤ Nat.card K)
    (N : Subgroup SL(2, K)) [N.Normal] (hN : Odd (Nat.card ↥N)) : N = ⊥ := by
  rcases Nat.lt_or_ge (Nat.card K) 4 with h | h
  · exact SL2Odd.eq_bot_of_card_three (by omega) N hN
  · exact SL2Odd.eq_bot_of_four_le h N hN

end CFSG.GH74.GLS.Stage2.OddAut
