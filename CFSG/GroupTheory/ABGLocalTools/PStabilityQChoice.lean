module

public import CFSG.GroupTheory.ABGLocalTools.PStabilitySL2Props
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
import Mathlib.Tactic.NormNum.Prime
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

open Subgroup

namespace CFSG.ABGLocalTools

open SL2Facts

section Lemmas

variable {F : Type*} [Field F]

local notation "SL2" => Matrix.SpecialLinearGroup (Fin 2) F

theorem apply_one_zero_ne_zero_of_orderOf [Finite F] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hpF : p ∣ Nat.card F + 1) {g : SL2} (hg : orderOf g = p) : g 1 0 ≠ 0 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hpp : p.Prime := Fact.out
  intro h0
  have hdet := det_eq g
  rw [h0, mul_zero, sub_zero] at hdet
  have hg00 : g 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have hgp : g ^ p = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have h1 : g 0 0 ^ p = 1 := by
    have := (pow_apply_of_lower_eq_zero h0 p).2
    rw [hgp] at this
    simpa using this.symm
  have h2 : g 0 0 ^ (Fintype.card F - 1) = 1 := FiniteField.pow_card_sub_one_eq_one _ hg00
  have hcop : Nat.Coprime p (Fintype.card F - 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd hpp]
    intro hdvd
    have hcard : 1 ≤ Fintype.card F := Fintype.card_pos
    have : p ∣ (Fintype.card F + 1) - (Fintype.card F - 1) :=
      Nat.dvd_sub (by rwa [← Nat.card_eq_fintype_card]) hdvd
    rw [show Fintype.card F + 1 - (Fintype.card F - 1) = 2 by omega] at this
    exact hp ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp this)
  have hg1 : g 0 0 = 1 := by
    have := pow_gcd_eq_one.mpr ⟨h1, h2⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  have hg11 : g 1 1 = 1 := by rw [hg1, one_mul] at hdet; exact hdet
  have hgu : g = uT (g 0 1) := by
    apply Subtype.ext
    rw [coe_uT]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hg1, hg11, h0]
  have hq : g ^ Fintype.card F = 1 := by
    rw [hgu, uT_pow, FiniteField.cast_card_eq_zero, zero_mul]
    apply Subtype.ext
    rw [coe_uT, Matrix.SpecialLinearGroup.coe_one]
    simp [Matrix.one_fin_two]
  have hdvd : p ∣ Fintype.card F := hg ▸ orderOf_dvd_of_pow_eq_one hq
  rw [Nat.card_eq_fintype_card] at hpF
  have : p ∣ 1 := (Nat.dvd_add_right hdvd).mp hpF
  exact hpp.one_lt.ne' (Nat.dvd_one.mp this)

end Lemmas

theorem sl2ElementChoice : SL2ElementChoice := by
  intro F _ _ p _ hp hFodd hF5 hpF g hg
  classical
  have : Fintype F := Fintype.ofFinite F
  have hpp : p.Prime := Fact.out
  have hγ := apply_one_zero_ne_zero_of_orderOf hp hpF hg
  set γ := g 1 0 with hγdef
  have hgp : g ^ p = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  by_cases h9 : Nat.card F = 9
  ·
    have : CharP F 3 := charP_of_card_eq_prime_pow (n := 2) Nat.prime_three (by rw [h9]; norm_num)
    have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
    have hp5 : p = 5 := by
      rw [h9] at hpF
      have : p ∣ 2 * 5 := hpF
      rcases (Nat.Prime.dvd_mul hpp).mp this with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h) hp
      · exact (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_five).mp h
    subst hp5
    set τ := Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) with hτdef
    have hτ4 : τ ^ 4 = -1 := by
      by_cases h2 : τ = 2
      · exfalso
        have hg3 : g ^ 3 = 1 := by
          refine pow_succ_eq_one_of_U (n := 2) ?_ ?_
          · rw [← hτdef, h2]; simp only [U_add_two, U_one, U_zero, zero_add]
            linear_combination h3
          · rw [← hτdef, h2]; simp only [U_add_two, U_one, U_zero, zero_add]
            linear_combination h3
        have := orderOf_dvd_of_pow_eq_one hg3
        rw [hg] at this
        norm_num at this
      by_cases hm2 : τ = -2
      · exfalso
        have hg6 : g ^ 6 = 1 := by
          have hg3 : g ^ 3 = -1 := by
            apply Subtype.ext
            rw [pow_succ_eq g 2, ← hτdef, hm2]
            simp only [U_add_two, U_one, U_zero, zero_add]
            rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
            have e1 : (-2 : F) * (-2 * 1 - 0) - 1 = 0 := by linear_combination h3
            have e2 : (-2 : F) * 1 - 0 = 1 := by linear_combination -h3
            rw [e1, e2, zero_smul, zero_sub, one_smul]
          rw [show 6 = 3 * 2 by rfl, pow_mul, hg3]
          simp
        have := orderOf_dvd_of_pow_eq_one hg6
        rw [hg] at this
        norm_num at this
      obtain ⟨h5, -⟩ := U_of_pow_succ_eq_one (n := 4) hgp h2 hm2
      simp only [U_add_two, U_one, U_zero, zero_add] at h5
      linear_combination h5 + τ ^ 2 * h3
    set u := uT (γ⁻¹ : F)
    refine ⟨u, g * (u * g * u⁻¹), mul_mem (subset_closure (Set.mem_insert _ _))
      (subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))), ?_⟩
    have htr : Matrix.trace ((g * (u * g * u⁻¹) : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = τ ^ 2 := by
      have h := trace_mul_add_trace_mul_inv g (u * g * u⁻¹)
      rw [trace_conj] at h
      have hcomm : g * (u * g * u⁻¹)⁻¹ = g * u * g⁻¹ * u⁻¹ := by group
      rw [hcomm, trace_comm_uT, ← hγdef] at h
      have : γ ^ 2 * γ⁻¹ ^ 2 = 1 := by field_simp
      rw [this] at h
      linear_combination h - h3
    obtain ⟨⟨h4, h6, h10⟩, h8⟩ := not_pow_of_trace_sq_eq_neg_one (A := g * (u * g * u⁻¹))
      (by rw [htr, ← pow_mul]; exact hτ4)
    refine ⟨fun k hk => h4 ?_, fun _ => ⟨h4, h6, h10⟩⟩
    have hcop : Nat.Coprime (5 ^ k) 8 := Nat.Coprime.pow_left k (by norm_num)
    have := pow_gcd_eq_one.mpr ⟨hk, h8⟩
    rw [hcop.gcd_eq_one, pow_one] at this
    rw [this, one_pow]
  by_cases h11 : Nat.card F = 11
  ·
    have : CharP F 11 := charP_of_card_eq_prime_pow (n := 1) (by norm_num) (by rw [h11]; norm_num)
    have h11' : (11 : F) = 0 := CharP.cast_eq_zero F 11
    have hp3 : p = 3 := by
      rw [h11] at hpF
      have : p ∣ 2 ^ 2 * 3 := hpF
      rcases (Nat.Prime.dvd_mul hpp).mp this with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow h)) hp
      · exact (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).mp h
    subst hp3
    set u := uT (5 / γ : F)
    refine ⟨u, g * (u * g * u⁻¹)⁻¹, mul_mem (subset_closure (Set.mem_insert _ _))
      (inv_mem (subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))), ?_⟩
    have hcomm : g * (u * g * u⁻¹)⁻¹ = g * u * g⁻¹ * u⁻¹ := by group
    have htr : Matrix.trace ((g * (u * g * u⁻¹)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = 5 := by
      rw [hcomm, trace_comm_uT, ← hγdef]
      have : γ ^ 2 * (5 / γ) ^ 2 = 25 := by field_simp; ring
      rw [this]
      linear_combination 2 * h11'
    obtain ⟨⟨h4, h6, h10⟩, h12⟩ := not_pow_of_trace_eq_five htr
    refine ⟨fun k hk => h6 ?_, fun _ => ⟨h4, h6, h10⟩⟩
    have hd : Nat.gcd (3 ^ k) 12 ∣ 3 := by
      have hcop : Nat.Coprime (Nat.gcd (3 ^ k) 12) 4 :=
        Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _)
          (Nat.Coprime.pow_left k (by norm_num))
      exact hcop.dvd_of_dvd_mul_left (show Nat.gcd (3 ^ k) 12 ∣ 4 * 3 from Nat.gcd_dvd_right _ _)
    have hg := pow_gcd_eq_one.mpr ⟨hk, h12⟩
    obtain ⟨c, hc⟩ := hd
    have h6' : (6 : ℕ) = Nat.gcd (3 ^ k) 12 * (c * 2) := by
      calc (6 : ℕ) = 3 * 2 := rfl
        _ = _ := by rw [← mul_assoc, ← hc]
    rw [h6', pow_mul, hg, one_pow]
  ·
    have hq : 5 < Fintype.card F := by rwa [← Nat.card_eq_fintype_card]
    obtain ⟨lam, hlam⟩ := IsCyclic.exists_generator (α := Fˣ)
    have hord : orderOf lam = Fintype.card F - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hlam, Nat.card_eq_fintype_card,
        Fintype.card_units]
    set t : F := ((lam : F) - (lam : F)⁻¹) / γ
    set u := uT t
    refine ⟨u, g * (u * g * u⁻¹)⁻¹, mul_mem (subset_closure (Set.mem_insert _ _))
      (inv_mem (subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))), ?_⟩
    have hcomm : g * (u * g * u⁻¹)⁻¹ = g * u * g⁻¹ * u⁻¹ := by group
    have key : ∀ n : ℕ, (g * (u * g * u⁻¹)⁻¹) ^ n = 1 → Fintype.card F - 1 ∣ 2 * n := by
      intro n hn
      rw [hcomm] at hn
      have h := pow_two_mul_eq_one_of_comm_pow hγ (Units.ne_zero lam) hn
      rw [← hord]
      apply orderOf_dvd_of_pow_eq_one
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact h
    have hcop : Nat.Coprime p (Fintype.card F - 1) := by
      rw [Nat.Prime.coprime_iff_not_dvd hpp]
      intro hdvd
      rw [Nat.card_eq_fintype_card] at hpF
      have : p ∣ (Fintype.card F + 1) - (Fintype.card F - 1) := Nat.dvd_sub hpF hdvd
      rw [show Fintype.card F + 1 - (Fintype.card F - 1) = 2 by omega] at this
      exact hp ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp this)
    refine ⟨fun k hk => ?_, fun h35 => ⟨fun h4 => ?_, fun h6 => ?_, fun h10 => ?_⟩⟩
    · have h := key _ hk
      have h2 : Fintype.card F - 1 ∣ 2 :=
        (Nat.Coprime.pow_right k hcop.symm).dvd_of_dvd_mul_right h
      have := Nat.le_of_dvd two_pos h2
      omega
    all_goals
      first
        | have h := key _ h4
        | have h := key _ h6
        | have h := key _ h10
      have hle := Nat.le_of_dvd (by norm_num) h
      have hub : Fintype.card F ≤ 21 := by omega
      rw [Nat.card_eq_fintype_card] at h9 h11 hpF hFodd
      rw [Nat.odd_iff] at hFodd
      interval_cases hc : Fintype.card F <;> rcases h35 with rfl | rfl <;> omega

end CFSG.ABGLocalTools
