module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAJ

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {Γ M : Type} [Group Γ] [Finite Γ] [Group M] [Finite M] {ρ : Γ →* MulAut M}
  {t : Γ} {J Q P M6 M7 : Subgroup Γ}

theorem y7c_cent_oddCore (c : K7Abs ρ t J Q P M6 M7) {x : Γ} (hx : x ∈ CFSG.oddCore Γ)
    (hxt : x * t = t * x) : x = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj, q, hq, rfl⟩ := c.cent x hxt
  have hnot2 : ¬ 2 ∣ Nat.card (CFSG.oddCore Γ) := by
    rw [CFSG.oddCore_eq_piCore Γ, ← CFSG.pPrimeCore_eq_piCore Γ 2]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp CFSG.pPrimeCore_coprime_card
  set m := orderOf (j * q)
  have hoddN : Odd (Nat.card (CFSG.oddCore Γ)) :=
    Nat.not_even_iff_odd.mp fun hE => hnot2 (even_iff_two_dvd.mp hE)
  have hmodd : Odd m := hoddN.of_dvd_nat (Subgroup.orderOf_dvd_natCard (CFSG.oddCore Γ) hx)
  have hcomm : Commute j q := (c.Q_J q hq j hj).symm
  have hpow : (j * q) ^ m = 1 := pow_orderOf_eq_one _
  have hjmq : j ^ m * q ^ m = 1 := by
    rw [← hcomm.mul_pow m]
    exact hpow
  have hqmpow : q ^ m = (j ^ m)⁻¹ := eq_inv_of_mul_eq_one_right hjmq
  have hqJ : q ^ m ∈ J := by
    rw [hqmpow]
    exact J.inv_mem (J.pow_mem hj m)
  have hqcomm : ∀ y ∈ J, q ^ m * y = y * q ^ m := by
    intro y hy
    exact ((show Commute q y from c.Q_J q hq y hy).pow_left m).eq
  have hqm1 : q ^ m = 1 := y7c_J_center c hqJ hqcomm
  obtain ⟨k, hk⟩ := c.Q_two.exists_orderOf_eq_pow (⟨q, hq⟩ : ↥Q)
  rw [Subgroup.orderOf_mk (H := Q) q hq] at hk
  have hdvd : 2 ^ k ∣ m := by
    rw [← hk]
    exact orderOf_dvd_iff_pow_eq_one.mpr hqm1
  have hk0 : k = 0 := by
    by_contra hkne
    have h2dvd : 2 ∣ 2 ^ k := by
      obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkne
      rw [pow_succ]
      exact dvd_mul_left 2 (2 ^ l)
    exact hmodd.not_two_dvd_nat (h2dvd.trans hdvd)
  rw [hk0, pow_zero] at hk
  have hq1 : q = 1 := orderOf_eq_one_iff.mp hk
  have hjO : j ∈ CFSG.oddCore Γ := by simpa [hq1] using hx
  rw [hq1, mul_one]
  rcases y7c_J_inf_normal c (CFSG.oddCore Γ) with hbot | hle
  · have hmem : j ∈ J ⊓ CFSG.oddCore Γ := ⟨hj, hjO⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  · exfalso
    have hdvdJ : Nat.card ↥J ∣ Nat.card ↥(CFSG.oddCore Γ) := Subgroup.card_dvd_of_le hle
    rw [y7c_J_card c] at hdvdJ
    exact hnot2 (dvd_trans (by norm_num : 2 ∣ 168) hdvdJ)

theorem y7c_oddCore_inv (c : K7Abs ρ t J Q P M6 M7) {x : Γ} (hx : x ∈ CFSG.oddCore Γ) :
    t * x * t⁻¹ = x⁻¹ := by
  have htt : t * t = 1 := by rw [← pow_two]; exact c.t_sq
  let φ : ↥(CFSG.oddCore Γ) →* ↥(CFSG.oddCore Γ) :=
    { toFun := fun a => ⟨t * (a : Γ) * t⁻¹,
        (CFSG.oddCore_normal (G := Γ)).conj_mem (a : Γ) a.2 t⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hφ : MonoidHom.FixedPointFree φ := by
    intro a ha
    apply Subtype.ext
    have h : t * (a : Γ) * t⁻¹ = (a : Γ) := congrArg Subtype.val ha
    refine y7c_cent_oddCore c a.2 ?_
    have h' : t * (a : Γ) = (a : Γ) * t := by
      calc t * (a : Γ) = t * (a : Γ) * t⁻¹ * t := by group
        _ = (a : Γ) * t := by rw [h]
    exact h'.symm
  have hinv : Function.Involutive φ := by
    intro a
    apply Subtype.ext
    change t * (t * (a : Γ) * t⁻¹) * t⁻¹ = (a : Γ)
    calc t * (t * (a : Γ) * t⁻¹) * t⁻¹ = (t * t) * (a : Γ) * (t * t)⁻¹ := by group
      _ = (a : Γ) := by rw [htt]; group
  have h := congrFun (MonoidHom.FixedPointFree.coe_eq_inv_of_involutive hφ hinv) ⟨x, hx⟩
  simpa [φ] using congrArg Subtype.val h

theorem y7c_comm_cent_oddCore (c : K7Abs ρ t J Q P M6 M7) (m : Γ) {o : Γ}
    (ho : o ∈ CFSG.oddCore Γ) : ⁅m, t⁆ * o = o * ⁅m, t⁆ := by
  set a := ⁅m, t⁆ with ha
  have hm_inv : (m * t * m⁻¹) * o * (m * t * m⁻¹)⁻¹ = o⁻¹ := by
    have h1 : t * (m⁻¹ * o * m) * t⁻¹ = (m⁻¹ * o * m)⁻¹ := by
      simpa using y7c_oddCore_inv c ((CFSG.oddCore_normal (G := Γ)).conj_mem o ho m⁻¹)
    calc (m * t * m⁻¹) * o * (m * t * m⁻¹)⁻¹
        = m * (t * (m⁻¹ * o * m) * t⁻¹) * m⁻¹ := by group
      _ = m * (m⁻¹ * o * m)⁻¹ * m⁻¹ := by rw [h1]
      _ = o⁻¹ := by group
  have hat : a * t = m * t * m⁻¹ := by
    rw [ha, commutatorElement_def]
    group
  have ha_inv : (a * t) * o * (a * t)⁻¹ = o⁻¹ := by
    rw [hat]
    exact hm_inv
  have hcalc : (a * t) * o * (a * t)⁻¹ = a * o⁻¹ * a⁻¹ := by
    calc (a * t) * o * (a * t)⁻¹ = a * (t * o * t⁻¹) * a⁻¹ := by group
      _ = a * o⁻¹ * a⁻¹ := by rw [y7c_oddCore_inv c ho]
  have hkey : a * o⁻¹ * a⁻¹ = o⁻¹ := by rw [← hcalc, ha_inv]
  have hao : a * o * a⁻¹ = o := by
    have h := congrArg Inv.inv hkey
    simpa [mul_assoc] using h
  have hfinal : a * o = o * a := by
    calc a * o = (a * o * a⁻¹) * a := by group
      _ = o * a := by rw [hao]
  rw [ha] at hfinal
  exact hfinal

theorem y7c_J_le_cent_oddCore (c : K7Abs ρ t J Q P M6 M7) :
    J ≤ Subgroup.centralizer ((CFSG.oddCore Γ : Subgroup Γ) : Set Γ) := by
  obtain ⟨m, hmJ, hmne⟩ := c.comm_wit
  set C : Subgroup Γ := Subgroup.centralizer ((CFSG.oddCore Γ : Subgroup Γ) : Set Γ) with hC
  haveI hCnorm : C.Normal := by
    rw [hC]
    exact Subgroup.normal_centralizer
  have haC : ⁅m, t⁆ ∈ C := by
    rw [hC, Subgroup.mem_centralizer_iff]
    intro o ho
    exact (y7c_comm_cent_oddCore c m ho).symm
  have hinter : ⁅m, t⁆ ∈ J ⊓ C := ⟨hmJ, haC⟩
  rcases y7c_J_inf_normal c C with hbot | hle
  · exfalso
    rw [hbot] at hinter
    exact hmne (Subgroup.mem_bot.mp hinter)
  · simpa [hC] using hle

end CFSG.OddStandard.HigherRank.YamadaG23
