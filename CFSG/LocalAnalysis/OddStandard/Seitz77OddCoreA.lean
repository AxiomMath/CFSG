module

public import CFSG.LocalAnalysis.OddStandard.Seitz77OddCoreRep
public import CFSG.LocalAnalysis.OddStandard.Seitz77OddCoreSchur
public import CFSG.LocalAnalysis.OddStandard.Seitz77OddCoreGroup

import CFSG.FeitThompson.OddOrderTheorem
import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup

theorem odd_core_trivial_A {H : Type*} [Group H] [Finite H]
    (ρ : H →* GL (Fin 8) (ZMod 2)) (hρ : Function.Injective ρ) (hperf : commutator H = ⊤)
    (K₀ : Subgroup H) [K₀.Normal] (hodd : Odd (Nat.card K₀))
    (hsimple : IsSimpleGroup (H ⧸ K₀)) (hcard : Nat.card (H ⧸ K₀) = 4080) : K₀ = ⊥ := by
  classical
  by_contra hK₀
  have hHcard : Nat.card H = 4080 * Nat.card K₀ := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup K₀, hcard]
  have hdvd := oddCore_card_dvd_gl_eight ρ hρ
  rw [hHcard] at hdvd
  have hR : Nat.card K₀ ∣ 3 ^ 4 * 5 * 7 ^ 2 * 31 * 127 := oddCore_dvd_R_of_mul_dvd_gl_A hodd hdvd
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have h17 : 17 ∣ Nat.card H := hHcard ▸ Dvd.dvd.mul_right (by norm_num : 17 ∣ 4080) _
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 17 h17
  have hc17 : c ^ 17 = 1 := hc ▸ pow_orderOf_eq_one c
  have hcK : c ∉ K₀ := by
    intro hcK
    have h1 : 17 ∣ Nat.card K₀ := hc ▸ Subgroup.orderOf_dvd_natCard K₀ hcK
    have h2 : 17 ∣ 3 ^ 4 * 5 * 7 ^ 2 * 31 * 127 := h1.trans hR
    norm_num at h2
  have hsolv : Group.IsSolvable K₀ := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  obtain ⟨M, p, r, hMn, hMK, hp, hr, hMcard⟩ := oddCore_exists_normal_pgroup_le K₀ hK₀
  have hMdvd : Nat.card M ∣ Nat.card K₀ := Subgroup.card_dvd_of_le hMK
  have hMR : p ^ r ∣ 3 ^ 4 * 5 * 7 ^ 2 * 31 * 127 := hMcard ▸ hMdvd.trans hR
  have htab : ∀ j, 1 ≤ j → j ≤ r → p ^ j % 17 ≠ 1 := fun j hj hjr =>
    oddCore_prime_pow_mod_seventeen hp hj ((pow_dvd_pow p hjr).trans hMR)
  have hp17 : p ≠ 17 := by
    intro h
    have hpR : p ∣ 3 ^ 4 * 5 * 7 ^ 2 * 31 * 127 := (dvd_pow_self p hr.ne').trans hMR
    rcases oddCore_prime_dvd_R_A hp hpR with h' | h' | h' | h' | h' <;> omega
  have hcM : c ∈ Subgroup.centralizer (M : Set H) :=
    oddCore_mem_centralizer_of_pow_eq_one M c 17 hc17 p r hp hp17 hMcard htab
  have hsup : Subgroup.centralizer (M : Set H) ⊔ K₀ = ⊤ :=
    oddCore_sup_eq_top_of_isSimple K₀ (Subgroup.centralizer (M : Set H)) (fun hle => hcK (hle hcM))
  have hMz : M ≤ Subgroup.center H := oddCore_le_center_of_sup_eq_top hperf K₀ M hsup
  have hMbot : M ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hMcard
    have := Nat.one_lt_pow hr.ne' hp.one_lt
    omega
  obtain ⟨⟨μ, hμM⟩, hμ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hMbot
  have hμ1' : μ ≠ 1 := fun h => hμ1 (Subtype.ext h)
  have hμc : ∀ g, g * μ = μ * g := fun g => Subgroup.mem_center_iff.mp (hMz hμM) g
  have hμodd : Odd (orderOf μ) :=
    Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard K₀ (hMK hμM))
  have hθc : oddCoreRep ρ c ^ 17 = 1 := by rw [← map_pow, hc17, map_one]
  have hθc1 : oddCoreRep ρ c ≠ 1 := by
    intro h
    have h1 : c = 1 := oddCoreRep_injective ρ hρ (by rw [h, map_one])
    have h2 : orderOf c = 1 := orderOf_eq_one_iff.mpr h1
    omega
  have hirr := oddCore_eq_bot_or_eq_top_of_pow_seventeen oddCore_finrank_fin_eight_fun
    (oddCoreRep ρ c) hθc hθc1
  have hcomm : oddCoreRep ρ μ * oddCoreRep ρ c = oddCoreRep ρ c * oddCoreRep ρ μ := by
    rw [← map_mul, ← map_mul, hμc]
  have hdom : ∀ a ∈ Algebra.adjoin (ZMod 2) {oddCoreRep ρ μ}, a ≠ 0 → Function.Injective a :=
    fun a ha ha0 =>
      oddCore_injective_of_mem_adjoin_of_irreducible (oddCoreRep ρ μ) (oddCoreRep ρ c) hcomm hirr
        a ha ha0
  have hone := oddCore_eq_one_of_central_odd (oddCoreRep ρ) hperf μ hμc hdom 3
    (by rw [oddCore_finrank_fin_eight_fun]; norm_num) hμodd
  exact hμ1' (oddCoreRep_injective ρ hρ (by rw [hone, map_one]))

end CFSG.OddStandard.Seitz77
