module

public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamL43Aux
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools Blueprint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

namespace Lem711Cfg

variable {X : Type} [Group X] [Finite X] {L K : Subgroup X} {x y : X}

theorem q_eq_three_of_proj2 (h : Lem711Cfg X L K x y) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    {E : Type} [Field E] [Finite E] (hE : Nat.card E = (p ^ f) ^ 2) (eK : ↥K ≃* projectiveSL 2 E) :
    p = 3 ∧ f = 1 := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hpf3 : 3 ≤ p ^ f := by
    have : 3 ≤ p := by
      have := hp.two_le
      obtain ⟨t, ht⟩ := hodd
      omega
    exact this.trans (Nat.le_self_pow (by omega) p)
  have hEc : 4 ≤ Nat.card E := by rw [hE]; nlinarith
  obtain ⟨hKsimple, hZ⟩ := h.pPrimeCore_eq_bot_of_proj2 hEc eK
  have hKP : Nat.card ↥K = Nat.card E * (Nat.card E ^ 2 - 1) / 2 := by
    rw [Nat.card_congr eK.toEquiv,
      ← Nat.card_congr (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 E).toEquiv]
    exact CFSG.GorensteinWalter.psl2_card_formula E
      ⟨p, 2 * f, hp, hodd, by omega, by rw [hE, ← pow_mul, mul_comm]⟩
  have hKc : Nat.card ↥K = 360 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K)
    have h2 : Nat.card ↥(pPrimeCore 2 ↥K) = 1 := by rw [hZ]; exact Subgroup.card_bot
    rw [h2, mul_one, h.card_K_bar] at h1
    exact h1
  have hn : Nat.card E = 9 := by
    have h1 := hKP
    rw [hKc] at h1
    set n := Nat.card E with hn
    have hn2 : 2 ≤ n := by omega
    have h2 : n * (n ^ 2 - 1) = 720 := by
      have hev : Even (n * (n ^ 2 - 1)) := by
        rcases Nat.even_or_odd n with he | ho
        · exact he.mul_right _
        · have : Even (n ^ 2 - 1) := Nat.Odd.sub_odd ho.pow odd_one
          exact this.mul_left n
      have := Nat.div_mul_cancel hev.two_dvd
      omega
    have hle : n ≤ 9 := by
      by_contra hlt
      push Not at hlt
      have : 10 * (10 ^ 2 - 1) ≤ n * (n ^ 2 - 1) := Nat.mul_le_mul (by omega) (by
        have := Nat.pow_le_pow_left (show 10 ≤ n by omega) 2
        omega)
      omega
    interval_cases n <;> omega
  have hq3 : p ^ f = 3 := by
    rw [hE] at hn
    have : (p ^ f) ^ 2 = 3 ^ 2 := by rw [hn]; norm_num
    exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) this
  rcases L3Aut.odd_prime_pow_eq_three_or_five_le hp hp2 hf with h3 | h5
  · exact h3
  · omega

end Lem711Cfg

end CFSG.GH74.GLS
