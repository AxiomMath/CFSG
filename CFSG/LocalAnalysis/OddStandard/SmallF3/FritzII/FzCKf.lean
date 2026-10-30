module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCNorm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AB1A

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem fzc_card_K (hs : FzCSteps t L S x₁ x₂ lam rho) :
    Nat.card (twoCore t) = 2 ∨ Nat.card (twoCore t) = 4 := by
  obtain ⟨n, hn⟩ := (fzc_K_pGroup t).exists_card_eq
  have hle : 2 ^ n ≤ 4 := by rw [← hn]; exact hs.fusion.card_P_le
  have hne1 : 2 ^ n ≠ 1 := by
    intro h1
    have hcard : Nat.card (twoCore t) = 1 := by rw [hn, h1]
    have hbot : twoCore t = ⊥ := (Subgroup.card_eq_one (H := twoCore t)).mp hcard
    have ht : t ∈ twoCore t := hs.ctx.hyp.mem_twoCore
    rw [hbot] at ht
    have ht1 : t = 1 := Subgroup.mem_bot.mp ht
    have hord : orderOf t = 2 := hs.ctx.hyp.ord_t
    rw [ht1, orderOf_one] at hord
    omega
  have hnle : n ≤ 2 := by
    by_contra h
    push Not at h
    have h3 : 2 ^ 3 ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega)
    norm_num at h3
    omega
  have hn0 : n ≠ 0 := by rintro rfl; exact hne1 (pow_zero 2)
  have hn12 : n = 1 ∨ n = 2 := by omega
  rcases hn12 with rfl | rfl
  · left; rw [hn]; norm_num
  · right; rw [hn]; norm_num

theorem fzc_K_two (hs : FzCSteps t L S x₁ x₂ lam rho) (h2 : Nat.card (twoCore t) = 2) :
    twoCore t = zpowers t := by
  have hle : zpowers t ≤ twoCore t := Subgroup.zpowers_le_of_mem hs.ctx.hyp.mem_twoCore
  have hcard : Nat.card (twoCore t) ≤ Nat.card (zpowers t) := by
    rw [h2, Nat.card_zpowers, hs.ctx.hyp.ord_t]
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem fzc_K_four (hs : FzCSteps t L S x₁ x₂ lam rho) (h4 : Nat.card (twoCore t) = 4) :
    ∃ q : G, twoCore t = zpowers q ∧ orderOf q = 4 ∧ q ^ 2 = t := by
  haveI : IsCyclic (twoCore t) := hs.ctx.hyp.isCyclic
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := twoCore t)
  have hordg : orderOf g = 4 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, h4]
  have hordc : orderOf (g : G) = 4 := by rw [Subgroup.orderOf_coe]; exact hordg
  refine ⟨(g : G), ?_, hordc, ?_⟩
  · have hle : zpowers (g : G) ≤ twoCore t := Subgroup.zpowers_le_of_mem g.2
    have hcard : Nat.card (twoCore t) ≤ Nat.card (zpowers (g : G)) := by
      rw [h4, Nat.card_zpowers, hordc]
    exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm
  · have hgmem : (g : G) ^ 2 ∈ twoCore t := Subgroup.pow_mem _ g.2 2
    have hsq : ((g : G) ^ 2) ^ 2 = 1 := by
      rw [← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num,
        show (4 : ℕ) = orderOf (g : G) from hordc.symm]
      exact pow_orderOf_eq_one (g : G)
    rcases hs.ctx.hyp.eq_one_or_eq ((g : G) ^ 2) hgmem hsq with h | h
    · exfalso
      have hdvd : orderOf (g : G) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
      rw [hordc] at hdvd
      norm_num at hdvd
    · exact h

theorem fzc_card_W (hs : FzCSteps t L S x₁ x₂ lam rho) :
    Nat.card (ctxW t x₁ x₂) = 16 * Nat.card (twoCore t) := by
  rw [S4A.pt_card_W hs.ctx]
  norm_num

end CFSG.OddStandard.SmallF3.FritzII
