module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmsF

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

namespace U3C1OuterSwapHigh

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G} {w s : G} {P : Subgroup G}
  (hW : U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P)
include hW

theorem gmg_mem_T₁_of_commute_t {c : G} (hc : c ∈ U₁) (hct : c * t = t * c) : c ∈ szT₁ L T := by
  have hS := hW.step
  have hL := hW.level
  have hσ : c * t * c⁻¹ * t⁻¹ ∈ szA₁ (szT₁ L T) := by
    rw [hct, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  obtain ⟨y, hy, r, hr, rfl⟩ := ncyc_exists_mul_of_mem_sup (hL.muOne_T₁_le_normalizer hS)
    (hL.muOne_mem_sup_of_comm_t_mem_szA₁ hS hc hσ)
  have hyt : y * t = t * y := mem_centralizer_iff.mp hS.start.mem_centralizer_szT₁ y hy
  have hrt : r * t = t * r := by
    have e : y * (r * t) = y * (t * r) := by
      calc y * (r * t) = y * r * t := (mul_assoc y r t).symm
        _ = t * (y * r) := hct
        _ = y * (t * r) := by rw [← mul_assoc, ← hyt, mul_assoc]
    exact mul_left_cancel e
  have hrr : r⁻¹ = r := by
    rw [← hS.conf.inv r hr, ← hrt, mul_inv_cancel_right]
  have hr2 : r ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [← hrr]
    exact mul_inv_cancel r
  exact mul_mem hy (mem_szA₁.mp (hS.conf.omega r hr hr2)).1

theorem gmg_mem_szA₁_of_commute_t {c : G} (hc : c ∈ U₁ ⊓ centralizer ({t * w} : Set G))
    (hct : c * t = t * c) : c ∈ szA₁ (szT₁ L T) := by
  have hS := hW.step
  obtain ⟨hcU, hcC⟩ := mem_inf.mp hc
  have hcT₁ := hW.gmg_mem_T₁_of_commute_t hcU hct
  have hctw : c * (t * w) = t * w * c := mem_centralizer_singleton_iff.mp hcC
  have hwc : w * c = c * w := by
    have e : t * (c * w) = t * (w * c) := by
      calc t * (c * w) = t * c * w := (mul_assoc t c w).symm
        _ = c * (t * w) := by rw [← hct, mul_assoc]
        _ = t * w * c := hctw
        _ = t * (w * c) := mul_assoc t w c
    exact (mul_left_cancel e).symm
  exact (hS.start.outer_facts_of_card_sylow hS.card_sylow hW.w_mem hW.w_sq hW.w_not_mem).2.2.1
    c hcT₁ hwc

theorem gmg_mem_szA₁_of_commute_w {c : G} (hc : c ∈ U₁ ⊓ centralizer ({t * w} : Set G))
    (hcw : c * w = w * c) : c ∈ szA₁ (szT₁ L T) := by
  have hctw : c * (t * w) = t * w * c := mem_centralizer_singleton_iff.mp (mem_inf.mp hc).2
  refine hW.gmg_mem_szA₁_of_commute_t hc ?_
  have e : c * t * w = t * c * w := by
    calc c * t * w = c * (t * w) := mul_assoc c t w
      _ = t * w * c := hctw
      _ = t * (w * c) := mul_assoc t w c
      _ = t * (c * w) := by rw [hcw]
      _ = t * c * w := (mul_assoc t c w).symm
  exact mul_right_cancel e

theorem gmg_not_le_szA₁ : ¬ U₁ ⊓ centralizer ({t * w} : Set G) ≤ szA₁ (szT₁ L T) := by
  intro hle
  have hS := hW.step
  obtain ⟨-, hA₁card, -⟩ := hS.start.facts_of_card_sylow hS.card_sylow
  have h1 := Subgroup.card_le_of_le hle
  rw [hW.card_F, hA₁card] at h1
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (le_trans (by norm_num) hS.start.two_le)
  have : 2 ^ f * 2 ≤ 2 ^ f * 2 ^ f := Nat.mul_le_mul_left _ hq
  nlinarith

theorem gmg_exists_not_commute (x : G) (hx : x = t ∨ x = w) :
    ∃ c ∈ U₁ ⊓ centralizer ({t * w} : Set G), c * x ≠ x * c := by
  by_contra hno
  push Not at hno
  apply hW.gmg_not_le_szA₁
  intro c hc
  rcases hx with rfl | rfl
  · exact hW.gmg_mem_szA₁_of_commute_t hc (hno c hc)
  · exact hW.gmg_mem_szA₁_of_commute_w hc (hno c hc)

end U3C1OuterSwapHigh

end CFSG.SeitzReduction.RankOne
