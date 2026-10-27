module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6dBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6d

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

theorem isPGroup_zpowers_of_sq {Y : Type} [Group Y] {c : Y} (h : c * c = 1) :
    IsPGroup 2 ↥(Subgroup.zpowers c) := by
  refine isPGroup_two_of_sq_eq_one fun d hd => ?_
  obtain ⟨k, rfl⟩ := hd
  rw [← (Commute.refl c).mul_zpow k, h, one_zpow]

theorem exists_order_five_aeSub : ∃ x ∈ aeSub 6, mkQ 6 x ^ 5 = 1 ∧ mkQ 6 x ≠ 1 := by
  let x₀ : Wr 6 := ⟨0, Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4⟩
  have hx₀ : x₀ ∈ aeSub 6 := ⟨by simp [Wr.wsum, x₀], by decide +kernel⟩
  have h5 : x₀ ^ 5 = 1 := by decide +kernel
  refine ⟨x₀, hx₀, by rw [← map_pow, h5, map_one], fun h => ?_⟩
  have h1 : x₀ ∈ piSub 6 := (QuotientGroup.eq_one_iff (N := piSub 6) _).mp h
  rcases mem_piSub.mp h1 with h2 | h2
  · exact absurd (congrArg Wr.perm h2) (by decide +kernel)
  · exact absurd (congrArg Wr.perm h2) (by decide +kernel)


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}

section Layer

variable (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
include H

theorem isPGroup_zpowers_u : IsPGroup 2 ↥(Subgroup.zpowers (u₁ * u₂)) :=
  isPGroup_zpowers_of_sq H.ex.1.datum.sq_12

theorem K₃_le_rLayer : K₃ ≤ rLayer Ω[R] (u₁ * u₂) :=
  Asc77.C22G.le_rLayer_of_le_centralizer
    (Q3.TC.mem_RSet_of_isPGroup H.ex.1.datum.hK₃.1 (h2Of H K₃ H.ex.1.datum.hK₃.1)) (K₃_le_C H)

theorem exists_order_five : ∃ y ∈ rLayer Ω[R] (u₁ * u₂), orderOf y = 5 := by
  obtain ⟨I₆⟩ := H.ae6
  obtain ⟨x₀, hx₀, h5, hne⟩ := exists_order_five_aeSub
  have hord : orderOf (mkQ 6 x₀) = 5 := orderOf_eq_prime h5 hne
  have hmem : mkQ 6 x₀ ∈ I₆.φ.range := by
    rw [I₆.range_eq]
    exact ⟨x₀, hx₀, rfl⟩
  obtain ⟨yb, hyb⟩ := hmem
  have h1 : 5 ∣ orderOf yb := by
    rw [← hord, ← hyb]
    exact orderOf_map_dvd I₆.φ yb
  have h2 : 5 ∣ orderOf (yb : ↥(coreHull Ω[R] (u₁ * u₂)) ⧸
      classicalInvolutionOddCore ↥(coreHull Ω[R] (u₁ * u₂))) := by
    rwa [Subgroup.orderOf_coe]
  obtain ⟨y₁, hy₁⟩ := QuotientGroup.mk_surjective (yb : ↥(coreHull Ω[R] (u₁ * u₂)) ⧸
      classicalInvolutionOddCore ↥(coreHull Ω[R] (u₁ * u₂)))
  have h3 : 5 ∣ orderOf y₁ := by
    refine h2.trans ?_
    rw [← hy₁]
    exact orderOf_map_dvd (QuotientGroup.mk' _) y₁
  have h4 : orderOf (y₁ ^ (orderOf y₁ / 5)) = 5 :=
    orderOf_pow_orderOf_div (orderOf_pos y₁).ne' h3
  refine ⟨(((y₁ ^ (orderOf y₁ / 5) : ↥(coreHull Ω[R] (u₁ * u₂))) :
      ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y), ?_, ?_⟩
  · exact coreHull_map_le_rLayer (hypOf H) (isPGroup_zpowers_u H) ⟨_, (y₁ ^ (orderOf y₁ / 5)).2, rfl⟩
  · have e : orderOf ((((y₁ ^ (orderOf y₁ / 5) : ↥(coreHull Ω[R] (u₁ * u₂))) :
        ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y)) = orderOf (y₁ ^ (orderOf y₁ / 5)) := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    rw [e, h4]

end Layer

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6d
