module

public import CFSG.GH74.KGroups.TwoM12Outer
public import CFSG.GroupTheory.NonabelianSimpleOrderSixty
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.GH74.KGroups.TwoM12

open Subgroup CFSG.Blueprint
open CFSG.GH74.E2 (Shape2M12)

variable {L : Type} [Group L] [Finite L]

theorem card_le_sixty_of_fixed
    (h : Shape2M12 L) (σ : MulAut L) (hσ2 : σ * σ = 1)
    (hσ1 : σ ≠ 1) {P : Subgroup L} (hP : ⁅P, P⁆ = P) (hPσ : ∀ x ∈ P, σ x = x) :
    Nat.card P ≤ 60 := by
  obtain ⟨t, π, hc⟩ := exists_isCover h
  have hq : CFSG.Assembly.IsQuasisimple L := ⟨Group.isPerfect_def.1 h.1.1, h.1.2.1⟩
  by_cases hin : ∃ u : L, ∀ x : L, σ x = u * x * u⁻¹
  · obtain ⟨u, hu⟩ := hin
    have huu : u * u ∈ center L := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 : σ (σ g) = g := by
        have := congrArg (fun f : MulAut L => f g) hσ2
        simpa using this
      rw [hu, hu] at h1
      have h2 : u * (u * g * u⁻¹) * u⁻¹ = g := h1
      calc g * (u * u) = (u * (u * g * u⁻¹) * u⁻¹) * (u * u) := by rw [h2]
        _ = (u * u) * g := by group
    have hπuu : π u * π u = 1 := by
      have : u * u ∈ π.ker := by rw [hc.ker_eq, ← hc.center_eq]; exact huu
      rw [← map_mul]
      exact this
    have hπu1 : π u ≠ 1 := by
      intro h1
      have hu_ker : u ∈ π.ker := h1
      rw [hc.ker_eq, ← hc.center_eq] at hu_ker
      apply hσ1
      ext x
      rw [hu, MulAut.one_apply]
      have := Subgroup.mem_center_iff.1 hu_ker x
      calc u * x * u⁻¹ = x * u * u⁻¹ := by rw [← this]
        _ = x := by group
    have hord : orderOf (π u) = 2 := orderOf_eq_prime (by rw [sq]; exact hπuu) hπu1
    refine card_le_sixty_of_inner hc hord hP fun x hx => ?_
    have h1 := hPσ x hx
    rw [hu] at h1
    calc x * u = (u * x * u⁻¹) * u := by rw [h1]
      _ = u * x := by group
  · exact card_le_sixty_of_outer hc hq σ hσ2 hσ1 hin hP hPσ

theorem card_quasisimple_fixed_of_shape2M12
    {K : Type} [Group K] [Finite K] (h : Shape2M12 K)
    (α : MulAut K) (hα2 : α ^ 2 = 1) (hα1 : α ≠ 1) (L' : Subgroup K) (hL' : ∀ x ∈ L', α x = x)
    (hq : CFSG.IsQuasisimple ↥L') : Nat.card ↥L' = 60 := by
  have hperf : ⁅L', L'⁆ = L' := Subgroup.isPerfect_iff.1 hq.1
  have hle := card_le_sixty_of_fixed h α (by rw [← sq]; exact hα2) hα1 hperf hL'
  have h60 : 60 ≤ Nat.card (↥L' ⧸ center ↥L') :=
    CFSG.GroupTheory.nonabelian_simple_order_at_least_sixty hq.2.1 hq.2.2
  have hcard : Nat.card ↥L' = Nat.card (↥L' ⧸ center ↥L') * Nat.card ↥(center ↥L') :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥L')
  have hpos : 0 < Nat.card ↥(center ↥L') := Nat.card_pos
  have : 60 ≤ Nat.card ↥L' := by
    rw [hcard]
    calc 60 = 60 * 1 := by norm_num
      _ ≤ _ := Nat.mul_le_mul h60 hpos
  omega

theorem pumpUp_of_shape2M12
    {K : Type} [Group K] [Finite K] (h : Shape2M12 K) :
    ∀ α : MulAut K, α ^ 2 = 1 → α ≠ 1 → ∀ L' : Subgroup K, (∀ x ∈ L', α x = x) →
      CFSG.IsQuasisimple ↥L' → Nat.card ↥L' = 60 ∨ Nat.card ↥L' = 120 :=
  fun α hα2 hα1 L' hL' hq => Or.inl (card_quasisimple_fixed_of_shape2M12 h α hα2 hα1 L' hL' hq)

end CFSG.GH74.KGroups.TwoM12
