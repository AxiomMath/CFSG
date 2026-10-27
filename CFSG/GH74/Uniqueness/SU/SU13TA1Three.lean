module

public import CFSG.GH74.Uniqueness.SU.SU13TA0
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverLift

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA

open Equiv Subgroup

variable {H : Type} [Group H] {n : ℕ} {π : H →* alternatingGroup (Fin n)}

namespace TwoCover

theorem isPGroup_ker' (hπ : TwoCover π) : IsPGroup 2 π.ker :=
  IsPGroup.of_card (n := 1) (by rw [hπ.card_ker, pow_one])

theorem sq_eq_one_of_mem_ker' (hπ : TwoCover π) {k : H} (hk : k ∈ π.ker) : k ^ 2 = 1 := by
  have h := pow_card_eq_one' (G := π.ker) (x := ⟨k, hk⟩)
  rw [hπ.card_ker] at h
  simpa using congrArg Subtype.val h

theorem finite' (hπ : TwoCover π) : Finite H := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ.surj).toEquiv,
    hπ.card_ker] at h1
  refine Nat.finite_of_card_ne_zero ?_
  rw [h1]
  have : 0 < Nat.card (alternatingGroup (Fin n)) := Nat.card_pos
  omega

theorem existsUnique_lift_pow_three (hπ : TwoCover π) (σ : alternatingGroup (Fin n))
    (hσ : σ ^ 3 = 1) : ∃! x : H, π x = σ ∧ x ^ 3 = 1 := by
  obtain ⟨y, rfl⟩ := hπ.surj σ
  obtain ⟨x, hx, hx3⟩ := CFSG.LocalAnalysis.ComponentInitial.exists_lift_pow_three_eq_one
    hπ.ker_le_center hπ.isPGroup_ker' hσ
  exact ⟨x, ⟨hx, hx3⟩, fun x' hx' =>
    CFSG.LocalAnalysis.ComponentInitial.eq_of_pow_three_eq_one_of_map_eq hπ.ker_le_center
      hπ.isPGroup_ker' hx'.2 hx3 (hx'.1.trans hx.symm)⟩

theorem commute_of_pow_three (hπ : TwoCover π) {x u : H} (hx : x ^ 3 = 1)
    (h : Commute (π u) (π x)) : Commute u x := by
  have hkk : u * x * u⁻¹ * x⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, h.eq, mul_inv_cancel_right, mul_inv_cancel]
  have hkx : Commute (u * x * u⁻¹ * x⁻¹) x :=
    (Subgroup.mem_center_iff.mp (hπ.ker_le_center hkk) x).symm
  have hk3 : (u * x * u⁻¹ * x⁻¹) ^ 3 = 1 := by
    have h3 : (u * x * u⁻¹) ^ 3 = 1 := by rw [conj_pow, hx, mul_one, mul_inv_cancel]
    rwa [show u * x * u⁻¹ = (u * x * u⁻¹ * x⁻¹) * x by group, hkx.mul_pow, hx, mul_one] at h3
  have hk1 : u * x * u⁻¹ * x⁻¹ = 1 := by
    calc u * x * u⁻¹ * x⁻¹
        = (u * x * u⁻¹ * x⁻¹) ^ 3 * ((u * x * u⁻¹ * x⁻¹) ^ 2)⁻¹ := by group
      _ = 1 := by rw [hk3, hπ.sq_eq_one_of_mem_ker' hkk, inv_one, one_mul]
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hk1
  exact hk1

end TwoCover

end CFSG.GH74.Uniqueness.SU.SU13.TA
