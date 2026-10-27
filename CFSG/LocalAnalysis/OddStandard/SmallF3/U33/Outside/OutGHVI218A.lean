module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutSpecial
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutZmodProd

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Subgroup
open scoped commutatorElement

variable {S : Type} [Group S] [Finite S] {ρ : MulAut S}

private theorem sq_mem_zpowers_of_orderOf_eq_four {a g : S} (ha : orderOf a = 4)
    (hg : g ∈ zpowers a) (hg1 : g ≠ 1) : a * a ∈ zpowers g := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf] at hg
  obtain ⟨i, hi, hgi⟩ := Finset.mem_image.mp hg
  rw [Finset.mem_range, ha] at hi
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hgi
    exact hg1 hgi.symm
  have ha4 : a ^ 4 = 1 := by rw [← ha, pow_orderOf_eq_one]
  interval_cases i
  · exact absurd rfl hi0
  · have hai : a = g := by rwa [pow_one] at hgi
    rw [hai]
    simpa [pow_two] using Subgroup.npow_mem_zpowers g 2
  · have hai : a ^ 2 = g := hgi
    rw [← pow_two]
    rw [hai]
    exact Subgroup.mem_zpowers g
  · have h : a ^ 2 = g ^ 2 := by
      rw [← hgi, ← pow_mul]
      rw [show (3 : ℕ) * 2 = 2 + 4 by norm_num, pow_add, ha4, mul_one]
    rw [← pow_two, h]
    exact Subgroup.npow_mem_zpowers g 2

theorem FpfNonab.exists_order_four (h : FpfNonab S ρ) : ∃ x : S, orderOf x = 4 := by
  by_contra hno
  simp only [not_exists] at hno
  have hexp : ∀ x : S, x * x = 1 := by
    intro x
    have hx4 : x ^ 4 = 1 := by
      have h4 := h.sq_center (x * x) (h.sq_mem x)
      rw [show x ^ 4 = (x * x) * (x * x) by
        rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two]]
      exact h4
    have hdvd : orderOf x ∣ 4 := orderOf_dvd_of_pow_eq_one hx4
    have hdvd' : orderOf x ∣ 2 ^ 2 := by
      rwa [show (2 : ℕ) ^ 2 = 4 by norm_num]
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
    have hdvd2 : orderOf x ∣ 2 := by
      have hk_ne : k ≠ 2 := by
        intro hk2'
        exact hno x (by rw [hk, hk2']; norm_num)
      have hk_le : k ≤ 1 := by omega
      rw [hk]
      simpa using pow_dvd_pow 2 hk_le
    have hx2 : x ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd2
    rwa [pow_two] at hx2
  obtain ⟨a, b, hab⟩ := h.nonab
  exact hab (by
    calc a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right (hexp (a * b))
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by
          rw [show b⁻¹ = b from (eq_inv_of_mul_eq_one_right (hexp b)).symm,
            show a⁻¹ = a from (eq_inv_of_mul_eq_one_right (hexp a)).symm])

theorem FpfNonab.commute_rho (h : FpfNonab S ρ) (x : S) : x * ρ x = ρ x * x := by
  set y : S := ρ x with hy
  have hburn : x * y * ρ y = 1 := forall_mul_rho_rho_sq ρ h.cube h.fpf x
  have hcZ : ⁅x, y⁆ ∈ center S := by
    simpa only [commutatorElement_def, hy] using h.comm_mem x (ρ x)
  have hcent : ∀ g : S, g * ⁅x, y⁆ = ⁅x, y⁆ * g :=
    fun g => Subgroup.mem_center_iff.mp hcZ g
  have hfix : ρ ⁅x, y⁆ = ⁅x, y⁆ := by
    have hry : ρ y = (x * y)⁻¹ := eq_inv_of_mul_eq_one_right hburn
    rw [map_commutatorElement, hry, commutatorElement_inv_right]
    have hxy : ⁅x * y, y⁆ = ⁅x, y⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul, commutatorElement_self, mul_one]
      group
    rw [hxy, hcent (x * y)⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  have h1 : ⁅x, y⁆ = 1 := h.fpf ⁅x, y⁆ hfix
  have hxy : x * y = y * x := commutatorElement_eq_one_iff_mul_comm.mp h1
  simpa [hy] using hxy

theorem FpfNonab.rho_sq_ne (h : FpfNonab S ρ) {x : S} (hx : orderOf x = 4) :
    ρ (x * x) ≠ x * x := by
  intro hfix
  have hx2 : x * x = 1 := h.fpf (x * x) hfix
  have hdvd : orderOf x ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    rwa [pow_two]
  rw [hx] at hdvd
  norm_num at hdvd

theorem FpfNonab.inf_zpowers_rho (h : FpfNonab S ρ) {x : S} (hx : orderOf x = 4) :
    zpowers x ⊓ zpowers (ρ x) = ⊥ := by
  classical
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  by_contra hg1
  have hgx : g ∈ zpowers x := hg.1
  have hgy : g ∈ zpowers (ρ x) := hg.2
  have hry : orderOf (ρ x) = 4 := by rw [MulEquiv.orderOf_eq, hx]
  have hx2g : x * x ∈ zpowers g := sq_mem_zpowers_of_orderOf_eq_four hx hgx hg1
  have hx2y : x * x ∈ zpowers (ρ x) := Subgroup.zpowers_le_of_mem hgy hx2g
  rw [mem_zpowers_iff_mem_range_orderOf] at hx2y
  obtain ⟨j, hj, hjx⟩ := Finset.mem_image.mp hx2y
  rw [Finset.mem_range, hry] at hj
  have hx2_ord : orderOf (x * x) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ (fun h1 => by
      have hdvd : orderOf x ∣ 2 := by
        apply orderOf_dvd_of_pow_eq_one
        rwa [pow_two]
      rw [hx] at hdvd
      norm_num at hdvd)
    rw [pow_two]
    exact h.sq_center (x * x) (h.sq_mem x)
  interval_cases j
  · exfalso
    rw [pow_zero] at hjx
    rw [← hjx, orderOf_one] at hx2_ord
    norm_num at hx2_ord
  · exfalso
    rw [pow_one] at hjx
    rw [← hjx, hry] at hx2_ord
    norm_num at hx2_ord
  · rw [pow_two] at hjx
    rw [← map_mul] at hjx
    exact (rho_sq_ne h hx) hjx
  · exfalso
    rw [← hjx] at hx2_ord
    rw [orderOf_pow, hry] at hx2_ord
    norm_num at hx2_ord

theorem FpfNonab.center_le_sup (h : FpfNonab S ρ) {x : S} (hx : orderOf x = 4) :
    center S ≤ zpowers x ⊔ zpowers (ρ x) := by
  classical
  have ha_mem : x * x ∈ center S := h.sq_mem x
  have hb_mem : ρ (x * x) ∈ center S := rho_mem_center ρ ha_mem
  have ha2 : (x * x) * (x * x) = 1 := h.sq_center (x * x) ha_mem
  have hb2 : (ρ (x * x)) * (ρ (x * x)) = 1 := h.sq_center (ρ (x * x)) hb_mem
  have ha1 : x * x ≠ 1 := by
    intro h1
    have hdvd : orderOf x ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      rwa [pow_two]
    rw [hx] at hdvd
    norm_num at hdvd
  have hb1 : ρ (x * x) ≠ 1 := by
    intro h1
    exact ha1 (ρ.injective (by rw [h1, map_one]))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha_ord : orderOf (x * x) = 2 :=
    orderOf_eq_prime (by rwa [pow_two]) ha1
  have hb_ord : orderOf (ρ (x * x)) = 2 :=
    orderOf_eq_prime (by rwa [pow_two]) hb1
  have hab : (x * x) * ρ (x * x) = ρ (x * x) * (x * x) :=
    (Subgroup.mem_center_iff.mp ha_mem (ρ (x * x))).symm
  have hinf : zpowers (x * x) ⊓ zpowers (ρ (x * x)) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    by_contra hg1
    have hga : g ∈ zpowers (x * x) := hg.1
    have hgb : g ∈ zpowers (ρ (x * x)) := hg.2
    rw [mem_zpowers_iff_mem_range_orderOf, ha_ord] at hga
    rw [mem_zpowers_iff_mem_range_orderOf, hb_ord] at hgb
    obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp hga
    obtain ⟨j, hj, hjb⟩ := Finset.mem_image.mp hgb
    rw [Finset.mem_range] at hi hj
    interval_cases i
    · rw [pow_zero] at hia
      exact hg1 hia.symm
    · interval_cases j
      · rw [pow_zero] at hjb
        exact hg1 hjb.symm
      · rw [pow_one] at hia hjb
        exact (rho_sq_ne h hx) (hjb.trans hia.symm)
  have hKle : zpowers (x * x) ⊔ zpowers (ρ (x * x)) ≤ center S :=
    sup_le (Subgroup.zpowers_le_of_mem ha_mem) (Subgroup.zpowers_le_of_mem hb_mem)
  have hKcard : Nat.card ↥(zpowers (x * x) ⊔ zpowers (ρ (x * x))) = 4 := by
    rw [card_zpowers_sup_zpowers (x * x) (ρ (x * x)) hab 2 ha_ord hb_ord hinf]
  have hKeq : zpowers (x * x) ⊔ zpowers (ρ (x * x)) = center S :=
    Subgroup.eq_of_le_of_card_ge hKle (le_of_eq (h.card_center.trans hKcard.symm))
  rw [← hKeq]
  exact sup_le
    (Subgroup.zpowers_le_of_mem
      (Subgroup.mem_sup_left (by simpa [pow_two] using Subgroup.npow_mem_zpowers x 2)))
    (Subgroup.zpowers_le_of_mem
      (Subgroup.mem_sup_right
        (by simpa [map_mul, pow_two] using Subgroup.npow_mem_zpowers (ρ x) 2)))

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
