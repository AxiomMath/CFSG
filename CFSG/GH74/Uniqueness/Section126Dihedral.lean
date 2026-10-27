module

public import CFSG.GH74.Uniqueness.Dihedral
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Dihedral2

variable {X : Type*} [Group X]

theorem card_closure_pair_involutions [Finite X] {s t : X} (hs : orderOf s = 2)
    (ht : orderOf t = 2) :
    Nat.card ↥(Subgroup.closure ({s, t} : Set X)) = 2 * orderOf (s * t) := by
  have hs1 : s * s = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs, pow_two] at this
  have ht1 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht, pow_two] at this
  have hsne : s ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hs
    omega
  have htne : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    omega
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs1
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht1
  set H := Subgroup.closure ({s, t} : Set X) with hH
  have hsH : s ∈ H := Subgroup.subset_closure (by simp)
  have htH : t ∈ H := Subgroup.subset_closure (by simp)
  set ρ : H := ⟨s * t, H.mul_mem hsH htH⟩ with hρ
  set σ : H := ⟨s, hsH⟩ with hσ
  have hσ2 : σ ^ 2 = 1 := by
    apply Subtype.ext
    simp [hσ, pow_two, hs1]
  have hrel : σ * ρ * σ⁻¹ = ρ⁻¹ := by
    apply Subtype.ext
    simp only [hσ, hρ, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, hsi, hti]
    rw [← mul_assoc, hs1, one_mul]
  have hgen : (⊤ : Subgroup H) = Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ := by
    refine (eq_top_iff.mpr ?_).symm
    rintro ⟨x, hx⟩ -
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | hy
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers σ)
      · have hy' : y = t := hy
        subst hy'
        have e : (⟨y, htH⟩ : H) = σ⁻¹ * ρ := by
          apply Subtype.ext
          simp only [hσ, hρ, Subgroup.coe_mul, Subgroup.coe_inv, hsi]
          rw [← mul_assoc, hs1, one_mul]
        rw [e]
        exact Subgroup.mul_mem _
          (Subgroup.inv_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers σ)))
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers ρ))
    | one => exact Subgroup.one_mem _
    | mul a b _ _ ha hb => exact Subgroup.mul_mem _ ha hb
    | inv a _ ha => exact Subgroup.inv_mem _ ha
  have hσρ : σ ∉ Subgroup.zpowers ρ := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hcomm : σ * ρ = ρ * σ := by
      rw [← hk]
      exact ((Commute.refl ρ).zpow_right k).symm.eq
    have hρ2 : ρ * ρ = 1 := by
      have h1 : σ * ρ * σ⁻¹ = ρ := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      rw [hrel] at h1
      exact inv_eq_iff_mul_eq_one.mp h1
    have hρ2' : ρ ^ 2 = 1 := by rwa [pow_two]
    have hk' : ρ ^ k = ρ ^ (k % 2) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul]
      rw [show ρ ^ (2 : ℤ) = 1 by exact_mod_cast hρ2', one_zpow, mul_one]
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [h0, zpow_zero] at hk'
      rw [hk'] at hk
      have : (σ : X) = 1 := by rw [← hk]; rfl
      exact hsne this
    · rw [h1, zpow_one] at hk'
      rw [hk'] at hk
      have h2 : s = s * t := congrArg Subtype.val hk.symm
      exact htne ((mul_eq_left.mp h2.symm))
  obtain ⟨e⟩ := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem ρ σ hgen hσ2 hrel hσρ
  have hρo : orderOf ρ = orderOf (s * t) := by
    rw [← Subgroup.orderOf_coe]
  have : NeZero (orderOf ρ) := ⟨(orderOf_pos ρ).ne'⟩
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hρo]

theorem exists_conj_mul_pow_of_odd_half {s t : X} (hs : s * s = 1) (ht : t * t = 1) {m : ℕ}
    (hord : orderOf (s * t) = 2 * m) (hm : Odd m) :
    ∃ x ∈ Subgroup.closure ({s, t} : Set X), x⁻¹ * t * x = s * (s * t) ^ m := by
  obtain ⟨j, hj⟩ := hm
  set w := s * t with hw
  have hw2 : w ^ (2 * m) = 1 := by rw [← hord]; exact pow_orderOf_eq_one w
  have hv2 : w ^ m * w ^ m = 1 := by rw [← pow_add, ← two_mul]; exact hw2
  have hvinv : (w ^ m)⁻¹ = w ^ m := inv_eq_of_mul_eq_one_right hv2
  have hsw : ∀ n : ℕ, s * w ^ n = (w ^ n)⁻¹ * s := fun n => by
    have := (semiconj_mul_of_sq hs ht).pow_right n
    rw [SemiconjBy, inv_pow] at this
    exact this
  have htw : ∀ n : ℕ, t * w ^ n = (w ^ n)⁻¹ * t := fun n => by
    have := (semiconj_mul_of_sq' hs ht).pow_right n
    rw [SemiconjBy, inv_pow] at this
    exact this
  have hsv : s * w ^ m = w ^ m * s := by rw [hsw m, hvinv]
  have hmem : w ∈ Subgroup.closure ({s, t} : Set X) :=
    mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  refine ⟨(w ^ (j + 1))⁻¹, Subgroup.inv_mem _ (Subgroup.pow_mem _ hmem _), ?_⟩
  have hti : ∀ n : ℕ, t * (w ^ n)⁻¹ = w ^ n * t := fun n => by
    have h := htw n
    have : (w ^ n)⁻¹ * (t * (w ^ n)⁻¹) = (w ^ n)⁻¹ * (w ^ n * t) := by
      calc (w ^ n)⁻¹ * (t * (w ^ n)⁻¹) = ((w ^ n)⁻¹ * t) * (w ^ n)⁻¹ := by rw [mul_assoc]
        _ = (t * w ^ n) * (w ^ n)⁻¹ := by rw [h]
        _ = t := by rw [mul_assoc, mul_inv_cancel, mul_one]
        _ = (w ^ n)⁻¹ * (w ^ n * t) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    exact mul_left_cancel this
  have hwt : w * t = s := by rw [hw, mul_assoc, ht, mul_one]
  calc ((w ^ (j + 1))⁻¹)⁻¹ * t * (w ^ (j + 1))⁻¹
      = w ^ (j + 1) * (t * (w ^ (j + 1))⁻¹) := by rw [inv_inv, mul_assoc]
    _ = w ^ (j + 1) * (w ^ (j + 1) * t) := by rw [hti]
    _ = w ^ (j + 1 + (j + 1)) * t := by rw [← mul_assoc, ← pow_add]
    _ = w ^ (2 * j + 1) * (w * t) := by
        rw [show j + 1 + (j + 1) = (2 * j + 1) + 1 by ring, pow_succ, mul_assoc]
    _ = w ^ m * s := by rw [hwt, hj]
    _ = s * w ^ m := hsv.symm

end Dihedral2

end CFSG.GH74.Uniqueness
