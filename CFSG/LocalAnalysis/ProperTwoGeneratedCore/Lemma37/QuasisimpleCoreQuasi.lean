module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreSetting

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {w : J}

namespace Setting

theorem orderOf_eq_four (h : Setting J Q B) (hw : w * w = centralElt J) : orderOf w = 4 := by
  have h4 : orderOf w = 2 ^ (1 + 1) := by
    refine orderOf_eq_prime_pow ?_ ?_
    · rw [pow_one, pow_two, hw]
      exact h.centralElt_ne_one
    · rw [show 2 ^ (1 + 1) = 2 + 2 by norm_num, pow_add, pow_two, hw, h.centralElt_mul_self]
  rw [h4]
  norm_num

theorem conj_mem_zpowers_of_comm_mem_center (h : Setting J Q B) (hw : w * w = centralElt J)
    {x : J} (hx : x * w * x⁻¹ * w⁻¹ ∈ Subgroup.center J) {y : J}
    (hy : y ∈ Subgroup.zpowers w) : x * y * x⁻¹ ∈ Subgroup.zpowers w := by
  have hxw : x * w * x⁻¹ ∈ Subgroup.zpowers w := by
    have hxw' : x * w * x⁻¹ = (x * w * x⁻¹ * w⁻¹) * w := by group
    rcases h.mem_center_iff.mp hx with h1 | he
    · rw [hxw', h1, one_mul]
      exact Subgroup.mem_zpowers w
    · rw [hxw', he, ← hw]
      exact (Subgroup.zpowers w).mul_mem ((Subgroup.zpowers w).mul_mem (Subgroup.mem_zpowers w)
        (Subgroup.mem_zpowers w)) (Subgroup.mem_zpowers w)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hconj : x * w ^ k * x⁻¹ = (x * w * x⁻¹) ^ k := by
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
  rw [hconj]
  exact (Subgroup.zpowers w).zpow_mem hxw k

theorem comm_mem_center_of_conj_mem_zpowers (h : Setting J Q B) (hw : w * w = centralElt J)
    {x : J} (hx : x * w * x⁻¹ ∈ Subgroup.zpowers w) : x * w * x⁻¹ * w⁻¹ ∈ Subgroup.center J := by
  have hord := h.orderOf_eq_four hw
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, hord] at hk
  have h0 := Int.emod_nonneg k (show ((4 : ℕ) : ℤ) ≠ 0 by norm_num)
  have h4 := Int.emod_lt_of_pos k (show (0 : ℤ) < ((4 : ℕ) : ℤ) by norm_num)
  generalize k % ((4 : ℕ) : ℤ) = r at hk h0 h4
  have hw1 : w ≠ 1 := fun h1 => h.centralElt_ne_one (by rw [← hw, h1, mul_one])
  push_cast at h4
  interval_cases r
  · exfalso
    rw [zpow_zero, eq_comm, conj_eq_one_iff] at hk
    exact hw1 hk
  · rw [← hk, zpow_one, mul_inv_cancel]
    exact (Subgroup.center J).one_mem
  · exfalso
    have hwe : w = centralElt J := by
      have hk' : x * w * x⁻¹ = centralElt J := by
        rw [← hk, ← hw, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two]
      have := congrArg (fun y => x⁻¹ * y * x) hk'
      simp only [(h.commute_centralElt x⁻¹).eq, mul_assoc, inv_mul_cancel_left, mul_one,
        inv_mul_cancel] at this
      exact this
    apply h.centralElt_ne_one
    calc centralElt J = w * w := hw.symm
      _ = centralElt J * centralElt J := by rw [hwe]
      _ = 1 := h.centralElt_mul_self
  · rw [← hk, show (3 : ℤ) = ((2 : ℕ) : ℤ) + 1 by norm_num, zpow_add, zpow_natCast, zpow_one,
      mul_inv_cancel_right, pow_two, hw]
    exact h.centralElt_mem_center

theorem mem_normalizer_zpowers_iff (h : Setting J Q B) (hw : w * w = centralElt J) {x : J} :
    x ∈ Subgroup.normalizer (Subgroup.zpowers w : Set J) ↔
      x * w * x⁻¹ * w⁻¹ ∈ Subgroup.center J := by
  constructor
  · intro hx
    exact h.comm_mem_center_of_conj_mem_zpowers hw
      ((Subgroup.mem_normalizer_iff.mp hx w).mp (Subgroup.mem_zpowers w))
  · intro hx
    have hx' : x⁻¹ * w * x⁻¹⁻¹ * w⁻¹ ∈ Subgroup.center J := by
      rw [← commute_mk_iff] at hx ⊢
      rw [QuotientGroup.mk_inv]
      exact hx.inv_left
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨h.conj_mem_zpowers_of_comm_mem_center hw hx, fun hy => ?_⟩
    have := h.conj_mem_zpowers_of_comm_mem_center hw hx' hy
    simpa [mul_assoc] using this

theorem mem_normalizer_zpowers_iff_commute (h : Setting J Q B) (hw : w * w = centralElt J)
    {x : J} : x ∈ Subgroup.normalizer (Subgroup.zpowers w : Set J) ↔
      Commute (x : J ⧸ Subgroup.center J) (w : J ⧸ Subgroup.center J) := by
  rw [h.mem_normalizer_zpowers_iff hw, commute_mk_iff]

end Setting

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
