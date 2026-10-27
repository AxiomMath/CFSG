module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I1420

open scoped Pointwise

theorem no_order_five_mul_of_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {y0 : G} (hy0 : orderOf y0 = p)
    (hfac : (Nat.card G).factorization p = 1)
    (hcent : ∀ c : G, c * y0 = y0 * c → c ^ 5 = 1 → c = 1) (g : G) :
    orderOf g ≠ 5 * p := by
  intro hg
  have hp : p.Prime := Fact.out
  have hpos : 0 < orderOf g := by rw [hg]; exact Nat.mul_pos (by norm_num) hp.pos
  have hy : orderOf (g ^ 5) = p := by
    rw [orderOf_pow' _ (by norm_num), hg, Nat.gcd_eq_right (dvd_mul_right 5 p)]
    exact Nat.mul_div_cancel_left p (by norm_num)
  have hx : orderOf (g ^ p) = 5 := by
    rw [orderOf_pow' _ hp.ne_zero, hg, Nat.gcd_eq_right (dvd_mul_left p 5)]
    exact Nat.mul_div_cancel 5 hp.pos
  set y := g ^ 5 with hydef
  set x := g ^ p with hxdef
  have hcomm : Commute x y := Commute.pow_pow_self g p 5
  have hP : Nat.card (Subgroup.zpowers y) = p ^ (Nat.card G).factorization p := by
    rw [Nat.card_zpowers, hy, hfac, pow_one]
  have hQ : Nat.card (Subgroup.zpowers y0) = p ^ (Nat.card G).factorization p := by
    rw [Nat.card_zpowers, hy0, hfac, pow_one]
  let P : Sylow p G := Sylow.ofCard (Subgroup.zpowers y) hP
  let Q : Sylow p G := Sylow.ofCard (Subgroup.zpowers y0) hQ
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G P Q
  have h1 : (MulAut.conj a • y : G) ∈ MulAut.conj a • (P : Subgroup G) :=
    Subgroup.smul_mem_pointwise_smul y (MulAut.conj a) _ (Subgroup.mem_zpowers y)
  rw [← Sylow.coe_subgroup_smul, ha] at h1
  have hz : a * y * a⁻¹ ∈ Subgroup.zpowers y0 := h1
  have hzord : orderOf (a * y * a⁻¹) = p := by
    have := MulEquiv.orderOf_eq (MulAut.conj a) y
    rw [MulAut.conj_apply] at this
    rw [this, hy]
  have hle : Subgroup.zpowers (a * y * a⁻¹) ≤ Subgroup.zpowers y0 := Subgroup.zpowers_le.2 hz
  have heq : Subgroup.zpowers (a * y * a⁻¹) = Subgroup.zpowers y0 :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Nat.card_zpowers, Nat.card_zpowers, hzord, hy0])
  have hy0z : y0 ∈ Subgroup.zpowers (a * y * a⁻¹) := heq ▸ Subgroup.mem_zpowers y0
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy0z
  have hcomm' : Commute (a * x * a⁻¹) (a * y * a⁻¹) := by
    have := hcomm.map (MulAut.conj a : G ≃* G).toMonoidHom
    simpa [MulAut.conj_apply] using this
  have hc0 : Commute (a * x * a⁻¹) y0 := by
    rw [← hk]
    exact hcomm'.zpow_right k
  have hx5' : x ^ 5 = 1 := by
    rw [hxdef, ← pow_mul, mul_comm, ← hg]
    exact pow_orderOf_eq_one g
  have hx5 : (a * x * a⁻¹) ^ 5 = 1 := by
    have : (MulAut.conj a x) ^ 5 = MulAut.conj a (x ^ 5) := (map_pow (MulAut.conj a) x 5).symm
    rw [MulAut.conj_apply, hx5', map_one] at this
    exact this
  have h1' := hcent _ hc0.eq hx5
  have hx1 : x = 1 := by
    rw [mul_inv_eq_one, mul_eq_left] at h1'
    exact h1'
  rw [hx1, orderOf_one] at hx
  exact absurd hx (by norm_num)

end CFSG.HardMathSupport.Solomon.Coordinator.I1420
