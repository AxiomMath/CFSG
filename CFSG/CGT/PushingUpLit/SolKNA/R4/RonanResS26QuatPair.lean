module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open QuaternionGroup

theorem quatPair_a_pow {n : ℕ} (i : ZMod (2 * n)) (k : ℕ) :
    (a i : QuaternionGroup n) ^ k = a ((k : ZMod (2 * n)) * i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, a_mul_a]
    congr 1
    push_cast
    ring

theorem quatPair_a_pow_n {n : ℕ} [NeZero n] (i : ZMod (2 * n))
    (ho : orderOf (a i : QuaternionGroup n) = 2 * n) :
    (a i : QuaternionGroup n) ^ n = a (n : ZMod (2 * n)) := by
  haveI : NeZero (2 * n) := ⟨by have := NeZero.ne n; omega⟩
  have hi : (n : ZMod (2 * n)) * i = ((n * i.val : ℕ) : ZMod (2 * n)) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [quatPair_a_pow, hi]
  rcases Nat.even_or_odd i.val with ⟨j, hj⟩ | ⟨j, hj⟩
  ·
    exfalso
    have h0 : ((n * i.val : ℕ) : ZMod (2 * n)) = 0 := by
      rw [hj, show n * (j + j) = j * (2 * n) by ring, Nat.cast_mul, ZMod.natCast_self, mul_zero]
    have hpow : (a i : QuaternionGroup n) ^ n = 1 := by
      rw [quatPair_a_pow, hi, h0, a_zero]
    have hdvd : orderOf (a i : QuaternionGroup n) ∣ n := orderOf_dvd_of_pow_eq_one hpow
    rw [ho] at hdvd
    have hpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have hle := Nat.le_of_dvd hpos hdvd
    omega
  ·
    congr 1
    rw [hj, show n * (2 * j + 1) = n + j * (2 * n) by ring, Nat.cast_add, Nat.cast_mul,
      ZMod.natCast_self, mul_zero, add_zero]

theorem quatPair_aux {G : Type*} [Group G] {Q : Subgroup G} {n : ℕ} [NeZero n] (hn : 4 ≤ n)
    (e : ↥Q ≃* QuaternionGroup n) {u : G} (huQ : u ∈ Q) (hou : orderOf u = 2 * n) :
    ∃ b : G, b ∈ Q ∧ b * u * b⁻¹ = u⁻¹ ∧ b * b = u ^ n := by
  let φ : QuaternionGroup n →* G := Q.subtype.comp e.symm.toMonoidHom
  obtain ⟨v, hv⟩ : ∃ v, e ⟨u, huQ⟩ = v := ⟨_, rfl⟩
  have hφv : φ v = u := by
    rw [← hv]
    change ((e.symm (e ⟨u, huQ⟩) : ↥Q) : G) = u
    rw [MulEquiv.symm_apply_apply]
  have hord : orderOf v = 2 * n := by
    rw [← hv, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hou]
  rcases v with i | i
  · have hpow : (a i : QuaternionGroup n) ^ n = a (n : ZMod (2 * n)) :=
      quatPair_a_pow_n i hord
    have h1 : (xa 0 : QuaternionGroup n) * a i * (xa 0)⁻¹ = (a i)⁻¹ := by
      rw [mul_inv_eq_iff_eq_mul]
      show xa (0 + i) = a (-i) * xa 0
      rw [a_mul_xa]
      congr 1
      ring
    have hxx : (xa 0 : QuaternionGroup n) * xa 0 = a (n : ZMod (2 * n)) := by
      rw [xa_mul_xa, add_zero, sub_zero]
    refine ⟨φ (xa 0), (e.symm _).2, ?_, ?_⟩
    · rw [← hφv]
      calc φ (xa 0) * φ (a i) * (φ (xa 0))⁻¹ = φ (xa 0 * a i * (xa 0)⁻¹) := by
            simp only [map_mul, map_inv]
        _ = φ ((a i)⁻¹) := by rw [h1]
        _ = (φ (a i))⁻¹ := map_inv φ _
    · rw [← hφv]
      calc φ (xa 0) * φ (xa 0) = φ (xa 0 * xa 0) := (map_mul φ _ _).symm
        _ = φ (a (n : ZMod (2 * n))) := by rw [hxx]
        _ = φ ((a i) ^ n) := by rw [hpow]
        _ = (φ (a i)) ^ n := map_pow φ _ _
  ·
    exfalso
    rw [orderOf_xa] at hord
    omega

theorem exists_quat_pair_of_mem {G : Type*} [Group G] {Q : Subgroup G} {r : ℕ} (hr : 4 ≤ r)
    (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) {u : G} (huQ : u ∈ Q)
    (hou : orderOf u = 2 ^ (r - 1)) :
    ∃ b : G, b ∈ Q ∧ b * u * b⁻¹ = u⁻¹ ∧ b * b = u ^ 2 ^ (r - 2) := by
  have h4 : (4 : ℕ) ≤ 2 ^ (r - 2) :=
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ (r - 1) = 2 * 2 ^ (r - 2) := by
    rw [show r - 1 = (r - 2) + 1 by omega, pow_succ, mul_comm]
  haveI : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
  exact quatPair_aux h4 e huQ (hou.trans h2)

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
