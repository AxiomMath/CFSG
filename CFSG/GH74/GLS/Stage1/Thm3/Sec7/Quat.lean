module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7.Q

open Subgroup

variable {G : Type*} [Group G]

structure QG (a b : G) (N : ℕ) : Prop where
  ord : orderOf a = 2 * N
  bsq : b * b = a ^ N
  bcomm : b * a = a⁻¹ * b

theorem quat_gens {P : Subgroup G} {N : ℕ} [NeZero N] (e : ↥P ≃* QuaternionGroup N) :
    ∃ a b : G, a ∈ P ∧ b ∈ P ∧ QG a b N ∧ ∀ x ∈ P, ∃ k : ℕ, x = a ^ k ∨ x = a ^ k * b := by
  let a₀ : ↥P := e.symm (QuaternionGroup.a 1)
  let b₀ : ↥P := e.symm (QuaternionGroup.xa 0)
  refine ⟨(a₀ : G), (b₀ : G), a₀.2, b₀.2, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq e.symm, QuaternionGroup.orderOf_a_one]
  · have h1 : b₀ * b₀ = a₀ ^ N := by
      apply e.injective
      rw [map_mul, map_pow]
      simp only [b₀, a₀, MulEquiv.apply_symm_apply]
      rw [QuaternionGroup.xa_mul_xa, QuaternionGroup.a_one_pow]
      congr 1
      simp
    exact congrArg Subtype.val h1
  · have h1 : b₀ * a₀ = a₀⁻¹ * b₀ := by
      apply e.injective
      rw [map_mul, map_mul, map_inv]
      simp only [b₀, a₀, MulEquiv.apply_symm_apply]
      have hinv : (QuaternionGroup.a (1 : ZMod (2 * N)))⁻¹ = QuaternionGroup.a (-1) := by
        apply inv_eq_of_mul_eq_one_right
        rw [QuaternionGroup.a_mul_a, add_neg_cancel, QuaternionGroup.a_zero]
      rw [hinv, QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa]
      congr 1
      simp
    exact congrArg Subtype.val h1
  · intro x hx
    obtain ⟨y, hy⟩ : ∃ y, y = e ⟨x, hx⟩ := ⟨_, rfl⟩
    have hxy : (⟨x, hx⟩ : ↥P) = e.symm y := by rw [hy, e.symm_apply_apply]
    cases y with
    | a i =>
      refine ⟨i.val, Or.inl ?_⟩
      have : (⟨x, hx⟩ : ↥P) = a₀ ^ i.val := by
        rw [hxy]
        apply e.injective
        simp only [map_pow, a₀, MulEquiv.apply_symm_apply]
        rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
      exact congrArg Subtype.val this
    | xa i =>
      refine ⟨(-i).val, Or.inr ?_⟩
      have : (⟨x, hx⟩ : ↥P) = a₀ ^ (-i).val * b₀ := by
        rw [hxy]
        apply e.injective
        rw [map_mul, map_pow]
        simp only [b₀, a₀, MulEquiv.apply_symm_apply]
        rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val, QuaternionGroup.a_mul_xa]
        congr 1
        simp
      exact congrArg Subtype.val this

namespace QG

variable {a b : G} {N : ℕ}

theorem b_pow (h : QG a b N) (k : ℕ) : b * a ^ k = (a ^ k)⁻¹ * b := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc b * a ^ (k + 1) = (b * a) * a ^ k := by rw [pow_succ']; group
      _ = a⁻¹ * (b * a ^ k) := by rw [h.bcomm]; group
      _ = a⁻¹ * ((a ^ k)⁻¹ * b) := by rw [ih]
      _ = (a ^ (k + 1))⁻¹ * b := by rw [pow_succ]; group

theorem a2N (h : QG a b N) : a ^ (2 * N) = 1 := by
  rw [← h.ord]; exact pow_orderOf_eq_one a

theorem aN_sq (h : QG a b N) : a ^ N * a ^ N = 1 := by
  rw [← pow_add, ← two_mul]; exact h.a2N

theorem aN_inv (h : QG a b N) : (a ^ N)⁻¹ = a ^ N := inv_eq_of_mul_eq_one_right h.aN_sq

theorem aN_ne_one (h : QG a b N) (hN : 1 ≤ N) : a ^ N ≠ 1 := by
  intro h1
  have := orderOf_dvd_of_pow_eq_one h1
  rw [h.ord] at this
  have := Nat.le_of_dvd (by omega) this
  omega

theorem b_aN (h : QG a b N) : b * a ^ N = a ^ N * b := by
  rw [h.b_pow, h.aN_inv]

theorem b_conj (h : QG a b N) (k : ℕ) : b * a ^ k * b⁻¹ = (a ^ k)⁻¹ := by
  rw [h.b_pow]; group

theorem b_inv_zpowers (h : QG a b N) {x : G} (hx : x ∈ zpowers a) : b * x * b⁻¹ = x⁻¹ := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  have h1 : b * a * b⁻¹ = a⁻¹ := by rw [h.bcomm]; group
  rw [← conj_zpow, h1, inv_zpow]

theorem eq_aN_of_involution (h : QG a b N) {P : Subgroup G} (hN : 1 ≤ N)
    (hgen : ∀ x ∈ P, ∃ k : ℕ, x = a ^ k ∨ x = a ^ k * b) {z : G} (hz : z ∈ P) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) : z = a ^ N := by
  obtain ⟨k, hk | hk⟩ := hgen z hz
  · subst hk
    have h1 : a ^ (2 * k) = 1 := by rw [two_mul, pow_add]; exact hz2
    have h2 : 2 * N ∣ 2 * k := by rw [← h.ord]; exact orderOf_dvd_of_pow_eq_one h1
    have h3 : N ∣ k := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
    obtain ⟨m, rfl⟩ := h3
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
    · exfalso; apply hz1
      rw [show N * (2 * j) = 2 * N * j by ring, pow_mul, h.a2N, one_pow]
    · rw [show N * (2 * j + 1) = 2 * N * j + N by ring, pow_add, pow_mul, h.a2N, one_pow, one_mul]
  · exfalso
    subst hk
    have : a ^ k * b * (a ^ k * b) = a ^ N := by
      calc a ^ k * b * (a ^ k * b) = a ^ k * (b * a ^ k) * b := by group
        _ = a ^ k * ((a ^ k)⁻¹ * b) * b := by rw [h.b_pow]
        _ = b * b := by group
        _ = a ^ N := h.bsq
    rw [this] at hz2
    exact h.aN_ne_one hN hz2

theorem exists_w2 {Q Mm : Subgroup G} {z v : G} {M : ℕ} (h : QG a b M) (hz : z = a ^ M)
    (ha : a ∈ Q) (hgen : ∀ x ∈ Q, ∃ k : ℕ, x = a ^ k ∨ x = a ^ k * b) (h4 : 4 ∣ M)
    (hsq : ∀ x ∈ Q, x * x ∈ Mm) (hvQ : v ∈ Q) (hvM : v ∉ Mm) (hv2 : v * v = z) :
    ∃ w ∈ Mm, w * w = z ∧ w * v * w⁻¹ = v⁻¹ := by
  obtain ⟨m, hm⟩ := h4
  have hzz : z * z = 1 := by rw [hz]; exact h.aN_sq
  refine ⟨a ^ (2 * m), ?_, ?_, ?_⟩
  · have := hsq (a ^ m) (Q.pow_mem ha m)
    rwa [← pow_add, ← two_mul] at this
  · rw [hz, hm, ← pow_add]; congr 1; ring
  · obtain ⟨k, hk | hk⟩ := hgen v hvQ
    · exfalso
      apply hvM
      obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
      · have := hsq (a ^ j) (Q.pow_mem ha j)
        rwa [← pow_add, ← two_mul, ← hk] at this
      · exfalso
        have h1 : a ^ (2 * (2 * j + 1)) = a ^ M := by
          rw [← hz, ← hv2, hk, ← pow_add, two_mul]
        rw [pow_eq_pow_iff_modEq, h.ord] at h1
        have h2 := Nat.ModEq.of_dvd (show 4 ∣ 2 * M from ⟨2 * m, by rw [hm]; ring⟩) h1
        rw [hm] at h2
        unfold Nat.ModEq at h2
        omega
    · have hvinv : v⁻¹ = v * z := by
        apply inv_eq_of_mul_eq_one_right
        rw [← mul_assoc, hv2, hzz]
      have hbz : b * z = z * b := by rw [hz]; exact h.b_aN
      have hWinv : (a ^ (2 * m))⁻¹ = a ^ (2 * M - 2 * m) := by
        apply inv_eq_of_mul_eq_one_right
        rw [← pow_add, Nat.add_sub_cancel' (by omega), h.a2N]
      have hbW : b * (a ^ (2 * m))⁻¹ = a ^ (2 * m) * b := by
        rw [hWinv, h.b_pow, ← hWinv, inv_inv]
      have hWb : a ^ (2 * m) * b * (a ^ (2 * m))⁻¹ = z * b := by
        calc a ^ (2 * m) * b * (a ^ (2 * m))⁻¹ = a ^ (2 * m) * (b * (a ^ (2 * m))⁻¹) := by group
          _ = a ^ (2 * m) * (a ^ (2 * m) * b) := by rw [hbW]
          _ = (a ^ (2 * m) * a ^ (2 * m)) * b := by group
          _ = z * b := by rw [← pow_add, hz, hm]; congr 2; ring
      have hcomm : a ^ (2 * m) * a ^ k = a ^ k * a ^ (2 * m) := pow_mul_comm a _ _
      rw [hvinv, hk]
      calc a ^ (2 * m) * (a ^ k * b) * (a ^ (2 * m))⁻¹
          = (a ^ (2 * m) * a ^ k) * b * (a ^ (2 * m))⁻¹ := by group
        _ = (a ^ k * a ^ (2 * m)) * b * (a ^ (2 * m))⁻¹ := by rw [hcomm]
        _ = a ^ k * (a ^ (2 * m) * b * (a ^ (2 * m))⁻¹) := by group
        _ = a ^ k * (z * b) := by rw [hWb]
        _ = a ^ k * (b * z) := by rw [hbz]
        _ = a ^ k * b * z := by group

end QG

end CFSG.GH74.GLS.Stage1.Thm3.Sec7.Q
