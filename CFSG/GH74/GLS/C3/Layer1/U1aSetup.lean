module

public import Mathlib.GroupTheory.Solvable
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.GH74.GLS.C3.Layer1.U1a

open Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G]

structure Setup (M L N W Q T : Subgroup G) : Prop where
  M_ne_top : M ≠ ⊤
  M_not_solvable : ¬ Group.IsSolvable ↥M
  L_le : L ≤ M
  L_norm : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L
  N_le : N ≤ L
  N_odd : Odd (Nat.card ↥N)
  N_norm : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N
  N_max : ∀ N' : Subgroup G, N' ≤ L → (∀ l ∈ L, ∀ n ∈ N', l * n * l⁻¹ ∈ N') →
    Odd (Nat.card ↥N') → N' ≤ N
  W_le : W ≤ M
  W_norm : ∀ m ∈ M, ∀ w ∈ W, m * w * m⁻¹ ∈ W
  W_comm : ∀ w ∈ W, ∀ l ∈ L, w * l * w⁻¹ * l⁻¹ ∈ N
  W_full : ∀ m ∈ M, (∀ l ∈ L, m * l * m⁻¹ * l⁻¹ ∈ N) → m ∈ W
  LW : ∀ v ∈ L, v ∈ W → orderOf v ≠ 2
  sylowQ : IsSylowOf 2 Q W
  sylowT : IsSylowOf 2 T M
  Q_le_T : Q ≤ T
  rankQ : ∃ a ∈ Q, ∃ b ∈ Q, orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b ∧ a * b = b * a
  preuniq : ∀ y ∈ W, orderOf y = 2 → centralizer ({y} : Set G) ≤ M

variable {M L N W Q T : Subgroup G}

theorem isPGroup_zpowers_of_orderOf_eq_two {a : G} (ha : orderOf a = 2) : IsPGroup 2 (zpowers a) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])

theorem mul_self_eq_one_of_orderOf_eq_two {a : G} (ha : orderOf a = 2) : a * a = 1 := by
  rw [← sq]
  exact ha ▸ pow_orderOf_eq_one a

theorem inv_eq_self_of_orderOf_eq_two {a : G} (ha : orderOf a = 2) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_orderOf_eq_two ha)

theorem orderOf_conj_eq {a : G} (g : G) : orderOf (g⁻¹ * a * g) = orderOf a := by
  simpa [MulAut.conj_apply, mul_assoc] using
    orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective a

theorem orderOf_conj_eq' {a : G} (g : G) : orderOf (g * a * g⁻¹) = orderOf a := by
  simpa using orderOf_conj_eq (a := a) g⁻¹

theorem exists_mem_conj_le [Finite G] {P K X : Subgroup G} (hP : IsSylowOf 2 P K) (hXK : X ≤ K)
    (hX : IsPGroup 2 ↥X) : ∃ k ∈ K, ∀ y ∈ X, k⁻¹ * y * k ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, rfl⟩ := hP
  obtain ⟨Q', hQ'⟩ := (hX.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨c, rfl⟩ := MulAction.exists_smul_eq K Q Q'
  refine ⟨c, c.2, fun y hy => ?_⟩
  have hy' : (⟨y, hXK hy⟩ : K) ∈ ((c • Q : Sylow 2 K) : Subgroup K) := hQ' hy
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy'
  exact ⟨_, hy', by simp [MulAut.inv_apply]⟩

theorem exists_conj_involution_mem [Finite G] {P K : Subgroup G} (hP : IsSylowOf 2 P K) {y : G} (hyK : y ∈ K)
    (hy : orderOf y = 2) : ∃ k ∈ K, k⁻¹ * y * k ∈ P := by
  obtain ⟨k, hk, h⟩ := exists_mem_conj_le hP (X := zpowers y) ((zpowers_le).mpr hyK)
    (isPGroup_zpowers_of_orderOf_eq_two hy)
  exact ⟨k, hk, h y (mem_zpowers y)⟩

namespace Setup

variable (S : Setup M L N W Q T)
include S

theorem Q_le_W : Q ≤ W := S.sylowQ.le

theorem Q_isPGroup : IsPGroup 2 ↥Q := S.sylowQ.isPGroup

theorem T_isPGroup : IsPGroup 2 ↥T := S.sylowT.isPGroup

theorem T_le_M : T ≤ M := S.sylowT.le

theorem Q_le_M : Q ≤ M := S.Q_le_W.trans S.W_le

theorem Q_eq [Finite G] : Q = T ⊓ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (S.sylowQ.eq_of_le (le_inf S.Q_le_T S.Q_le_W) inf_le_right ?_).symm
  exact S.T_isPGroup.to_le inf_le_left

theorem Q_norm_T [Finite G] : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q := by
  intro t ht q hq
  rw [S.Q_eq] at hq ⊢
  exact ⟨T.mul_mem (T.mul_mem ht hq.1) (T.inv_mem ht),
    S.W_norm t (S.T_le_M ht) q hq.2⟩

theorem exists_conj_Q [Finite G] {w : G} (hw : w ∈ W) (hw2 : orderOf w = 2) : ∃ c ∈ W, c⁻¹ * w * c ∈ Q :=
  exists_conj_involution_mem S.sylowQ hw hw2

end Setup

end CFSG.GH74.GLS.C3.Layer1.U1a
