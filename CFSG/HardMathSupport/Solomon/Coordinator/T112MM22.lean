module

public import CFSG.HardMathSupport.Solomon.Coordinator.T112MCover
public import CFSG.Sporadic.Bridge.M22

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open Equiv

theorem t112m_natCard_m22 : Nat.card TauCeti.SporadicName.M22.Group = 443520 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  have h1 := CFSG.Sporadic.Bridge.M22.tauCeti_finite_card_le.2
  have h2 := CFSG.Sporadic.Bridge.M22.le_card_native
  rw [Nat.card_congr e.toEquiv] at h2
  omega

theorem t112m_sylow_hatM22 {K : Type*} [Group K] [Finite K] (h : IsHatMTwentyTwo K)
    (R : Sylow 3 K) :
    Nat.card ↥(R : Subgroup K) = 27 ∧
      (∃ r ∈ (R : Subgroup K), ∃ s ∈ (R : Subgroup K), r * s ≠ s * r) ∧
      ∀ r ∈ (R : Subgroup K), r ^ 3 = 1 := by
  obtain ⟨hc, hZ, ⟨e⟩⟩ := h
  refine t112m_sylow_cover hc hZ e (m := 49280) ?_ (by norm_num) R
  exact t112m_natCard_m22.trans (by norm_num)

@[irreducible] def t112mA : Perm (Fin 22) :=
  List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] * List.formPerm [3, 11] *
    List.formPerm [5, 21] * List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [10, 13]

@[irreducible] def t112mB : Perm (Fin 22) :=
  List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] *
    List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18]

@[irreducible] def t112mX : Perm (Fin 22) :=
  List.formPerm [1, 11, 15] * List.formPerm [2, 7, 3] * List.formPerm [4, 14, 20] *
    List.formPerm [5, 8, 16] * List.formPerm [6, 21, 9] * List.formPerm [17, 18, 19]

theorem t112mA_mem : t112mA ∈ CFSG.Blueprint.NativeSporadic.M22 := by
  unfold t112mA
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem t112mB_mem : t112mB ∈ CFSG.Blueprint.NativeSporadic.M22 := by
  unfold t112mB
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem t112mX_eq : t112mX =
    [t112mB, t112mA, t112mB⁻¹, t112mA, t112mB, t112mB, t112mA, t112mB, t112mA, t112mB, t112mB,
      t112mA, t112mB, t112mA, t112mB, t112mB, t112mA, t112mB⁻¹, t112mA, t112mB].prod := by
  unfold t112mX t112mA t112mB
  decide +kernel

theorem t112mX_pow_three : t112mX ^ 3 = 1 := by
  unfold t112mX
  decide +kernel

theorem t112mX_comm : t112mX * t112mA = t112mA * t112mX := by
  unfold t112mX t112mA
  decide +kernel

theorem t112mA_sq : t112mA ^ 2 = 1 := by
  unfold t112mA
  decide +kernel

theorem t112mA_ne_one : t112mA ≠ 1 := by
  unfold t112mA
  decide +kernel

theorem t112mX_ne_one : t112mX ≠ 1 := by
  unfold t112mX
  decide +kernel

theorem t112mX_mem : t112mX ∈ CFSG.Blueprint.NativeSporadic.M22 := by
  have ha := t112mA_mem
  have hb := t112mB_mem
  have hb' := CFSG.Blueprint.NativeSporadic.M22.inv_mem hb
  rw [t112mX_eq]
  refine Subgroup.list_prod_mem _ fun y hy => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [hb, ha, hb', ha, hb, hb, ha, hb, ha, hb, hb, ha, hb, ha, hb, hb, ha, hb', ha, hb]

theorem t112m_m22_data :
    ∃ (V : Subgroup ↥CFSG.Blueprint.NativeSporadic.M22) (x : ↥CFSG.Blueprint.NativeSporadic.M22),
      V ≠ ⊥ ∧ (∀ v ∈ V, v ^ 2 = 1) ∧ x ≠ 1 ∧ x ^ 3 = 1 ∧
        x ∈ Subgroup.normalizer (V : Set ↥CFSG.Blueprint.NativeSporadic.M22) := by
  let a' : ↥CFSG.Blueprint.NativeSporadic.M22 := ⟨t112mA, t112mA_mem⟩
  let x' : ↥CFSG.Blueprint.NativeSporadic.M22 := ⟨t112mX, t112mX_mem⟩
  have hxa' : x' * a' = a' * x' := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact t112mX_comm
  have ha2' : a' ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact t112mA_sq
  have hx3' : x' ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact t112mX_pow_three
  refine ⟨Subgroup.zpowers a', x', ?_, ?_, ?_, hx3', ?_⟩
  · intro hV
    have h1 : a' ∈ Subgroup.zpowers a' := Subgroup.mem_zpowers a'
    rw [hV, Subgroup.mem_bot] at h1
    exact t112mA_ne_one (congrArg Subtype.val h1)
  · intro v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha2', one_zpow]
  · intro h
    exact t112mX_ne_one (congrArg Subtype.val h)
  · rw [Subgroup.mem_normalizer_iff]
    intro v
    have hc : ∀ k : ℤ, x' * a' ^ k * x'⁻¹ = a' ^ k := fun k => by
      rw [(Commute.zpow_right (hxa' : Commute x' a') k).eq, mul_inv_cancel_right]
    constructor
    · rintro hv
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
      rw [hc k]
      exact Subgroup.zpow_mem_zpowers a' k
    · intro hv
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hv
      have : v = a' ^ k := by
        have h1 : x' * v * x'⁻¹ = x' * a' ^ k * x'⁻¹ := by
          rw [hc k]
          exact hk.symm
        exact mul_left_cancel (mul_right_cancel h1)
      rw [this]
      exact Subgroup.zpow_mem_zpowers a' k

theorem t112m_twoLocal_hatM22 {K : Type} [Group K] [Finite K] (h : IsHatMTwentyTwo K) :
    2 ≤ GLATwoLocalRank 3 K := by
  have hexp := fun R => (t112m_sylow_hatM22 h R).2.2
  obtain ⟨-, hZ, ⟨e⟩⟩ := h
  obtain ⟨eb⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  obtain ⟨V, x, hV1, hV2, hx1, hx3, hxV⟩ := t112m_data_of_mulEquiv (e.trans eb.symm) t112m_m22_data
  exact t112m_cover_twoLocal hZ hexp hV1 hV2 hx1 hx3 hxV

end CFSG.HardMathSupport.Solomon.Coordinator
