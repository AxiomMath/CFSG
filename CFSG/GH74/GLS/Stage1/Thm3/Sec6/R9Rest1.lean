module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.IVK.Defs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Basic
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Basic

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1

open Subgroup CFSG.GH74.GLS.Stage1.Thm3.Sec4.M CFSG.GH74.GLS CFSG.GH74
open QuaternionGroup

theorem quat_model_outside (N : ℕ) [NeZero N] (hN : 2 ≤ N) (V : Subgroup (QuaternionGroup N))
    (hc : IsCyclic ↥V) (hi : V.index = 2) (b : QuaternionGroup N) (hb : b ∉ V) :
    b * b = a (N : ZMod (2 * N)) ∧ ∀ v ∈ V, b * v * b⁻¹ = v⁻¹ := by
  have hcardG : Nat.card (QuaternionGroup N) = 4 * N := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hcardV : Nat.card V = 2 * N := by
    have h1 := Subgroup.card_mul_index V
    rw [hi, hcardG] at h1
    omega
  obtain ⟨γ, hγ⟩ := hc.exists_generator
  have hord : orderOf (γ : QuaternionGroup N) = 2 * N := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hγ, hcardV]
  have h2N : ((2 * N : ℕ) : ZMod (2 * N)) = 0 := ZMod.natCast_self _
  push_cast at h2N
  obtain ⟨γ', hγ'V⟩ := γ
  cases γ' with
  | a i =>
    have hform : ∀ k : ℤ, ∃ j, (a i : QuaternionGroup N) ^ k = a j := by
      intro k
      induction k using Int.induction_on with
      | zero => exact ⟨0, by rw [zpow_zero, one_def]⟩
      | succ k ih =>
        obtain ⟨j, hj⟩ := ih
        exact ⟨j + i, by rw [zpow_add_one, hj, a_mul_a]⟩
      | pred k ih =>
        obtain ⟨j, hj⟩ := ih
        exact ⟨j - i, by rw [zpow_sub_one, hj, show (a i : QuaternionGroup N)⁻¹ = a (-i) from rfl, a_mul_a]; congr 1; ring⟩
    have hrot : ∀ v ∈ V, ∃ j, v = a j := by
      intro v hv
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hγ ⟨v, hv⟩)
      obtain ⟨j, hj⟩ := hform k
      refine ⟨j, ?_⟩
      have := congrArg Subtype.val hk
      simp only [Subgroup.coe_zpow] at this
      rw [← this, hj]
    have hRot : ∀ j : ZMod (2 * N), (a j : QuaternionGroup N) ∈ Subgroup.zpowers (a 1) := by
      intro j
      refine ⟨(j.val : ℤ), ?_⟩
      simp only [zpow_natCast]
      rw [a_one_pow, ZMod.natCast_zmod_val]
    have hVR : V ≤ Subgroup.zpowers (a 1 : QuaternionGroup N) := by
      intro v hv
      obtain ⟨j, rfl⟩ := hrot v hv
      exact hRot j
    have hEq : V = Subgroup.zpowers (a 1 : QuaternionGroup N) :=
      Subgroup.eq_of_le_of_card_ge hVR (by rw [Nat.card_zpowers, orderOf_a_one, hcardV])
    cases b with
    | a j =>
      exfalso
      apply hb
      rw [hEq]
      exact hRot j
    | xa j =>
      refine ⟨by rw [xa_mul_xa]; congr 1; ring, ?_⟩
      intro v hv
      obtain ⟨j', rfl⟩ := hrot v hv
      rw [show (xa j : QuaternionGroup N)⁻¹ = xa ((N : ZMod (2 * N)) + j) from rfl,
        xa_mul_a, xa_mul_xa, show (a j' : QuaternionGroup N)⁻¹ = a (-j') from rfl]
      congr 1
      linear_combination h2N
  | xa i =>
    have hN2 : N = 2 := by
      have h4 : orderOf (xa i : QuaternionGroup N) = 4 := orderOf_xa i
      have : orderOf (xa i : QuaternionGroup N) = 2 * N := hord
      omega
    subst hN2
    have hmem : ∀ v : QuaternionGroup 2, v ∈ V ↔
        v = 1 ∨ v = xa i ∨ v = a ((2 : ℕ) : ZMod (2 * 2)) ∨ v = xa (i + ((2 : ℕ) : ZMod (2 * 2))) := by
      intro v
      constructor
      · intro hv
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hγ ⟨v, hv⟩)
        have hk' : (xa i : QuaternionGroup 2) ^ k = v := by
          have := congrArg Subtype.val hk
          simpa only [Subgroup.coe_zpow] using this
        have hord4 : orderOf (xa i : QuaternionGroup 2) = 4 := orderOf_xa i
        have hmod := zpow_mod_orderOf (xa i : QuaternionGroup 2) k
        rw [hord4] at hmod
        rw [← hk', ← hmod]
        have hr0 : 0 ≤ k % ((4 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
        have hr1 : k % ((4 : ℕ) : ℤ) < 4 := Int.emod_lt_of_pos _ (by norm_num)
        generalize k % ((4 : ℕ) : ℤ) = r at hr0 hr1 ⊢
        have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
        have hsq : (xa i : QuaternionGroup 2) * xa i = a ((2 : ℕ) : ZMod (2 * 2)) := by
          rw [xa_mul_xa]; congr 1; ring
        rcases hr with rfl | rfl | rfl | rfl
        · left; simp
        · right; left; simp
        · right; right; left; rw [zpow_two, hsq]
        · right; right; right
          rw [show (3 : ℤ) = 2 + 1 from rfl, zpow_add_one, zpow_two, hsq, a_mul_xa]
          congr 1; linear_combination (-1 : ZMod (2 * 2)) * h2N
      · intro h
        have hxa : (xa i : QuaternionGroup 2) ∈ V := hγ'V
        have hsq : (xa i : QuaternionGroup 2) * xa i = a ((2 : ℕ) : ZMod (2 * 2)) := by
          rw [xa_mul_xa]; congr 1; ring
        rcases h with rfl | rfl | rfl | rfl
        · exact V.one_mem
        · exact hxa
        · rw [← hsq]; exact V.mul_mem hxa hxa
        · have : (xa (i + ((2 : ℕ) : ZMod (2 * 2))) : QuaternionGroup 2) =
              xa i * a ((2 : ℕ) : ZMod (2 * 2)) := by rw [xa_mul_a]
          rw [this, ← hsq]
          exact V.mul_mem hxa (V.mul_mem hxa hxa)
    have key : ∀ i : ZMod (2 * 2), ∀ b : QuaternionGroup 2,
        ¬ (b = 1 ∨ b = xa i ∨ b = a ((2 : ℕ) : ZMod (2 * 2)) ∨ b = xa (i + ((2 : ℕ) : ZMod (2 * 2)))) →
        b * b = a ((2 : ℕ) : ZMod (2 * 2)) ∧ ∀ v : QuaternionGroup 2,
          (v = 1 ∨ v = xa i ∨ v = a ((2 : ℕ) : ZMod (2 * 2)) ∨ v = xa (i + ((2 : ℕ) : ZMod (2 * 2)))) →
          b * v * b⁻¹ = v⁻¹ := by decide
    have hb' := (hmem b).not.1 hb
    obtain ⟨h1, h2⟩ := key i b hb'
    exact ⟨h1, fun v hv => h2 v ((hmem v).1 hv)⟩


theorem quat_outside_cyclic {G : Type} [Group G] {Y V : Subgroup G} {z : G} {n : ℕ}
    (hY : IVK.IsQuaternionTwoGroup ↥Y n) (hz : z ∈ Y) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hVY : V ≤ Y) (hVc : IsCyclic ↥V) (hVi : V.relIndex Y = 2) :
    ∀ b ∈ Y, b ∉ V → b * b = z ∧ ∀ v ∈ V, b * v * b⁻¹ = v⁻¹ := by
  obtain ⟨hn3, ⟨ι⟩⟩ := hY
  have hNne : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  have hN2 : 2 ≤ 2 ^ (n - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  set V0 : Subgroup ↥Y := V.subgroupOf Y with hV0
  set V' : Subgroup (QuaternionGroup (2 ^ (n - 2))) := V0.map ι.toMonoidHom with hV'
  have hV'idx : V'.index = 2 := by
    have h5 : V'.index = V0.index := Subgroup.index_map_equiv V0 ι
    rw [h5]
    exact hVi
  have hV'cyc : IsCyclic ↥V' := by
    have e1 : ↥V' ≃* ↥V :=
      (Subgroup.equivMapOfInjective V0 ι.toMonoidHom ι.injective).symm.trans
        (Subgroup.subgroupOfEquivOfLe hVY)
    exact e1.isCyclic.2 hVc
  intro b hb hbV
  have hz' : ι ⟨z, hz⟩ = a ((2 ^ (n - 2) : ℕ) : ZMod (2 * 2 ^ (n - 2))) := by
    have hsq : ι ⟨z, hz⟩ * ι ⟨z, hz⟩ = 1 := by
      rw [← map_mul]
      have : (⟨z, hz⟩ * ⟨z, hz⟩ : ↥Y) = 1 := Subtype.ext (by simpa using hz2)
      rw [this, map_one]
    rcases B.quat_invol _ hsq with h1 | h1
    · exfalso
      apply hz1
      have : (⟨z, hz⟩ : ↥Y) = 1 := ι.injective (by rw [h1, map_one])
      simpa using congrArg Subtype.val this
    · exact h1
  have hb' : ι ⟨b, hb⟩ ∉ V' := by
    intro hmem
    apply hbV
    have := (Subgroup.mem_map_equiv (f := ι) (K := V0) (x := ι ⟨b, hb⟩)).1 hmem
    simpa [hV0, Subgroup.mem_subgroupOf] using this
  obtain ⟨h1, h2⟩ := quat_model_outside (2 ^ (n - 2)) hN2 V' hV'cyc hV'idx (ι ⟨b, hb⟩) hb'
  refine ⟨?_, ?_⟩
  · have : ι (⟨b, hb⟩ * ⟨b, hb⟩) = ι ⟨z, hz⟩ := by rw [map_mul, h1, hz']
    have h3 := ι.injective this
    simpa using congrArg Subtype.val h3
  · intro v hv
    have hvV' : ι ⟨v, hVY hv⟩ ∈ V' := by
      refine (Subgroup.mem_map_equiv (f := ι) (K := V0) (x := ι ⟨v, hVY hv⟩)).2 ?_
      simpa [hV0, Subgroup.mem_subgroupOf] using hv
    have h3 := h2 _ hvV'
    have : ι (⟨b, hb⟩ * ⟨v, hVY hv⟩ * ⟨b, hb⟩⁻¹) = ι ⟨v, hVY hv⟩⁻¹ := by
      rw [map_mul, map_mul, map_inv, map_inv]; exact h3
    have h4 := ι.injective this
    simpa using congrArg Subtype.val h4

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1
