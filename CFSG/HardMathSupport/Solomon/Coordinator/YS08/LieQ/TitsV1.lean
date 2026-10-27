module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.TitsV2

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.ChevTwo.Semi CFSG.LieType.Ree.LargeReeInvolution

set_option linter.unusedSectionVars false

theorem commute_of_odd_order_inner {G : Type*} [Group G] {S : Subgroup G} {q r : G} (hq : q ∈ S)
    (hq2 : ∃ k : ℕ, orderOf q = 2 ^ k) (hr : Nat.Coprime (orderOf r) 2)
    (h : ∀ w ∈ S, r * w * r⁻¹ = q⁻¹ * w * q) : ∀ w ∈ S, r * w = w * r := by
  intro w hw
  have hpow : ∀ n : ℕ, ∀ w' ∈ S, r ^ n * w' * (r ^ n)⁻¹ = (q ^ n)⁻¹ * w' * q ^ n := by
    intro n
    induction n with
    | zero => intro w' _; simp
    | succ n ih =>
      intro w' hw'
      have hmem : (q ^ n)⁻¹ * w' * q ^ n ∈ S :=
        mul_mem (mul_mem (inv_mem (pow_mem hq n)) hw') (pow_mem hq n)
      calc r ^ (n + 1) * w' * (r ^ (n + 1))⁻¹
          = r * (r ^ n * w' * (r ^ n)⁻¹) * r⁻¹ := by group
        _ = r * ((q ^ n)⁻¹ * w' * q ^ n) * r⁻¹ := by rw [ih w' hw']
        _ = q⁻¹ * ((q ^ n)⁻¹ * w' * q ^ n) * q := h _ hmem
        _ = (q ^ (n + 1))⁻¹ * w' * q ^ (n + 1) := by group
  have hm : (q ^ orderOf r)⁻¹ * w * q ^ orderOf r = w := by
    have := hpow (orderOf r) w hw
    rw [pow_orderOf_eq_one, inv_one, mul_one, one_mul] at this
    exact this.symm
  have hqm : Commute (q ^ orderOf r) w := by
    have h1 : q ^ orderOf r * w = w * q ^ orderOf r := by
      calc q ^ orderOf r * w = q ^ orderOf r * ((q ^ orderOf r)⁻¹ * w * q ^ orderOf r) := by rw [hm]
        _ = w * q ^ orderOf r := by group
    exact h1
  obtain ⟨k, hk⟩ := hq2
  have hcop : Nat.Coprime (orderOf r) (orderOf q) := by
    rw [hk]
    exact Nat.Coprime.pow_right k hr
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
  have hqw : q * w = w * q := by
    have := (hqm.pow_left j).eq
    rwa [hj] at this
  have := h w hw
  calc r * w = (r * w * r⁻¹) * r := by group
    _ = (q⁻¹ * w * q) * r := by rw [this]
    _ = w * r := by
      have e : q⁻¹ * w * q = w := by
        calc q⁻¹ * w * q = q⁻¹ * (w * q) := by group
          _ = q⁻¹ * (q * w) := by rw [hqw]
          _ = w := by group
      rw [e]

section TitsV1


variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem reeLIOddAt_zero_of_witness (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hW : ∀ r ∈ rankOneGroupOne K a, Nat.Coprime (orderOf r) 2 → r ≠ 1 →
      ∃ w ∈ ReeTag.F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩, r * w ≠ w * r) :
    ReeLIOddAt K a ⟨0, by decide⟩ := by
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  intro x hxo hx
  have hQ1 : sylowL a K 1 ∈ tKernel K a := sylowL_mem_tKernel hK 1
  have hV : sylowL a K 1 ∈ ReeTag.F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ :=
    (Subgroup.mem_inf.1 hQ1).1
  have hΓt : sylowL a K 1 ∈ ReeTag.F4.reeGamma K a := tKernel_le_reeGamma hQ1
  have hQJt : (⟨sylowL a K 1, hΓt⟩ : ↥(ReeTag.F4.reeGamma K a)) ∈
      reeQJ ReeTag.F4 K a (some ⟨0, by decide⟩) := by
    rw [reeQJ_some]
    exact Subgroup.mem_subgroupOf.2 hV
  have hxt : (x : ModGL ReeTag.F4.tag K) * sylowL a K 1 = sylowL a K 1 * x := by
    have h1 := congrArg (fun y : ↥(ReeTag.F4.reeGamma K a) => (y : ModGL ReeTag.F4.tag K))
      (hx _ hQJt)
    simp only [Subgroup.coe_mul] at h1
    exact h1
  obtain ⟨q, hq, r, hr, hqr, hrodd⟩ := tOne_decomp hK hxo hxt
  have hqV : q ∈ ReeTag.F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ :=
    (Subgroup.mem_inf.1 hq).1
  have hqΓ : q ∈ ReeTag.F4.reeGamma K a := tKernel_le_reeGamma hq
  have hqQJ : (⟨q, hqΓ⟩ : ↥(ReeTag.F4.reeGamma K a)) ∈
      reeQJ ReeTag.F4 K a (some ⟨0, by decide⟩) := by
    rw [reeQJ_some]
    exact Subgroup.mem_subgroupOf.2 hqV
  have hq2 : ∃ k : ℕ, orderOf q = 2 ^ k := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 (ree_QJ_pgroup (t := ReeTag.F4)
      (K := K) (a := a) (some ⟨0, by decide⟩))) ⟨⟨q, hqΓ⟩, hqQJ⟩
    refine ⟨k, ?_⟩
    have h1 : orderOf (⟨q, hqΓ⟩ : ↥(ReeTag.F4.reeGamma K a)) = 2 ^ k :=
      (Subgroup.orderOf_coe (⟨⟨q, hqΓ⟩, hqQJ⟩ :
        reeQJ ReeTag.F4 K a (some ⟨0, by decide⟩))).trans hk
    exact (Subgroup.orderOf_coe (⟨q, hqΓ⟩ : ↥(ReeTag.F4.reeGamma K a))).trans h1
  have hact : ∀ w ∈ ReeTag.F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩,
      r * w * r⁻¹ = q⁻¹ * w * q := by
    intro w hw
    have hwΓ : w ∈ ReeTag.F4.reeGamma K a := (Subgroup.mem_inf.1 hw).2
    have hwQJ : (⟨w, hwΓ⟩ : ↥(ReeTag.F4.reeGamma K a)) ∈
        reeQJ ReeTag.F4 K a (some ⟨0, by decide⟩) := by
      rw [reeQJ_some]
      exact Subgroup.mem_subgroupOf.2 hw
    have h1 := congrArg (fun y : ↥(ReeTag.F4.reeGamma K a) => (y : ModGL ReeTag.F4.tag K))
      (hx _ hwQJ)
    simp only [Subgroup.coe_mul] at h1
    rw [← hqr] at h1
    calc r * w * r⁻¹ = q⁻¹ * (q * r * w) * r⁻¹ := by group
      _ = q⁻¹ * (w * (q * r)) * r⁻¹ := by rw [h1]
      _ = q⁻¹ * w * q := by group
  have hrc := commute_of_odd_order_inner (S := ReeTag.F4.reeFixedOrbitComplementUnipotent K a
    ⟨0, by decide⟩) hqV hq2 hrodd hact
  have hr1 : r = 1 := by
    by_contra hne
    obtain ⟨w, hw, hwne⟩ := hW r hr hrodd hne
    exact hwne (hrc w hw)
  rw [hr1, mul_one] at hqr
  have hxQJ : x ∈ reeQJ ReeTag.F4 K a (some ⟨0, by decide⟩) := by
    have : x = ⟨q, hqΓ⟩ := Subtype.ext hqr.symm
    rw [this]
    exact hqQJ
  exact eq_one_of_mem_pGroup_of_coprime (q := 2) (ree_QJ_pgroup (t := ReeTag.F4) _) hxQJ hxo

end TitsV1

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
