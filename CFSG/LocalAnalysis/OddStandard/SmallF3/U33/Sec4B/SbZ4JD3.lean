module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD3A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

private theorem mul_self_mul_self_eq_one_of_pow_three {G : Type*} [Group G] {r : G}
    (h : r ^ 3 = 1) : r * (r * r) = 1 := by
  rw [show r * (r * r) = r ^ 3 by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, pow_two, pow_one]
    group]
  exact h

private theorem mul_self_eq_inv_of_pow_three {G : Type*} [Group G] {r : G} (h : r ^ 3 = 1) :
    r * r = r⁻¹ :=
  (inv_eq_of_mul_eq_one_right (mul_self_mul_self_eq_one_of_pow_three h)).symm


namespace ZJData

variable (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂) include h

variable {Mh : Subgroup H} (hMh : IsZJMh y z v₁ v₂ Mh) include hMh

variable {Mc : Subgroup H} (hMc : IsZJMc ρ Q Mh Mc) include hMc

theorem comm_rho_mem_Mc {m : H} (hm : m ∈ Mh) : m * (ρ * m⁻¹ * ρ⁻¹) ∈ Mc := by
  rw [hMc (m * (ρ * m⁻¹ * ρ⁻¹))]
  refine ⟨Mh.mul_mem hm (Mh_normal h hMh (g := ρ) (Mh.inv_mem hm)), ?_⟩
  rw [zjNorm_comm_rho h.rho_pow_three m]
  exact Q.one_mem

theorem mem_Mc_or_tau_mul {g : H} (hg : g ∈ Mh) : g ∈ Mc ∨ τ * g ∈ Mc := by
  have hττ : τ * τ = 1 := h.tau_sq
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right h.tau_sq
  let S : Subgroup H :=
    { carrier := {g : H | g ∈ Mc ∨ τ * g ∈ Mc}
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (Mc.mul_mem ha hb)
        · exact Or.inr (by
            have h1 : τ * a * τ⁻¹ ∈ Mc := Mc_conj_tau h hMh hMc ha
            have heq : τ * (a * b) = (τ * a * τ⁻¹) * (τ * b) := by group
            rw [heq]; exact Mc.mul_mem h1 hb)
        · exact Or.inr (by
            have heq : τ * (a * b) = (τ * a) * b := by group
            rw [heq]; exact Mc.mul_mem ha hb)
        · exact Or.inl (by
            have h1 : τ * (τ * a) * τ⁻¹ ∈ Mc := Mc_conj_tau h hMh hMc ha
            have heq : a * b = (τ * (τ * a) * τ⁻¹) * (τ * b) := by
              calc a * b = (τ * τ) * a * (τ * τ) * b := by rw [hττ]; group
                _ = (τ * (τ * a) * τ⁻¹) * (τ * b) := by rw [hτinv]; group
            rw [heq]; exact Mc.mul_mem h1 hb)
      one_mem' := Or.inl Mc.one_mem
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (Mc.inv_mem ha)
        · refine Or.inr ?_
          have h1 : τ * (τ * a)⁻¹ * τ⁻¹ ∈ Mc := Mc_conj_tau h hMh hMc (Mc.inv_mem ha)
          have heq : τ * a⁻¹ = τ * (τ * a)⁻¹ * τ⁻¹ := by
            have haeq : τ * (τ * a) = a := by rw [← mul_assoc, hττ, one_mul]
            conv_lhs => rw [← haeq]
            rw [mul_inv_rev]
            group
          rw [heq]; exact h1 }
  have hMhS : Mh ≤ S := by
    have hcomm_le : ⁅Mh, zpowers ρ⁆ ≤ Mc := by
      rw [Subgroup.commutator_le]
      intro m hm r hr
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr
      have hmod : ρ ^ k = ρ ^ (k % 3) := zpow_eq_zpow_emod' k h.rho_pow_three
      rw [hmod]
      have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by
        have h1 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
        have h2 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
        omega
      rcases hk with hk | hk | hk
      · rw [hk, zpow_zero]
        simpa using Mc.one_mem
      · rw [hk, zpow_one]
        have heq : ⁅m, ρ⁆ = m * (ρ * m⁻¹ * ρ⁻¹) := by rw [commutatorElement_def]; group
        rw [heq]; exact comm_rho_mem_Mc h hMh hMc hm
      · rw [hk]
        have hρsq : (ρ : H) ^ (2 : ℤ) = ρ⁻¹ := by
          rw [zpow_ofNat, pow_two]
          exact mul_self_eq_inv_of_pow_three h.rho_pow_three
        rw [hρsq]
        have hm' : ρ⁻¹ * m * ρ ∈ Mh := by
          have hh := Mh_normal h hMh (g := ρ⁻¹) hm
          simpa using hh
        have hc := comm_rho_mem_Mc h hMh hMc hm'
        have heq : (ρ⁻¹ * m * ρ) * (ρ * (ρ⁻¹ * m * ρ)⁻¹ * ρ⁻¹) = ⁅m, ρ⁻¹⁆⁻¹ := by
          rw [commutatorElement_def]; group
        have hmem : ⁅m, ρ⁻¹⁆⁻¹ ∈ Mc := by rw [← heq]; exact hc
        simpa using Mc.inv_mem hmem
    have hzp : zpowers τ ≤ S := by
      rw [Subgroup.zpowers_le]
      exact Or.inr (by rw [hττ]; exact Mc.one_mem)
    have hMcS : Mc ≤ S := fun x hx => Or.inl hx
    exact fun g hg => (sup_le (le_trans hcomm_le hMcS) hzp) (h.Mh_le_comm_sup hMh hg)
  exact hMhS hg

theorem card_Mc : Nat.card Mc = 256 := by
  let K : Subgroup Mh := Mc.subgroupOf Mh
  have hKcard : Nat.card K = Nat.card Mc :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Mc_le_Mh h hMh hMc)).toEquiv
  have hidx : K.index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and']
    refine ⟨⟨τ, tau_mem_Mh h hMh⟩, ?_, ?_⟩
    · intro hτ
      exact tau_not_mem_Mc h hMh hMc (Subgroup.mem_subgroupOf.mp hτ)
    · intro b
      rcases mem_Mc_or_tau_mul h hMh hMc b.2 with hb | hb
      · exact Or.inr (Subgroup.mem_subgroupOf.mpr hb)
      · exact Or.inl (Subgroup.mem_subgroupOf.mpr (by simpa using hb))
  have hmain : K.index * Nat.card K = Nat.card Mh := Subgroup.index_mul_card K
  rw [hidx, hKcard, card_Mh h hMh] at hmain
  omega

theorem Mc_isPGroup : IsPGroup 2 Mc :=
  (Mh_isPGroup h hMh).to_le (Mc_le_Mh h hMh hMc)

theorem mem_Q_of_mem_Mc_cent_Y {m : H} (hm : m ∈ Mc) (hY : m ∈ centralizer (Y : Set H)) :
    m ∈ Q := by
  haveI hQn : Q.Normal := ⟨fun x hx g => h.normal_Q g x hx⟩
  have hmE : m ∈ Q ⊔ zpowers τ := by rw [← h.E_eq]; exact hY
  obtain ⟨q, hq, zz, hzz, hxz⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := Q) (t := zpowers τ)).mp hmE
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hzz
  have htau2 : τ ^ (2 : ℕ) = 1 := by rw [pow_two]; exact h.tau_sq
  have hmod : τ ^ n = τ ^ (n % (2 : ℤ)) := zpow_eq_zpow_emod' n htau2
  rw [← hn, hmod] at hxz
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · rw [h0, zpow_zero, mul_one] at hxz
    rw [← hxz]; exact hq
  · exfalso
    rw [h1, zpow_one] at hxz
    have hτMc : τ ∈ Mc := by
      have heq : τ = q⁻¹ * m := by rw [← hxz]; group
      rw [heq]
      exact Mc.mul_mem (Q_le_Mc h hMh hMc (Q.inv_mem hq)) hm
    exact tau_not_mem_Mc h hMh hMc hτMc

theorem cent_rho_Mc {m : H} (hm : m ∈ Mc) (hc : ρ * m * ρ⁻¹ = m) : m = 1 := by
  have hmMh : m ∈ Mh := Mc_le_Mh h hMh hMc hm
  have hmc : m ∈ centralizer ({ρ} : Set H) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc m * ρ = (ρ * m * ρ⁻¹) * ρ := by conv_lhs => rw [← hc]
      _ = ρ * m := by group
  have hmem : m ∈ zpowers τ := by
    have hinf : m ∈ Mh ⊓ centralizer ({ρ} : Set H) := Subgroup.mem_inf.mpr ⟨hmMh, hmc⟩
    rwa [Mh_inf_cent_rho h hMh] at hinf
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have htau2 : τ ^ (2 : ℕ) = 1 := by rw [pow_two]; exact h.tau_sq
  have hmod : τ ^ n = τ ^ (n % (2 : ℤ)) := zpow_eq_zpow_emod' n htau2
  rw [hmod] at hn
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · rw [h0, zpow_zero] at hn; exact hn.symm
  · exfalso
    rw [h1, zpow_one] at hn
    exact tau_not_mem_Mc h hMh hMc (hn ▸ hm)

end ZJData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
