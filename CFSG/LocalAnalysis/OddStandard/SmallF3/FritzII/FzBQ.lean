module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBQ1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB0A

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}
  {q s : G}

theorem fzb_comm_q_mem (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 4)
    (hq : zpowers q = twoCore t) {a : G} (ha : a ∈ invCent t) :
    a * q * a⁻¹ * q⁻¹ ∈ zpowers t := by
  have hqK : q ∈ twoCore t := by rw [← hq]; exact Subgroup.mem_zpowers q
  obtain ⟨hq4, hq2⟩ := fzbs_q_facts h hK hq
  have hm : a * q * a⁻¹ ∈ zpowers q := by
    rw [hq]; exact fzb_H_norm_K h ha hqK
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hm
  have hq4z : (orderOf q : ℤ) = 4 := by rw [hq4]; norm_num
  have hmod : q ^ (i % 4) = a * q * a⁻¹ := by
    have h := zpow_mod_orderOf q i
    rw [hq4z] at h
    exact h.trans hi
  have hzpow2 : q ^ (2 : ℤ) = t := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, hq2]
  have hge : 0 ≤ i % 4 := Int.emod_nonneg i (by norm_num)
  have hlt : i % 4 < 4 := Int.emod_lt_of_pos i (by norm_num)
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h0 | h1 | h2 | h3
  · exfalso
    have hq1 : q = 1 := by
      have h : (1 : G) = a * q * a⁻¹ := by rw [← hmod, h0, zpow_zero]
      calc q = a⁻¹ * (a * q * a⁻¹) * a := by group
        _ = a⁻¹ * 1 * a := by rw [← h]
        _ = 1 := by group
    rw [hq1, orderOf_one] at hq4
    norm_num at hq4
  · rw [← hmod, h1, zpow_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  · exfalso
    have hqt : q = t := by
      have h : t = a * q * a⁻¹ := by rw [← hmod, h2, hzpow2]
      have hat : a * t = t * a := S4A.mem_invCent_iff.mp ha
      calc q = a⁻¹ * (a * q * a⁻¹) * a := by group
        _ = a⁻¹ * t * a := by rw [← h]
        _ = t := by
            calc a⁻¹ * t * a = a⁻¹ * (t * a) := by group
              _ = a⁻¹ * (a * t) := by rw [← hat]
              _ = t := by group
    have ht_ne_one : t ≠ 1 := by
      intro h1
      have hord := h.hyp.ord_t
      rw [h1, orderOf_one] at hord
      norm_num at hord
    rw [hqt] at hq2
    have ht2 : t ^ 2 = 1 := by rw [← h.hyp.ord_t]; exact pow_orderOf_eq_one t
    exact ht_ne_one (by rw [← hq2, ht2])
  · rw [← hmod, h3]
    have h3t : q ^ (3 : ℤ) * q⁻¹ = t := by
      rw [show q⁻¹ = q ^ (-1 : ℤ) from (zpow_neg_one q).symm, ← zpow_add,
        show (3 : ℤ) + (-1) = 2 by norm_num, hzpow2]
    rw [h3t]
    exact Subgroup.mem_zpowers t

theorem fzb_comm_tau_mem (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 4)
    (hq : zpowers q = twoCore t) (hτq : tau * q * tau⁻¹ = q⁻¹) {a : G} (ha : a ∈ invCent t) :
    a * tau * a⁻¹ * tau⁻¹ ∈ zpowers t ⊔ L := by
  have hq2 : q ^ 2 = t := (fzbs_q_facts h hK hq).2
  have hA : ∀ b ∈ twoCore t ⊔ L, b * tau * b⁻¹ * tau⁻¹ ∈ zpowers t ⊔ L := by
    intro b hb
    obtain ⟨k, hk, ℓ, hℓ, rfl⟩ := fzb_KL_decomp h hb
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (by rw [hq]; exact hk)
    have hℓ'mem : tau * ℓ⁻¹ * tau⁻¹ ∈ L :=
      fzb_H_norm_L h (h.le_invCent h.tau_mem) (L.inv_mem hℓ)
    have hτk : tau * k * tau⁻¹ = k⁻¹ := by
      rw [← hi, ← conj_zpow (a := tau) (b := q) (i := i), hτq, inv_zpow]
    have hτk_inv : tau * k⁻¹ * tau⁻¹ = k := by
      have h : tau * k⁻¹ * tau⁻¹ = (tau * k * tau⁻¹)⁻¹ := by group
      rw [h, hτk, inv_inv]
    have hk2 : k ^ 2 ∈ zpowers t := by
      rw [← hi]
      refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
      calc t ^ i = (q ^ 2) ^ i := congrArg (fun x => x ^ i) hq2.symm
        _ = (q ^ ((2 : ℕ) : ℤ)) ^ i :=
              congrArg (fun x => x ^ i) (zpow_natCast q 2).symm
        _ = q ^ (((2 : ℕ) : ℤ) * i) := (zpow_mul q ((2 : ℕ) : ℤ) i).symm
        _ = q ^ (i * ((2 : ℕ) : ℤ)) := by congr 1; ring
        _ = (q ^ i) ^ ((2 : ℕ) : ℤ) := zpow_mul q i ((2 : ℕ) : ℤ)
        _ = (q ^ i) ^ 2 := zpow_natCast (q ^ i) 2
    have hcomm : k * (ℓ * (tau * ℓ⁻¹ * tau⁻¹)) = (ℓ * (tau * ℓ⁻¹ * tau⁻¹)) * k :=
      fzb_K_comm_L h hk (L.mul_mem hℓ hℓ'mem)
    have hgoal : (k * ℓ) * tau * (k * ℓ)⁻¹ * tau⁻¹
        = k ^ 2 * (ℓ * (tau * ℓ⁻¹ * tau⁻¹)) := by
      have hkey : (k * ℓ) * tau * (k * ℓ)⁻¹ * tau⁻¹
          = k * (ℓ * (tau * ℓ⁻¹ * tau⁻¹)) * (tau * k⁻¹ * tau⁻¹) := by group
      rw [hkey, hτk_inv, mul_assoc k (ℓ * (tau * ℓ⁻¹ * tau⁻¹)) k, hcomm.symm, pow_two]
      exact (mul_assoc k k (ℓ * (tau * ℓ⁻¹ * tau⁻¹))).symm
    rw [hgoal]
    exact Subgroup.mul_mem_sup hk2 (L.mul_mem hℓ hℓ'mem)
  rcases fzb_H_cases h ha with ha' | ha''
  · exact hA a ha'
  · have h : a * tau * a⁻¹ * tau⁻¹
        = (a * tau⁻¹) * tau * (a * tau⁻¹)⁻¹ * tau⁻¹ := by group
    rw [h]
    exact hA (a * tau⁻¹) ha''

theorem fzb_comm_qs_mem (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 4)
    (hq : zpowers q = twoCore t) (hs : s = tau ∨ s = q * tau) (hsq : s * q * s⁻¹ = q⁻¹) {a : G}
    (ha : a ∈ invCent t) {ℓ : G} (hℓ : ℓ ∈ L) :
    a * (q * s * ℓ) * a⁻¹ * (q * s * ℓ)⁻¹ ∈ zpowers t ⊔ L := by
  have hqK : q ∈ twoCore t := by rw [← hq]; exact Subgroup.mem_zpowers q
  have hPle : twoCore t ≤ invCent t := by
    have := Subgroup.map_subtype_le (CFSG.pCore 2 ↥(invCent t))
    simpa only [twoCore, CFSG.Open.pCoreOf] using this
  have hqH : q ∈ invCent t := hPle hqK
  have hτq : tau * q * tau⁻¹ = q⁻¹ := by
    rcases hs with rfl | rfl
    · exact hsq
    · have h1 : q * (tau * q * tau⁻¹) * q⁻¹ = q⁻¹ := by
        calc q * (tau * q * tau⁻¹) * q⁻¹
            = (q * tau) * q * (q * tau)⁻¹ := by group
          _ = q⁻¹ := hsq
      have h2 : q * (tau * q * tau⁻¹) = 1 := by
        have := congrArg (· * q) h1
        simpa [mul_assoc] using this
      exact (inv_eq_of_mul_eq_one_right h2).symm
  have hsH : s ∈ invCent t := by
    rcases hs with rfl | rfl
    · exact h.le_invCent h.tau_mem
    · exact (invCent t).mul_mem hqH (h.le_invCent h.tau_mem)
  have hcq : a * q * a⁻¹ * q⁻¹ ∈ zpowers t ⊔ L :=
    Subgroup.mem_sup_left (fzb_comm_q_mem h hK hq ha)
  have hcτ : a * tau * a⁻¹ * tau⁻¹ ∈ zpowers t ⊔ L :=
    fzb_comm_tau_mem h hK hq hτq ha
  have hcℓ : a * ℓ * a⁻¹ * ℓ⁻¹ ∈ zpowers t ⊔ L :=
    Subgroup.mem_sup_right (L.mul_mem (fzb_H_norm_L h ha hℓ) (L.inv_mem hℓ))
  have hcs : a * s * a⁻¹ * s⁻¹ ∈ zpowers t ⊔ L := by
    rcases hs with rfl | rfl
    · exact hcτ
    · have hid : a * (q * tau) * a⁻¹ * (q * tau)⁻¹
          = (a * q * a⁻¹ * q⁻¹) * (q * (a * tau * a⁻¹ * tau⁻¹) * q⁻¹) := by group
      rw [hid]
      exact (zpowers t ⊔ L).mul_mem hcq (fzb_H_norm_N h hqH hcτ)
  have hcsℓ : a * (s * ℓ) * a⁻¹ * (s * ℓ)⁻¹ ∈ zpowers t ⊔ L := by
    have hid : a * (s * ℓ) * a⁻¹ * (s * ℓ)⁻¹
        = (a * s * a⁻¹ * s⁻¹) * (s * (a * ℓ * a⁻¹ * ℓ⁻¹) * s⁻¹) := by group
    rw [hid]
    exact (zpowers t ⊔ L).mul_mem hcs (fzb_H_norm_N h hsH hcℓ)
  have hid : a * (q * s * ℓ) * a⁻¹ * (q * s * ℓ)⁻¹
      = (a * q * a⁻¹ * q⁻¹) * (q * (a * (s * ℓ) * a⁻¹ * (s * ℓ)⁻¹) * q⁻¹) := by
    group
  rw [hid]
  exact (zpowers t ⊔ L).mul_mem hcq (fzb_H_norm_N h hqH hcsℓ)

end CFSG.OddStandard.SmallF3.FritzII
