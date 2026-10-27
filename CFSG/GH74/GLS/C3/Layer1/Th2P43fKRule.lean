module

public import CFSG.GH74.GLS.C3.Layer1.Th2P43fPerm

public section

namespace CFSG.GH74.GLS.Th2.P43f

open Subgroup Equiv Equiv.Perm

variable {G : Type} [Group G]

theorem exists_zpow_conj_of_odd {y c : G} (hc : c * c = 1) (hyc : (y * c) * (y * c) = 1)
    (hodd : Odd (orderOf y)) : ∃ w ∈ Subgroup.zpowers y, w * c * w⁻¹ = y * c := by
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have hcyc : c * y * c = y⁻¹ := by
    have h1 : y * (c * y * c) = 1 := by
      calc y * (c * y * c) = (y * c) * (y * c) := by group
        _ = 1 := hyc
    exact (eq_inv_of_mul_eq_one_right h1)
  obtain ⟨k, hk⟩ := hodd
  have hy : y ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one y
  refine ⟨y ^ (k + 1), Subgroup.pow_mem _ (Subgroup.mem_zpowers y) _, ?_⟩
  have hconj : c * y ^ (k + 1) * c⁻¹ = (y ^ (k + 1))⁻¹ := by
    have h1 : c * y * c⁻¹ = y⁻¹ := by rw [hcinv]; exact hcyc
    calc c * y ^ (k + 1) * c⁻¹ = (c * y * c⁻¹) ^ (k + 1) := by
          rw [conj_pow]
      _ = (y ^ (k + 1))⁻¹ := by rw [h1, inv_pow]
  have hww : y ^ (k + 1) * y ^ (k + 1) = y := by
    calc y ^ (k + 1) * y ^ (k + 1) = y ^ (2 * k + 1) * y := by rw [← pow_add, ← pow_succ]; congr 1; ring
      _ = y := by rw [hy, one_mul]
  calc y ^ (k + 1) * c * (y ^ (k + 1))⁻¹
      = y ^ (k + 1) * (c * (y ^ (k + 1))⁻¹ * c⁻¹) * c := by group
    _ = y ^ (k + 1) * (c * y ^ (k + 1) * c⁻¹)⁻¹ * c := by rw [conj_inv]
    _ = y ^ (k + 1) * y ^ (k + 1) * c := by rw [hconj, inv_inv]
    _ = y * c := by rw [hww]

theorem k_rule {C K : Subgroup G} (hKC : K ≤ C) (hnorm : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (psi : G → Perm (Fin 7)) (hmul : ∀ g ∈ C, ∀ h ∈ C, psi (g * h) = psi g * psi h)
    (hker : ∀ k ∈ K, psi k = 1 → Odd (orderOf k))
    (hsurj : ∀ h : Perm (Fin 7), sign h = 1 → ∃ k ∈ K, psi k = h)
    {c c' : G} (hc : c ∈ C) (hc' : c' ∈ C) (hc2 : c * c = 1) (hc'2 : c' * c' = 1)
    (hcc : c' * c⁻¹ ∈ K) (hsupp : (psi c).support.card = (psi c').support.card) :
    ∃ k ∈ K, k * c * k⁻¹ = c' := by
  have hpsi1 : psi 1 = 1 := by
    have := hmul 1 C.one_mem 1 C.one_mem
    rw [mul_one] at this
    exact (mul_eq_left.1 this.symm)
  have hinv : ∀ g ∈ C, psi g⁻¹ = (psi g)⁻¹ := by
    intro g hg
    have := hmul g hg g⁻¹ (C.inv_mem hg)
    rw [mul_inv_cancel, hpsi1] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  have hcc2 : psi c * psi c = 1 := by rw [← hmul c hc c hc, hc2, hpsi1]
  have hc'c2 : psi c' * psi c' = 1 := by rw [← hmul c' hc' c' hc', hc'2, hpsi1]
  obtain ⟨g, hgs, hg⟩ := exists_even_conj_of_card_support_eq hcc2 hc'c2 hsupp
  obtain ⟨k₁, hk₁, hk₁g⟩ := hsurj g hgs
  have hk₁C : k₁ ∈ C := hKC hk₁
  set c'' : G := k₁ * c * k₁⁻¹ with hc''
  have hc''C : c'' ∈ C := C.mul_mem (C.mul_mem hk₁C hc) (C.inv_mem hk₁C)
  have hc''2 : c'' * c'' = 1 := by
    calc c'' * c'' = k₁ * (c * c) * k₁⁻¹ := by rw [hc'']; group
      _ = 1 := by rw [hc2]; group
  have hpsic'' : psi c'' = psi c' := by
    rw [hc'', hmul _ (C.mul_mem hk₁C hc) _ (C.inv_mem hk₁C), hmul _ hk₁C _ hc, hinv _ hk₁C, hk₁g, ← hg]
  set y : G := c' * c'' with hy
  have hyK : y ∈ K := by
    have hm : c * k₁⁻¹ * c⁻¹ ∈ K := hnorm c hc k₁⁻¹ (K.inv_mem hk₁)
    have e : y = (c' * c⁻¹) * (k₁ * (c * k₁⁻¹ * c⁻¹))⁻¹ := by
      have hc''inv : c'' = c''⁻¹ := (inv_eq_of_mul_eq_one_right hc''2).symm
      rw [hy, hc''inv, hc'']
      group
    rw [e]
    exact K.mul_mem hcc (K.inv_mem (K.mul_mem hk₁ hm))
  have hyC : y ∈ C := hKC hyK
  have hpsiy : psi y = 1 := by
    rw [hy, hmul _ hc' _ hc''C, hpsic'', hc'c2]
  have hodd := hker y hyK hpsiy
  have hyc : y * c'' = c' := by
    rw [hy, mul_assoc, hc''2, mul_one]
  obtain ⟨w, hw, hwc⟩ := exists_zpow_conj_of_odd hc''2 (by rw [hyc]; exact hc'2) hodd
  have hwK : w ∈ K := Subgroup.zpowers_le.2 hyK hw
  refine ⟨w * k₁, K.mul_mem hwK hk₁, ?_⟩
  calc w * k₁ * c * (w * k₁)⁻¹ = w * (k₁ * c * k₁⁻¹) * w⁻¹ := by group
    _ = w * c'' * w⁻¹ := rfl
    _ = y * c'' := hwc
    _ = c' := hyc

end CFSG.GH74.GLS.Th2.P43f
