module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.CoreHyp
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.Factors

public section

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

open CFSG.EvenSporadicStandard.HNRecog.Fpf

variable {L L' : Type} [Group L] [Group L'] {N : Subgroup L} {N' : Subgroup L'}
  {θ : L →* A5 × A5} {θ' : L' →* A5 × A5} {ψ : A5 × A5 ≃* A5 × A5} {φ : L → L'} {z : L}

theorem CoreHyp.z_sq (h : CoreHyp N N' θ θ' ψ φ z) : z ^ 2 = 1 := by
  have hmem : z ^ 2 ∈ N := N.pow_mem h.z_mem 2
  have hcent : ∀ y ∈ N, z ^ 2 * y = y * z ^ 2 := by
    intro y _
    calc z ^ 2 * y = z * (z * y) := by rw [pow_two, mul_assoc]
      _ = z * (y * z) := by rw [(h.z_central y).symm]
      _ = (z * y) * z := by rw [mul_assoc]
      _ = (y * z) * z := by rw [(h.z_central y).symm]
      _ = y * (z * z) := by rw [mul_assoc]
      _ = y * z ^ 2 := by rw [pow_two]
  rcases h.centre (z ^ 2) hmem hcent with h1 | h1
  · exact h1
  · exfalso
    have hcancel : z * z = z * 1 := by rw [← pow_two, h1, mul_one]
    exact h.z_ne_one (mul_left_cancel hcancel)

theorem CoreHyp.phi_one (h : CoreHyp N N' θ θ' ψ φ z) : φ 1 = 1 := by
  have h1 := h.iso.map_mul 1 N.one_mem 1 N.one_mem
  rw [mul_one] at h1
  exact mul_eq_left.mp h1.symm

theorem CoreHyp.phi_inv (h : CoreHyp N N' θ θ' ψ φ z) {x : L} (hx : x ∈ N) : φ x⁻¹ = (φ x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← h.iso.map_mul x hx x⁻¹ (N.inv_mem hx), mul_inv_cancel, CoreHyp.phi_one h]

theorem CoreHyp.phi_pow (h : CoreHyp N N' θ θ' ψ φ z) {x : L} (hx : x ∈ N) (n : ℕ) :
    φ (x ^ n) = φ x ^ n := by
  induction n with
  | zero => rw [pow_zero, CoreHyp.phi_one h, pow_zero]
  | succ n ih =>
      rw [pow_succ x n, h.iso.map_mul (x ^ n) (N.pow_mem hx n) x hx, ih, pow_succ]

theorem CoreHyp.phiZ_ne_one (h : CoreHyp N N' θ θ' ψ φ z) : φ z ≠ 1 := by
  intro hz
  apply h.z_ne_one
  apply h.iso.inj z h.z_mem 1 N.one_mem
  rw [hz, CoreHyp.phi_one h]

theorem CoreHyp.phiZ_sq (h : CoreHyp N N' θ θ' ψ φ z) : φ z ^ 2 = 1 := by
  rw [← CoreHyp.phi_pow h h.z_mem 2, CoreHyp.z_sq h, CoreHyp.phi_one h]

theorem CoreHyp.centre' (h : CoreHyp N N' θ θ' ψ φ z) :
    ∀ x ∈ N', (∀ y ∈ N', x * y = y * x) → x = 1 ∨ x = φ z := by
  intro x hxN' hxcent
  obtain ⟨w, hwN, hw⟩ := h.iso.surj x hxN'
  have hwcent : ∀ y ∈ N, w * y = y * w := by
    intro y hy
    apply h.iso.inj (w * y) (N.mul_mem hwN hy) (y * w) (N.mul_mem hy hwN)
    rw [h.iso.map_mul w hwN y hy, h.iso.map_mul y hy w hwN, hw]
    exact hxcent (φ y) (h.iso.mem y hy)
  rcases h.centre w hwN hwcent with hw1 | hwz
  · left
    rw [← hw, hw1, CoreHyp.phi_one h]
  · right
    rw [← hw, hwz]

theorem CoreHyp.phiZ_central (h : CoreHyp N N' θ θ' ψ φ z) (l' : L') : l' * φ z = φ z * l' := by
  obtain ⟨l, _, hcompat⟩ := h.exists_compat' l'
  have h1 : φ z = l' * φ z * l'⁻¹ := by
    have hthis := hcompat z h.z_mem
    rw [h.z_central l, mul_assoc, mul_inv_cancel, mul_one] at hthis
    exact hthis
  calc l' * φ z = (l' * φ z * l'⁻¹) * l' := by group
    _ = φ z * l' := by rw [← h1]

private theorem innerInv_of_fst (a : A5) (ha : a ≠ 1) (ha2 : a ^ 2 = 1)
    (ψ : A5 × A5 ≃* A5 × A5) : InnerInv (ψ (a, 1)) := by
  have ha2' : a * a = 1 := by simpa [pow_two] using ha2
  have hp2 : ((a, 1) : A5 × A5) ^ 2 = 1 := by
    rw [pow_two, Prod.mk_mul_mk, ha2', one_mul]
    rfl
  rcases Swap.exists_preserves_or_swaps ψ with ⟨hp, _⟩ | ⟨hs, _⟩
  · obtain ⟨a', ha'⟩ := hp.1 a
    have hsq : (a', 1) ^ 2 = (1 : A5 × A5) := by
      calc (a', 1) ^ 2 = ψ (a, 1) ^ 2 := by rw [ha']
        _ = ψ ((a, 1) ^ 2) := (map_pow ψ (a, 1) 2).symm
        _ = 1 := by rw [hp2, map_one]
    refine ⟨a', ?_, ?_, Or.inl ?_⟩
    · intro ha1
      apply ha
      have h : ψ (a, 1) = ψ 1 := by simp [ha', ha1, map_one]
      simpa using congrArg Prod.fst (ψ.injective h)
    · have := congrArg Prod.fst hsq
      simpa using this
    · rw [ha']
  · obtain ⟨a', ha'⟩ := hs.1 a
    have hsq : (1, a') ^ 2 = (1 : A5 × A5) := by
      calc (1, a') ^ 2 = ψ (a, 1) ^ 2 := by rw [ha']
        _ = ψ ((a, 1) ^ 2) := (map_pow ψ (a, 1) 2).symm
        _ = 1 := by rw [hp2, map_one]
    refine ⟨a', ?_, ?_, Or.inr ?_⟩
    · intro ha1
      apply ha
      have h : ψ (a, 1) = ψ 1 := by simp [ha', ha1, map_one]
      simpa using congrArg Prod.fst (ψ.injective h)
    · have := congrArg Prod.snd hsq
      simpa using this
    · rw [ha']

private theorem innerInv_of_snd (a : A5) (ha : a ≠ 1) (ha2 : a ^ 2 = 1)
    (ψ : A5 × A5 ≃* A5 × A5) : InnerInv (ψ (1, a)) := by
  have ha2' : a * a = 1 := by simpa [pow_two] using ha2
  have hp2 : ((1, a) : A5 × A5) ^ 2 = 1 := by
    rw [pow_two, Prod.mk_mul_mk, one_mul, ha2']
    rfl
  rcases Swap.exists_preserves_or_swaps ψ with ⟨hp, _⟩ | ⟨hs, _⟩
  · obtain ⟨a', ha'⟩ := hp.2 a
    have hsq : (1, a') ^ 2 = (1 : A5 × A5) := by
      calc (1, a') ^ 2 = ψ (1, a) ^ 2 := by rw [ha']
        _ = ψ ((1, a) ^ 2) := (map_pow ψ (1, a) 2).symm
        _ = 1 := by rw [hp2, map_one]
    refine ⟨a', ?_, ?_, Or.inr ?_⟩
    · intro ha1
      apply ha
      have h : ψ (1, a) = ψ 1 := by simp [ha', ha1, map_one]
      simpa using congrArg Prod.snd (ψ.injective h)
    · have := congrArg Prod.snd hsq
      simpa using this
    · rw [ha']
  · obtain ⟨a', ha'⟩ := hs.2 a
    have hsq : (a', 1) ^ 2 = (1 : A5 × A5) := by
      calc (a', 1) ^ 2 = ψ (1, a) ^ 2 := by rw [ha']
        _ = ψ ((1, a) ^ 2) := (map_pow ψ (1, a) 2).symm
        _ = 1 := by rw [hp2, map_one]
    refine ⟨a', ?_, ?_, Or.inl ?_⟩
    · intro ha1
      apply ha
      have h : ψ (1, a) = ψ 1 := by simp [ha', ha1, map_one]
      simpa using congrArg Prod.snd (ψ.injective h)
    · have := congrArg Prod.fst hsq
      simpa using this
    · rw [ha']

theorem InnerInv.map {g : A5 × A5} (hg : InnerInv g) (ψ : A5 × A5 ≃* A5 × A5) : InnerInv (ψ g) := by
  obtain ⟨a, ha_ne, ha_sq, hg | hg⟩ := hg
  · rw [hg]
    exact innerInv_of_fst a ha_ne ha_sq ψ
  · rw [hg]
    exact innerInv_of_snd a ha_ne ha_sq ψ

end CFSG.EvenSporadicStandard.HNRecog.ML1
