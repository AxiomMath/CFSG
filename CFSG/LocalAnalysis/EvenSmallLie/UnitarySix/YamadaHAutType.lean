module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAutModel

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaHAut

open CFSG.Fischer Subgroup


theorem pow_mul_dP_pow {l : Equiv.Perm (Fin 693)} (hl : l ∈ T46) (a : ℕ) :
    ∀ n : ℕ, ∃ l' ∈ T46, (l * dP ^ a) ^ n = l' * dP ^ (a * n)
  | 0 => ⟨1, one_mem _, by simp⟩
  | n + 1 => by
    obtain ⟨l', hl', h⟩ := pow_mul_dP_pow hl a n
    refine ⟨l' * (dP ^ (a * n) * l * (dP ^ (a * n))⁻¹),
      mul_mem hl' ((conj_mem_T46_iff (pow_mem dP_mem_autT _)).2 hl), ?_⟩
    rw [pow_succ, h, Nat.mul_succ, pow_add]
    group

theorem mem_T46_of_pow_two_pow {l : Equiv.Perm (Fin 693)} (hl : l ∈ T46) {a k : ℕ}
    (h : (l * dP ^ a) ^ 2 ^ k = 1) : l * dP ^ a ∈ T46 := by
  obtain ⟨l', hl', e⟩ := pow_mul_dP_pow hl a (2 ^ k)
  rw [h] at e
  have h1 : dP ^ ((a * 2 ^ k : ℕ) : ℤ) * sP ^ (0 : ℤ) ∈ T46 := by
    rw [zpow_zero, mul_one, zpow_natCast]
    have : dP ^ (a * 2 ^ k) = l'⁻¹ := eq_inv_of_mul_eq_one_right e.symm
    rw [this]
    exact inv_mem hl'
  have h3 := (zpow_mem_T46 h1).1
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by decide)
  have h4 : 3 ∣ a * 2 ^ k := by exact_mod_cast h3
  have h5 : 3 ∣ a := (Nat.Coprime.dvd_of_dvd_mul_right hcop h4)
  obtain ⟨c, rfl⟩ := h5
  rw [pow_mul, dP_pow_three, one_pow, mul_one]
  exact hl

theorem mem_T46_of_zpow_two_pow {l : Equiv.Perm (Fin 693)} (hl : l ∈ T46) {c : ℤ} {k : ℕ}
    (h : (l * dP ^ c) ^ 2 ^ k = 1) : l * dP ^ c ∈ T46 := by
  have h3 : dP ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, dP_pow_three]
  have hc : dP ^ c = dP ^ (c % 3).toNat := by
    rw [zpow_eq_zpow_emod c h3, ← zpow_natCast,
      Int.toNat_of_nonneg (Int.emod_nonneg c (by norm_num))]
  rw [hc] at h ⊢
  exact mem_T46_of_pow_two_pow hl h

theorem field_of_pow_two_pow {y : Equiv.Perm (Fin 693)} (hy : y ∈ autT) {k : ℕ}
    (h : y ^ 2 ^ k = 1) (hT : y ∉ T46) : ∃ l ∈ T46, ∃ a < 3, y = l * dP ^ a * sP := by
  obtain ⟨l, hl, a, ha, j, hj, rfl⟩ := mem_autT_iff.1 hy
  interval_cases j
  · exfalso
    rw [pow_zero, mul_one] at h hT
    exact hT (mem_T46_of_pow_two_pow hl h)
  · exact ⟨l, hl, a, ha, by rw [pow_one]⟩

theorem sP_conj_dP_zpow (c : ℤ) : sP * dP ^ c * sP⁻¹ = dP ^ (-c) := by
  have h : (MulAut.conj sP) (dP ^ c) = ((MulAut.conj sP) dP) ^ c := map_zpow _ _ _
  simp only [MulAut.conj_apply] at h
  rw [h, sP_conj_dP, zpow_neg, inv_zpow]

theorem inv_mul_mem_T46_of_field {l₁ l₂ : Equiv.Perm (Fin 693)} (hl₁ : l₁ ∈ T46) (hl₂ : l₂ ∈ T46)
    (a b : ℕ) {k : ℕ} (h : ((l₁ * dP ^ a * sP)⁻¹ * (l₂ * dP ^ b * sP)) ^ 2 ^ k = 1) :
    (l₁ * dP ^ a * sP)⁻¹ * (l₂ * dP ^ b * sP) ∈ T46 := by
  set u := sP⁻¹ * dP ^ (-(a : ℤ)) with hu
  have huA : u ∈ autT := mul_mem (inv_mem sP_mem_autT) (zpow_mem dP_mem_autT _)
  set l' := u * (l₁⁻¹ * l₂) * u⁻¹ with hl'
  have hl'T : l' ∈ T46 := (conj_mem_T46_iff huA).2 (mul_mem (inv_mem hl₁) hl₂)
  have e1 : (l₁ * dP ^ a * sP)⁻¹ * (l₂ * dP ^ b * sP) = l' * dP ^ ((a : ℤ) - b) := by
    have e2 : sP⁻¹ * dP ^ ((b : ℤ) - a) * sP = dP ^ ((a : ℤ) - b) := by
      rw [sP_inv]
      have := sP_conj_dP_zpow ((b : ℤ) - a)
      rw [sP_inv] at this
      rw [this, neg_sub]
    rw [← e2, hl', hu]
    simp only [← zpow_natCast]
    group
  rw [e1] at h ⊢
  exact mem_T46_of_zpow_two_pow hl'T h

theorem dP_pow_mul_sP_sq (a : ℕ) : dP ^ a * sP * (dP ^ a * sP) = 1 := by
  have h := sP_conj_dP_zpow (a : ℤ)
  rw [zpow_natCast] at h
  calc dP ^ a * sP * (dP ^ a * sP) = dP ^ a * (sP * dP ^ a * sP⁻¹) * (sP * sP) := by group
    _ = 1 := by rw [h, sP_mul_self, mul_one, zpow_neg, zpow_natCast, mul_inv_cancel]

theorem dP_pow_mul_sP_not_mem {a : ℕ} (ha : a < 3) : dP ^ a * sP ∉ T46 := fun h => by
  have := eq_zero_of_mem_T46 a ha 1 (by norm_num) (by rwa [pow_one])
  exact absurd this.2 (by norm_num)

theorem inv_mul_mem_T46 {X : Subgroup (Equiv.Perm (Fin 693))} (hX : X ≤ autT) (h2 : IsPGroup 2 X)
    {x y : Equiv.Perm (Fin 693)} (hx : x ∈ X) (hxT : x ∉ T46) (hy : y ∈ X) (hyT : y ∉ T46) :
    x⁻¹ * y ∈ T46 := by
  obtain ⟨k₁, hk₁⟩ := h2 ⟨x, hx⟩
  obtain ⟨k₂, hk₂⟩ := h2 ⟨y, hy⟩
  obtain ⟨k₃, hk₃⟩ := h2 ⟨x⁻¹ * y, mul_mem (inv_mem hx) hy⟩
  have e1 : x ^ 2 ^ k₁ = 1 := by simpa using congrArg Subtype.val hk₁
  have e2 : y ^ 2 ^ k₂ = 1 := by simpa using congrArg Subtype.val hk₂
  have e3 : (x⁻¹ * y) ^ 2 ^ k₃ = 1 := by simpa using congrArg Subtype.val hk₃
  obtain ⟨l₁, hl₁, a, -, rfl⟩ := field_of_pow_two_pow (hX hx) e1 hxT
  obtain ⟨l₂, hl₂, b, -, rfl⟩ := field_of_pow_two_pow (hX hy) e2 hyT
  exact inv_mul_mem_T46_of_field hl₁ hl₂ a b e3

theorem card_le_two_mul_inf {X : Subgroup (Equiv.Perm (Fin 693))} (hX : X ≤ autT)
    (h2 : IsPGroup 2 X) : Nat.card X ≤ 2 * Nat.card (X ⊓ T46 : Subgroup (Equiv.Perm (Fin 693))) := by
  classical
  by_cases hle : X ≤ T46
  · rw [inf_eq_left.2 hle]
    omega
  · obtain ⟨x, hxX, hxT⟩ := Set.not_subset.1 hle
    let f : X → (X ⊓ T46 : Subgroup (Equiv.Perm (Fin 693))) ⊕
        (X ⊓ T46 : Subgroup (Equiv.Perm (Fin 693))) := fun y =>
      if hy : (y : Equiv.Perm (Fin 693)) ∈ T46 then Sum.inl ⟨y, Subgroup.mem_inf.2 ⟨y.2, hy⟩⟩
      else Sum.inr ⟨x⁻¹ * y, Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hxX) y.2,
        inv_mul_mem_T46 hX h2 hxX hxT y.2 hy⟩⟩
    have hf : Function.Injective f := by
      intro y y' h
      by_cases hy : (y : Equiv.Perm (Fin 693)) ∈ T46 <;>
        by_cases hy' : (y' : Equiv.Perm (Fin 693)) ∈ T46 <;>
        simp only [f, hy, hy', dite_true, dite_false, Sum.inl.injEq, Sum.inr.injEq,
          reduceCtorEq] at h
      · exact Subtype.ext (Subtype.mk.inj h)
      · exact Subtype.ext (mul_left_cancel (Subtype.mk.inj h))
    calc Nat.card X ≤ Nat.card ((X ⊓ T46 : Subgroup (Equiv.Perm (Fin 693))) ⊕
          (X ⊓ T46 : Subgroup (Equiv.Perm (Fin 693)))) := Nat.card_le_card_of_injective f hf
      _ = 2 * Nat.card (X ⊓ T46 : Subgroup (Equiv.Perm (Fin 693))) := by
        rw [Nat.card_sum]
        ring

end CFSG.EvenSmallLie.UnitarySix.YamadaHAut
