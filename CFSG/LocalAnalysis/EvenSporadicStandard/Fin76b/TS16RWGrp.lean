module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RL1

public section

namespace CFSG.EvenSporadicStandard.Fin76b.W16

open Subgroup CFSG.EvenSporadicStandard.Fin76b.LiftRL

section Grp

variable {M : Type*} [Group M] {N : Subgroup M} [N.Normal] {t : M}

theorem t_not_mem_N (hN : ∀ n ∈ N, Odd (orderOf n)) (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    t ∉ N := by
  intro h
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  have h2 := hN t h
  rw [hord] at h2
  exact absurd h2 (by decide)

theorem eq_one_of_sq_eq_one {n : M} (hn : Odd (orderOf n)) (h2 : n * n = 1) : n = 1 := by
  have hd : orderOf n ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
  have h1 : orderOf n = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact h
    · rw [h] at hn
      exact absurd hn (by decide)
  exact orderOf_eq_one_iff.1 h1

theorem ker_decomp (ht2 : t * t = 1) (ht1 : t ≠ 1) {k : M} (hk : k ∈ N ⊔ zpowers t) :
    ∃ n ∈ N, k = n ∨ k = n * t := by
  have h := hk
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at h
  obtain ⟨n, hn, s, hs, rfl⟩ := h
  rcases mem_zpowers_involution ht2 ht1 hs with rfl | rfl
  · exact ⟨n, hn, Or.inl (mul_one n)⟩
  · exact ⟨n, hn, Or.inr rfl⟩

theorem sq_mul_t (ht2 : t * t = 1) (htc : ∀ m : M, m * t = t * m) (x : M) :
    (x * t) * (x * t) = x * x := by
  have ht' : ∀ y : M, t * y = y * t := fun y => (htc y).symm
  calc (x * t) * (x * t) = x * (t * x) * t := by group
    _ = x * (x * t) * t := by rw [ht' x]
    _ = (x * x) * (t * t) := by group
    _ = x * x := by rw [ht2, mul_one]

theorem invol_ker_eq_t (hN : ∀ n ∈ N, Odd (orderOf n)) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (htc : ∀ m : M, m * t = t * m) {η : M} (hη : η ∈ N ⊔ zpowers t) (h2 : η * η = 1)
    (h1 : η ≠ 1) : η = t := by
  obtain ⟨n, hn, h | h⟩ := ker_decomp ht2 ht1 hη
  · rw [h] at h2 h1
    exact absurd (eq_one_of_sq_eq_one (hN n hn) h2) h1
  · rw [h, sq_mul_t ht2 htc] at h2
    rw [h, eq_one_of_sq_eq_one (hN n hn) h2, one_mul]

theorem twist_contra (hN : ∀ n ∈ N, Odd (orderOf n)) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (htc : ∀ m : M, m * t = t * m) {z b0 : M} (hz2 : z * z = 1) (hzb : z * b0 * z⁻¹ = b0)
    (hb2 : b0 * b0 = t) (hNb : ∀ n ∈ N, b0 * n = n * b0) {k : M} (hk : k ∈ N ⊔ zpowers t)
    (hy : (z * b0 * k) * (z * b0 * k) = 1) : False := by
  have hz1 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have key : ∀ n ∈ N, (z * b0 * n) * (z * b0 * n) = t * ((z * n * z⁻¹) * n) := by
    intro n hn
    have hn' : z * n * z⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance n hn z
    have hc1 : b0 * (z * n * z⁻¹) = (z * n * z⁻¹) * b0 := hNb _ hn'
    calc (z * b0 * n) * (z * b0 * n)
        = (z * b0 * z⁻¹) * (z * n * z⁻¹) * (z * z) * b0 * n := by group
      _ = b0 * (z * n * z⁻¹) * 1 * b0 * n := by rw [hzb, hz2]
      _ = b0 * ((z * n * z⁻¹) * b0) * n := by group
      _ = b0 * (b0 * (z * n * z⁻¹)) * n := by rw [hc1]
      _ = (b0 * b0) * ((z * n * z⁻¹) * n) := by group
      _ = t * ((z * n * z⁻¹) * n) := by rw [hb2]
  have hnot : ∀ n ∈ N, (z * b0 * n) * (z * b0 * n) ≠ 1 := by
    intro n hn h
    rw [key n hn] at h
    have hn' : z * n * z⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance n hn z
    have hmem : (z * n * z⁻¹) * n ∈ N := N.mul_mem hn' hn
    have : t = ((z * n * z⁻¹) * n)⁻¹ := eq_inv_of_mul_eq_one_left h
    exact t_not_mem_N hN ht2 ht1 (this ▸ N.inv_mem hmem)
  obtain ⟨n, hn, h | h⟩ := ker_decomp ht2 ht1 hk
  · rw [h] at hy
    exact hnot n hn hy
  · apply hnot n hn
    have e : z * b0 * k = (z * b0 * n) * t := by rw [h]; group
    rw [e, sq_mul_t ht2 htc] at hy
    exact hy

theorem invol_coset_z_conj (ht2 : t * t = 1) (ht1 : t ≠ 1) (htc : ∀ m : M, m * t = t * m)
    (hN : ∀ n ∈ N, Odd (orderOf n)) {z : M} (hz2 : z * z = 1) {w : M} (hw : z * w * z⁻¹ = w * t)
    {k : M} (hk : k ∈ N ⊔ zpowers t) (hy : (z * k) * (z * k) = 1) :
    ∃ m : M, z * k = m * z * m⁻¹ := by
  have ht' : ∀ x : M, t * x = x * t := fun x => (htc x).symm
  have hzt : t * z = w⁻¹ * z * w := by
    have h1 : z * w = w * t * z := by
      calc z * w = z * w * z⁻¹ * z := by group
        _ = w * t * z := by rw [hw]
    calc t * z = w⁻¹ * (w * t * z) := by group
      _ = w⁻¹ * (z * w) := by rw [h1]
      _ = w⁻¹ * z * w := by group
  obtain ⟨n, hn, hk' | hk'⟩ := ker_decomp ht2 ht1 hk
  · rw [hk'] at hy ⊢
    obtain ⟨h, hh, hconj⟩ := mem_conjOrbit_of_involution (hN n hn) hn hz2 hy
    exact ⟨h, hconj.symm⟩
  · have e : z * k = (z * n) * t := by rw [hk']; group
    rw [e, sq_mul_t ht2 htc] at hy
    obtain ⟨h, hh, hconj⟩ := mem_conjOrbit_of_involution (hN n hn) hn hz2 hy
    refine ⟨h * w⁻¹, ?_⟩
    calc z * k = (z * n) * t := e
      _ = (h * z * h⁻¹) * t := by rw [hconj]
      _ = h * (t * z) * h⁻¹ := by
          calc (h * z * h⁻¹) * t = h * z * (h⁻¹ * t) := by group
            _ = h * z * (t * h⁻¹) := by rw [← ht' h⁻¹]
            _ = h * (z * t) * h⁻¹ := by group
            _ = h * (t * z) * h⁻¹ := by rw [← ht' z]
      _ = h * (w⁻¹ * z * w) * h⁻¹ := by rw [hzt]
      _ = (h * w⁻¹) * z * (h * w⁻¹)⁻¹ := by group

end Grp

theorem card_centralizer_conj {G : Type*} [Group G] (c r : G) :
    Nat.card (Subgroup.centralizer ({c * r * c⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({r} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨c⁻¹ * x * c, ?_⟩
      invFun := fun x => ⟨c * x * c⁻¹, ?_⟩
      left_inv := fun x => ?_
      right_inv := fun x => ?_ }
  · have hx := x.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    calc (c⁻¹ * x * c) * r = c⁻¹ * (x * (c * r * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * r * c⁻¹) * x) * c := by rw [hx]
      _ = r * (c⁻¹ * x * c) := by group
  · have hx := x.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    calc (c * x * c⁻¹) * (c * r * c⁻¹) = c * (x * r) * c⁻¹ := by group
      _ = c * (r * x) * c⁻¹ := by rw [hx]
      _ = (c * r * c⁻¹) * (c * x * c⁻¹) := by group
  · apply Subtype.ext
    simp only
    group
  · apply Subtype.ext
    simp only
    group

end CFSG.EvenSporadicStandard.Fin76b.W16
