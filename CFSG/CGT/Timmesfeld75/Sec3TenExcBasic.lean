module

public import CFSG.CGT.Timmesfeld75.StrongClosure

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open DihedralGroup

section Centralizer

variable {G : Type} [Group G]

theorem mem_conj_of_mem_classD_of_centralizes [Finite G] {T : Subgroup G} (hT : IsWC T) {k : G}
    {d : G} (hd : d ∈ classD T) (hdc : ∀ t ∈ conjSubgroup k T, d * t = t * d) :
    d ∈ conjSubgroup k T := by
  obtain ⟨g, t, htT, ht1, rfl⟩ := hd
  have hmem : g⁻¹ * t * g ∈ conjSubgroup g⁻¹ T := by
    rw [mem_conjSubgroup, inv_inv]
    have e : g * (g⁻¹ * t * g) * g⁻¹ = t := by group
    rw [e]
    exact htT
  have hd1 : g⁻¹ * t * g ≠ 1 := by
    intro h
    apply ht1
    have e : t = g * (g⁻¹ * t * g) * g⁻¹ := by group
    rw [e, h]
    group
  have hwc := hT.conj g⁻¹
  have hN : conjSubgroup k T ≤ Subgroup.normalizer (conjSubgroup g⁻¹ T : Set G) := fun y hy =>
    hwc.centralizer_le_normalizer hmem hd1
      (Subgroup.mem_centralizer_singleton_iff.2 (hdc y hy).symm)
  have heq : conjSubgroup k T = conjSubgroup g⁻¹ T := by
    refine eq_of_le_normalizer_of_isWC hwc ⟨k * g, ?_⟩ hN
    rw [conjSubgroup_conjSubgroup, show k * g * g⁻¹ = k by group]
  rw [heq]
  exact hmem

end Centralizer

section Dihedral

theorem zmod_odd_two_mul_eq_zero {n : ℕ} (hn : Odd n) {k : ZMod n} (h : 2 * k = 0) : k = 0 := by
  obtain ⟨m, hm⟩ := hn
  have h0 : ((2 * m + 1 : ℕ) : ZMod n) = 0 := by
    rw [← hm]
    exact ZMod.natCast_self n
  push_cast at h0
  linear_combination k * h0 - (m : ZMod n) * h

theorem dih_eq_one_or_of_comm_sr {n : ℕ} (hn : Odd n) {g : DihedralGroup n} (j : ZMod n)
    (h : g * sr j = sr j * g) : g = 1 ∨ g = sr j := by
  rcases g with k | k
  · left
    rw [r_mul_sr, sr_mul_r] at h
    have h1 : j - k = j + k := sr.inj h
    have h2 : 2 * k = 0 := by linear_combination h1.symm
    rw [zmod_odd_two_mul_eq_zero hn h2]
    rfl
  · right
    rw [sr_mul_sr, sr_mul_sr] at h
    have h1 : j - k = k - j := r.inj h
    have h2 : 2 * (j - k) = 0 := by linear_combination h1
    have h3 := zmod_odd_two_mul_eq_zero hn h2
    rw [sub_eq_zero.1 h3]

theorem dih_exists_sr_of_sq {n : ℕ} (hn : Odd n) {g : DihedralGroup n} (h : g * g = 1)
    (h1 : g ≠ 1) : ∃ j : ZMod n, g = sr j := by
  rcases g with k | k
  · exfalso
    apply h1
    rw [r_mul_r] at h
    have h2 : k + k = 0 := r.inj h
    have h3 : 2 * k = 0 := by linear_combination h2
    rw [zmod_odd_two_mul_eq_zero hn h3]
    rfl
  · exact ⟨k, rfl⟩

theorem dih5_conj_dichotomy (ψ : DihedralGroup 5 →* DihedralGroup 5)
    (hψψ : ∀ g, ψ (ψ g) = g) {i₀ i₁ i₂ : ZMod 5} (h0 : ψ (sr i₀) = sr i₀)
    (h1 : ψ (sr i₁) = sr i₂) : i₂ = i₁ ∨ i₂ = 2 * i₀ - i₁ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases hd : i₁ - i₀ = 0
  · left
    have : i₁ = i₀ := sub_eq_zero.1 hd
    subst this
    exact sr.inj (h1.symm.trans h0)
  have hr : ψ (r (i₁ - i₀)) = r (i₂ - i₀) := by
    have e : (r (i₁ - i₀) : DihedralGroup 5) = sr i₀ * sr i₁ := (sr_mul_sr i₀ i₁).symm
    rw [e, map_mul, h0, h1, sr_mul_sr]
  set d := i₁ - i₀ with hdd
  set d' := i₂ - i₀ with hdd'
  have hd0 : d ≠ 0 := hd
  have hm : (r d' : DihedralGroup 5) = (r d) ^ ((d' / d : ZMod 5).val) := by
    rw [r_pow]
    congr 1
    rw [ZMod.natCast_zmod_val]
    field_simp
  have h2 : ψ (r d') = r d := by
    have := hψψ (r d)
    rwa [hr] at this
  have h3 : ψ (r d') = r ((d' / d) * d') := by
    rw [hm, map_pow, hr, r_pow]
    congr 1
    rw [ZMod.natCast_zmod_val, mul_comm]
  rw [h2] at h3
  have h4 : d = (d' / d) * d' := r.inj h3
  have h5 : d' ^ 2 = d ^ 2 := by
    field_simp at h4
    linear_combination -h4
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h5 with h6 | h6
  · left
    rw [hdd, hdd'] at h6
    linear_combination h6
  · right
    rw [hdd, hdd'] at h6
    linear_combination h6

end Dihedral

end CFSG.CGT.Timmesfeld75
