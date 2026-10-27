module

public import CFSG.GF2Type.Aschbacher1976Full.HSAutBasic

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.PartE

variable {G : Type} [Group G] [Finite G] {z : G} {T V : Subgroup G}

structure IsBasis (z : G) (V : Subgroup G) (t₁ t₂ : G) : Prop where
  mem₁ : t₁ ∈ V
  mem₂ : t₂ ∈ V
  not_mem₁ : t₁ ∉ Subgroup.zpowers z
  not_mem₂ : t₂ ∉ Subgroup.zpowers z
  not_mem₃ : t₁ * t₂ ∉ Subgroup.zpowers z

theorem ne_one_ne_z_of_not_mem {t : G} (ht : t ∉ Subgroup.zpowers z) : t ≠ 1 ∧ t ≠ z :=
  ⟨fun h => ht (h ▸ Subgroup.one_mem _), fun h => ht (h ▸ Subgroup.mem_zpowers z)⟩

theorem exists_basis (hz : orderOf z = 2) (hV : HSV z T V) :
    ∃ t₁ t₂ : G, IsBasis z V t₁ t₂ := by
  classical
  obtain ⟨t₁, ht₁V, ht₁z⟩ := hsAut_exists_not_mem_zpowers hz hV
  have hab := hV.isElem.1
  obtain ⟨t₂, ht₂V, ht₂⟩ : ∃ t₂ ∈ V, t₂ ∉ (↑({1, z, t₁, z * t₁} : Finset G) : Set G) := by
    by_contra hcon
    push Not at hcon
    have hsub : (V : Set G) ⊆ (↑({1, z, t₁, z * t₁} : Finset G) : Set G) := hcon
    have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h1
    have h2 : (V : Set G).ncard = 8 := by
      rw [← Nat.card_coe_set_eq]
      exact hV.card_eq
    have h3 := Finset.card_le_four (a := (1 : G)) (b := z) (c := t₁) (d := z * t₁)
    omega
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
    not_or] at ht₂
  obtain ⟨h2one, h2z, h2t, h2zt⟩ := ht₂
  have hsq : ∀ {a : G}, a ∈ V → a * a = 1 := fun ha => hsAut_mul_self hV ha
  refine ⟨t₁, t₂, ht₁V, ht₂V, ht₁z, ?_, ?_⟩
  · intro hmem
    rcases Width.mem_zpowers_involution hz hmem with h | h
    · exact h2one h
    · exact h2z h
  · intro hmem
    rcases Width.mem_zpowers_involution hz hmem with h | h
    · apply h2t
      have := hsq ht₁V
      calc t₂ = t₁ * (t₁ * t₂) := by rw [← mul_assoc, this, one_mul]
        _ = t₁ := by rw [h, mul_one]
    · apply h2zt
      have := hsq ht₁V
      calc t₂ = t₁ * (t₁ * t₂) := by rw [← mul_assoc, this, one_mul]
        _ = t₁ * z := by rw [h]
        _ = z * t₁ := hsAut_mul_comm hV ht₁V hV.z_mem

theorem exists_noncomm_F (hset : HSSetting G z) (hV : HSV z T V) {t : G} (htV : t ∈ V)
    (htz : t ∉ Subgroup.zpowers z) : ∃ f ∈ Fz z, t * f ≠ f * t := by
  have hz : orderOf z = 2 := hset.1.2.2.1
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hset.2
  have ht1 := (ne_one_ne_z_of_not_mem htz).1
  by_contra hcon
  push Not at hcon
  have htZ : t ∈ Z := Width.mem_Z_of_comm hD hz (hV.le_F htV) fun b hb =>
    hcon b (hD.sup_eq ▸ Subgroup.mem_sup_right hb)
  have htsq : t ^ 2 = 1 := by rw [pow_two]; exact hsAut_mul_self hV htV
  exact htz (Width.involution_eq hD hz htZ htsq ht1 ▸ Subgroup.mem_zpowers z)

theorem zpow_of_mul_self_eq_one {g : G} (hg : g * g = 1) (n : ℤ) :
    (Even n → g ^ n = 1) ∧ (Odd n → g ^ n = g) := by
  have hg2 : g ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hg
  constructor
  · rintro ⟨r, rfl⟩
    rw [← two_mul, zpow_mul, hg2, one_zpow]
  · rintro ⟨r, rfl⟩
    rw [zpow_add_one, zpow_mul, hg2, one_zpow, one_mul]

theorem independent_of_basis {t₁ t₂ : G} (hz1 : z ≠ 1) (hz2 : z * z = 1) (h1 : t₁ * t₁ = 1)
    (h2 : t₂ * t₂ = 1) (hb : IsBasis z V t₁ t₂) (i j l : ℤ)
    (h : z ^ i * t₁ ^ j * t₂ ^ l = 1) : Even i ∧ Even j ∧ Even l := by
  have hmemz : ∀ {a : G}, a = z⁻¹ → a ∈ Subgroup.zpowers z := fun ha =>
    ha ▸ Subgroup.inv_mem _ (Subgroup.mem_zpowers z)
  have ht1 := (ne_one_ne_z_of_not_mem hb.not_mem₁).1
  have ht2 := (ne_one_ne_z_of_not_mem hb.not_mem₂).1
  obtain ⟨zE, zO⟩ := zpow_of_mul_self_eq_one hz2 i
  obtain ⟨t1E, t1O⟩ := zpow_of_mul_self_eq_one h1 j
  obtain ⟨t2E, t2O⟩ := zpow_of_mul_self_eq_one h2 l
  rcases Int.even_or_odd i with hi | hi <;> rcases Int.even_or_odd j with hj | hj <;>
    rcases Int.even_or_odd l with hl | hl
  · exact ⟨hi, hj, hl⟩
  · rw [zE hi, t1E hj, t2O hl] at h
    simp at h
    exact absurd h ht2
  · rw [zE hi, t1O hj, t2E hl] at h
    simp at h
    exact absurd h ht1
  · rw [zE hi, t1O hj, t2O hl, one_mul] at h
    exact absurd (h ▸ Subgroup.one_mem _) hb.not_mem₃
  · rw [zO hi, t1E hj, t2E hl] at h
    simp at h
    exact absurd h hz1
  · rw [zO hi, t1E hj, t2O hl, mul_one] at h
    exact absurd (hmemz (eq_inv_of_mul_eq_one_right h)) hb.not_mem₂
  · rw [zO hi, t1O hj, t2E hl, mul_one] at h
    exact absurd (hmemz (eq_inv_of_mul_eq_one_right h)) hb.not_mem₁
  · rw [zO hi, t1O hj, t2O hl, mul_assoc] at h
    exact absurd (hmemz (eq_inv_of_mul_eq_one_right h)) hb.not_mem₃

end CFSG.GF2Type.Aschbacher1976Full.HS.PartE
