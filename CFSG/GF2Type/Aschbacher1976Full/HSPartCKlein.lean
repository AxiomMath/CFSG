module

public import CFSG.GF2Type.Aschbacher1976Full.HSPartCSq

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint CFSG.GF2Type.CenterFour Subgroup

variable {G : Type} [Group G] [Finite G]

namespace PartC

theorem exists_mem_not_mem_finset {V : Subgroup G} (s : Finset G) (h : s.card < Nat.card V) :
    ∃ t ∈ V, t ∉ s := by
  by_contra hcon
  have hsub : (V : Set G) ⊆ (s : Set G) := fun t ht =>
    Finset.mem_coe.mpr (by_contra fun hts => hcon ⟨t, ht, hts⟩)
  have h1 : Set.ncard (V : Set G) ≤ Set.ncard (s : Set G) :=
    Set.ncard_le_ncard hsub s.finite_toSet
  rw [Set.ncard_coe_finset] at h1
  have h2 : Nat.card V = Set.ncard (V : Set G) := Nat.card_coe_set_eq (V : Set G)
  omega

theorem exists_independent {z : G} {V : Subgroup G} (hVc : Nat.card V = 8) :
    ∃ t₁ ∈ V, ∃ t₂ ∈ V, t₁ ≠ 1 ∧ t₁ ≠ z ∧ t₂ ≠ 1 ∧ t₂ ≠ z ∧ t₂ ≠ t₁ ∧ t₂ ≠ t₁ * z := by
  classical
  obtain ⟨t₁, ht₁, h₁⟩ := exists_mem_not_mem_finset (V := V) {1, z}
    (by rw [hVc]; exact lt_of_le_of_lt Finset.card_le_two (by norm_num))
  obtain ⟨t₂, ht₂, h₂⟩ := exists_mem_not_mem_finset (V := V) {1, z, t₁, t₁ * z}
    (by rw [hVc]; exact lt_of_le_of_lt Finset.card_le_four (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h₁ h₂
  exact ⟨t₁, ht₁, t₂, ht₂, h₁.1, h₁.2, h₂.1, h₂.2.1, h₂.2.2.1, h₂.2.2.2⟩

section Klein

variable {z : G} {Z A : Subgroup G} {T V : Subgroup G}

theorem mem_Dinv_of_mem_V (hV : HSV z T V) {t : G} (ht : t ∈ V) (h1 : t ≠ 1) (hz : t ≠ z) :
    t ∈ Dinv z :=
  ⟨hV.isConj t ht h1, hz, (hV.ZF_le t ht h1).trans hV.le_H⟩

theorem klein_four (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z))
    (hti : HSTI z) (hV : HSV z T V) {t₁ t₂ : G} (h₁ : t₁ ∈ V) (h₂ : t₂ ∈ V) (n1 : t₁ ≠ 1)
    (nz1 : t₁ ≠ z) (n2 : t₂ ≠ 1) (nz2 : t₂ ≠ z) (d12 : t₂ ≠ t₁) (d12' : t₂ ≠ t₁ * z) :
    t₁ * t₂ ≠ 1 ∧ t₁ * t₂ ≠ z ∧ yBar z t₁ * yBar z t₂ = yBar z t₂ * yBar z t₁ ∧
      yBar z t₁ ≠ yBar z t₂ ∧ yBar z (t₁ * t₂) = yBar z t₁ * yBar z t₂ := by
  have hV2 : ∀ a ∈ V, a * a = 1 := fun a ha => by rw [← pow_two]; exact hV.isElem.2 a ha
  have h₃ : t₁ * t₂ ∈ V := V.mul_mem h₁ h₂
  have ht1i : t₁⁻¹ = t₁ := inv_eq_of_mul_eq_one_left (hV2 t₁ h₁)
  have n3 : t₁ * t₂ ≠ 1 := fun h => d12 (by
    have := eq_inv_of_mul_eq_one_right h
    rw [this, ht1i])
  have nz3 : t₁ * t₂ ≠ z := fun h => d12' (by
    calc t₂ = t₁⁻¹ * (t₁ * t₂) := by group
      _ = t₁ * z := by rw [h, ht1i])
  have hD1 : t₁ ∈ Dinv z := mem_Dinv_of_mem_V hV h₁ n1 nz1
  have hD2 : t₂ ∈ Dinv z := mem_Dinv_of_mem_V hV h₂ n2 nz2
  have hD3 : t₁ * t₂ ∈ Dinv z := mem_Dinv_of_mem_V hV h₃ n3 nz3
  obtain ⟨Y₁, hY₁⟩ := exists_gen_H hD hz hF2 hD1
  obtain ⟨Y₂, hY₂⟩ := exists_gen_H hD hz hF2 hD2
  obtain ⟨Y₃, hY₃⟩ := exists_gen_H hD hz hF2 hD3
  have hW₁ : (Y₁ : G) ∈ WT T z := hV.ZF_le_W t₁ h₁ n1 (hY₁ ▸ mem_zpowers _)
  have hW₂ : (Y₂ : G) ∈ WT T z := hV.ZF_le_W t₂ h₂ n2 (hY₂ ▸ mem_zpowers _)
  have hW₃ : (Y₃ : G) ∈ WT T z := hV.ZF_le_W (t₁ * t₂) h₃ n3 (hY₃ ▸ mem_zpowers _)
  have hs₁ : (Y₁ : G) ^ 2 = t₁ := (gen_props hD hz hF2 hD1.1 hY₁).2
  have hs₂ : (Y₂ : G) ^ 2 = t₂ := (gen_props hD hz hF2 hD2.1 hY₂).2
  have hs₃ : (Y₃ : G) ^ 2 = t₁ * t₂ := (gen_props hD hz hF2 hD3.1 hY₃).2
  have k12 : Commute (Y₁ : G) (Y₂ : G) := hV.W_comm _ hW₁ _ hW₂
  have k13 : Commute (Y₁ : G) (Y₃ : G) := hV.W_comm _ hW₁ _ hW₃
  have k23 : Commute (Y₂ : G) (Y₃ : G) := hV.W_comm _ hW₂ _ hW₃
  have c12 : Y₁ * Y₂ = Y₂ * Y₁ := Subtype.ext k12
  have e1 : yBar z t₁ = qmk z Y₁ := yBar_eq hD hz hF2 hti hD1 hY₁
  have e2 : yBar z t₂ = qmk z Y₂ := yBar_eq hD hz hF2 hti hD2 hY₂
  have e3 : yBar z (t₁ * t₂) = qmk z Y₃ := yBar_eq hD hz hF2 hti hD3 hY₃
  refine ⟨n3, nz3, ?_, ?_, ?_⟩
  · rw [e1, e2, ← map_mul, ← map_mul, c12]
  · intro heq
    rw [e1, e2] at heq
    have h1 : qmk z (Y₁⁻¹ * Y₂) = 1 := by
      rw [map_mul, map_inv, heq, inv_mul_cancel]
    have hF : (Y₁ : G)⁻¹ * Y₂ ∈ Fz z := (qmk_eq_one_iff z _).mp h1
    have hcomm : Commute ((Y₁ : G)⁻¹) (Y₂ : G) := k12.inv_left
    have hsq : ((Y₁ : G)⁻¹ * Y₂) ^ 2 = t₁ * t₂ := by
      rw [hcomm.mul_pow, inv_pow, hs₁, hs₂, ht1i]
    rcases Width.sq_F hD hz hF with h | h
    · exact n3 (hsq ▸ h)
    · exact nz3 (hsq ▸ h)
  · have hm : ((Y₁ : G) * Y₂) ^ 2 = t₁ * t₂ := by
      rw [k12.mul_pow, hs₁, hs₂]
    have hcm : Commute (Y₃ : G) ((Y₁ : G) * Y₂)⁻¹ :=
      (k13.symm.mul_right k23.symm).inv_right
    have hcW : (Y₃ : G) * ((Y₁ : G) * Y₂)⁻¹ ∈ WT T z :=
      (WT T z).mul_mem hW₃ ((WT T z).inv_mem ((WT T z).mul_mem hW₁ hW₂))
    have hc2 : ((Y₃ : G) * ((Y₁ : G) * Y₂)⁻¹) * ((Y₃ : G) * ((Y₁ : G) * Y₂)⁻¹) = 1 := by
      rw [← pow_two, hcm.mul_pow, inv_pow, hs₃, hm]
      exact mul_inv_cancel _
    have hcV := mem_V_of_sq_eq_one hD hz hF2 hV hcW hc2
    have hcF : (Y₃ : G) * ((Y₁ : G) * Y₂)⁻¹ ∈ Fz z := hV.le_F hcV
    have h1 : qmk z (Y₃ * (Y₁ * Y₂)⁻¹) = 1 := (qmk_eq_one_iff z _).mpr (by simpa using hcF)
    rw [map_mul, map_inv, map_mul, mul_inv_eq_one] at h1
    rw [e3, e1, e2, h1]

end Klein

end PartC

end CFSG.GF2Type.Aschbacher1976Full.HS
