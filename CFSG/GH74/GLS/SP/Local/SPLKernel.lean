module

public import CFSG.LieType.CurtisTits.Recognition

public section

namespace CFSG.GH74.GLS.SP.Local

section KernelModY

variable {G : Type} [Group G]

@[expose] def kernelModY (K R Y : Subgroup G) (hKR : ∀ k ∈ K, ∀ r ∈ R, k * r * k⁻¹ ∈ R)
    (hKY : ∀ k ∈ K, ∀ y ∈ Y, k * y * k⁻¹ ∈ Y) : Subgroup ↥K where
  carrier := {k | ∀ r ∈ R, (k : G) * r * (k : G)⁻¹ * r⁻¹ ∈ Y}
  mul_mem' := by
    intro a b ha hb r hr
    have h1 := hKY a a.2 _ (hb r hr)
    have h3 := Y.mul_mem h1 (ha r hr)
    have e : ((a * b : ↥K) : G) * r * ((a * b : ↥K) : G)⁻¹ * r⁻¹ =
        ((a : G) * ((b : G) * r * (b : G)⁻¹ * r⁻¹) * (a : G)⁻¹) *
          ((a : G) * r * (a : G)⁻¹ * r⁻¹) := by
      simp only [Subgroup.coe_mul]; group
    rw [e]; exact h3
  one_mem' := by
    intro r hr
    simp
  inv_mem' := by
    intro a ha r hr
    have hr' : (a : G)⁻¹ * r * (a : G) ∈ R := by
      have := hKR _ (K.inv_mem a.2) r hr
      rwa [inv_inv] at this
    have h := Y.inv_mem (ha _ hr')
    have e : ((a⁻¹ : ↥K) : G) * r * ((a⁻¹ : ↥K) : G)⁻¹ * r⁻¹ =
        ((a : G) * ((a : G)⁻¹ * r * (a : G)) * (a : G)⁻¹ * ((a : G)⁻¹ * r * (a : G))⁻¹)⁻¹ := by
      simp only [Subgroup.coe_inv]; group
    rw [e]; exact h

theorem kernelModY_normal (K R Y : Subgroup G) (hKR : ∀ k ∈ K, ∀ r ∈ R, k * r * k⁻¹ ∈ R)
    (hKY : ∀ k ∈ K, ∀ y ∈ Y, k * y * k⁻¹ ∈ Y) : (kernelModY K R Y hKR hKY).Normal where
  conj_mem := by
    intro n hn g r hr
    have hr' : (g : G)⁻¹ * r * (g : G) ∈ R := by
      have := hKR _ (K.inv_mem g.2) r hr
      rwa [inv_inv] at this
    have h2 := hKY g g.2 _ (hn _ hr')
    have e : ((g * n * g⁻¹ : ↥K) : G) * r * ((g * n * g⁻¹ : ↥K) : G)⁻¹ * r⁻¹ =
        (g : G) * ((n : G) * ((g : G)⁻¹ * r * (g : G)) * (n : G)⁻¹ *
          ((g : G)⁻¹ * r * (g : G))⁻¹) * (g : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [e]; exact h2

end KernelModY

theorem kernel_mem_zpowers_of_quasisimple {G : Type} [Group G] (K R Y : Subgroup G) (z : G)
    (hK : CFSG.IsQuasisimple ↥K)
    (hcen : (Subgroup.center ↥K).map K.subtype = Subgroup.zpowers z)
    (hKR : ∀ k ∈ K, ∀ r ∈ R, k * r * k⁻¹ ∈ R)
    (hKY : ∀ k ∈ K, ∀ y ∈ Y, k * y * k⁻¹ ∈ Y)
    (hzK : z ∈ K)
    (hz : ∃ r ∈ R, z * r * z⁻¹ * r⁻¹ ∉ Y)
    {k : G} (hk : k ∈ K) (hkr : ∀ r ∈ R, k * r * k⁻¹ * r⁻¹ ∈ Y) :
    k ∈ Subgroup.zpowers z := by
  have := kernelModY_normal K R Y hKR hKY
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hK
      (kernelModY K R Y hKR hKY) with hle | htop
  · rw [← hcen]
    exact ⟨⟨k, hk⟩, hle hkr, rfl⟩
  · exfalso
    obtain ⟨r, hr, hzr⟩ := hz
    have hzN : (⟨z, hzK⟩ : ↥K) ∈ kernelModY K R Y hKR hKY := by
      rw [htop]; trivial
    exact hzr (hzN r hr)

theorem kernel_eq_one_of_quasisimple {G : Type} [Group G] (K R Y : Subgroup G) (z : G)
    (hK : CFSG.IsQuasisimple ↥K)
    (hcen : (Subgroup.center ↥K).map K.subtype = Subgroup.zpowers z)
    (hz2 : z * z = 1)
    (hKR : ∀ k ∈ K, ∀ r ∈ R, k * r * k⁻¹ ∈ R)
    (hKY : ∀ k ∈ K, ∀ y ∈ Y, k * y * k⁻¹ ∈ Y)
    (hzK : z ∈ K)
    (hz : ∃ r ∈ R, z * r * z⁻¹ * r⁻¹ ∉ Y)
    {k : G} (hk : k ∈ K) (hkr : ∀ r ∈ R, k * r * k⁻¹ * r⁻¹ ∈ Y) : k = 1 := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp
    (kernel_mem_zpowers_of_quasisimple K R Y z hK hcen hKR hKY hzK hz hk hkr)
  have hsq : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz2
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
  · rw [← hn, zpow_mul, hsq, one_zpow]
  · exfalso
    obtain ⟨r, hr, hzr⟩ := hz
    have hkz : k = z := by
      rw [← hn, zpow_add_one, zpow_mul, hsq, one_zpow, one_mul]
    subst hkz
    exact hzr (hkr r hr)

end CFSG.GH74.GLS.SP.Local
