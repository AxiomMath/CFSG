module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Tactic.Group

public section

namespace CFSG.HardMathSupport.Lang.TwE6Step3

variable {G : Type*} [Group G]

theorem exists_fixed_split (θ : G →* G) {H Q : Subgroup G}
    (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hHQ : H ≤ Subgroup.normalizer (Q : Set G))
    (hθH : ∀ h ∈ H, θ h ∈ H) (hθQ : ∀ g ∈ Q, θ g ∈ Q)
    (hlang : ∀ s ∈ H ⊓ Q, ∃ t ∈ H ⊓ Q, t⁻¹ * θ t = s)
    {m : G} (hm : m ∈ H ⊔ Q) (hθm : θ m = m) :
    ∃ t ∈ H, θ t = t ∧ ∃ g ∈ Q, θ g = g ∧ m = t * g := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hHQ] at hm
  obtain ⟨h, hh, g, hg, rfl⟩ := hm
  set s := h⁻¹ * θ h with hsdef
  have hs : s = g * (θ g)⁻¹ := by
    have h1 : θ h * θ g = h * g := by rw [← map_mul, hθm]
    calc s = h⁻¹ * (θ h * θ g) * (θ g)⁻¹ := by rw [hsdef]; group
      _ = h⁻¹ * (h * g) * (θ g)⁻¹ := by rw [h1]
      _ = g * (θ g)⁻¹ := by group
  have hsH : s ∈ H := mul_mem (inv_mem hh) (hθH h hh)
  have hsQ : s ∈ Q := by rw [hs]; exact mul_mem hg (inv_mem (hθQ g hg))
  obtain ⟨t₁, ht₁HQ, ht₁⟩ := hlang s⁻¹ (Subgroup.mem_inf.2 ⟨inv_mem hsH, inv_mem hsQ⟩)
  obtain ⟨ht₁H, ht₁Q⟩ := Subgroup.mem_inf.1 ht₁HQ
  have hθh : θ h = h * s := by rw [hsdef]; group
  have hθt : θ t₁ = t₁ * s⁻¹ := by
    calc θ t₁ = t₁ * (t₁⁻¹ * θ t₁) := by group
      _ = t₁ * s⁻¹ := by rw [ht₁]
  have hst : s * t₁ = t₁ * s := hH s hsH t₁ ht₁H
  have hfix : θ (h * t₁) = h * t₁ := by
    calc θ (h * t₁) = h * s * (t₁ * s⁻¹) := by rw [map_mul, hθh, hθt]
      _ = h * (s * t₁) * s⁻¹ := by group
      _ = h * (t₁ * s) * s⁻¹ := by rw [hst]
      _ = h * t₁ := by group
  refine ⟨h * t₁, mul_mem hh ht₁H, hfix, t₁⁻¹ * g, mul_mem (inv_mem ht₁Q) hg, ?_, by group⟩
  have hm' : t₁⁻¹ * g = (h * t₁)⁻¹ * (h * g) := by group
  rw [hm', map_mul, map_inv, hfix, hθm]

theorem le_normalizer_of_commute {P Q : Subgroup G} (h : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a) :
    P ≤ Subgroup.normalizer (Q : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    have hab : a * b * a⁻¹ = b := by rw [h a ha b hb, mul_inv_cancel_right]
    rw [hab]
    exact hb
  · intro hb
    have hc : a⁻¹ * (a * b * a⁻¹) * a = a * b * a⁻¹ := by
      rw [h a⁻¹ (inv_mem ha) _ hb, inv_mul_cancel_right]
    have hb' : b = a⁻¹ * (a * b * a⁻¹) * a := by group
    rw [hb', hc]
    exact hb

theorem le_normalizer_sup_of_commute {H Q₁ Q₂ : Subgroup G}
    (hHQ₁ : H ≤ Subgroup.normalizer (Q₁ : Set G)) (hHQ₂ : H ≤ Subgroup.normalizer (Q₂ : Set G))
    (hQ : ∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a) :
    H ≤ Subgroup.normalizer ((Q₁ ⊔ Q₂ : Subgroup G) : Set G) := by
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right Q₁ Q₂ (le_normalizer_of_commute hQ)
  intro x hx
  have h₁ := Subgroup.mem_normalizer_iff.1 (hHQ₁ hx)
  have h₂ := Subgroup.mem_normalizer_iff.1 (hHQ₂ hx)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [← SetLike.mem_coe, ← SetLike.mem_coe, hcoe]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨x * a * x⁻¹, (h₁ a).1 ha, x * b * x⁻¹, (h₂ b).1 hb, by group⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    refine ⟨x⁻¹ * a * x, ?_, x⁻¹ * b * x, ?_, ?_⟩
    · exact (h₁ _).2 (by simpa [mul_assoc] using ha)
    · exact (h₂ _).2 (by simpa [mul_assoc] using hb)
    · have hy : y = x⁻¹ * (x * y * x⁻¹) * x := by group
      rw [hy, ← hab]
      group

theorem exists_fixed_split₂ (θ : G →* G) {H Q₁ Q₂ : Subgroup G}
    (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hHQ₁ : H ≤ Subgroup.normalizer (Q₁ : Set G)) (hHQ₂ : H ≤ Subgroup.normalizer (Q₂ : Set G))
    (hQ : ∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a)
    (hθH : ∀ h ∈ H, θ h ∈ H) (hθQ₁ : ∀ g ∈ Q₁, θ g ∈ Q₁) (hθQ₂ : ∀ g ∈ Q₂, θ g ∈ Q₂)
    (hQ₁₂ : Q₁ ⊓ Q₂ ≤ H) (hHQ12 : H ⊓ (Q₁ ⊔ Q₂) ≤ (H ⊓ Q₁) ⊔ (H ⊓ Q₂))
    (hlang₁ : ∀ s ∈ H ⊓ Q₁, ∃ t ∈ H ⊓ Q₁, t⁻¹ * θ t = s)
    (hlang₂ : ∀ s ∈ H ⊓ Q₂, ∃ t ∈ H ⊓ Q₂, t⁻¹ * θ t = s)
    {m : G} (hm : m ∈ H ⊔ (Q₁ ⊔ Q₂)) (hθm : θ m = m) :
    ∃ t ∈ H, θ t = t ∧ ∃ g₁ ∈ Q₁, θ g₁ = g₁ ∧ ∃ g₂ ∈ Q₂, θ g₂ = g₂ ∧ m = t * g₁ * g₂ := by
  have hQ₁₂n := le_normalizer_of_commute hQ
  have hθsup : ∀ g ∈ Q₁ ⊔ Q₂, θ g ∈ Q₁ ⊔ Q₂ := by
    intro g hg
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right Q₁ Q₂ hQ₁₂n] at hg ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := hg
    exact ⟨θ a, hθQ₁ a ha, θ b, hθQ₂ b hb, (map_mul θ a b).symm⟩
  have hlang : ∀ s ∈ H ⊓ (Q₁ ⊔ Q₂), ∃ t ∈ H ⊓ (Q₁ ⊔ Q₂), t⁻¹ * θ t = s := by
    intro s hs
    have hs' := hHQ12 hs
    have hnorm : H ⊓ Q₁ ≤ Subgroup.normalizer ((H ⊓ Q₂ : Subgroup G) : Set G) :=
      le_normalizer_of_commute fun a ha b hb =>
        hH a (Subgroup.mem_inf.1 ha).1 b (Subgroup.mem_inf.1 hb).1
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at hs'
    obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := hs'
    obtain ⟨t₁, ht₁, ht₁e⟩ := hlang₁ s₁ hs₁
    obtain ⟨t₂, ht₂, ht₂e⟩ := hlang₂ s₂ hs₂
    obtain ⟨ht₁H, ht₁Q⟩ := Subgroup.mem_inf.1 ht₁
    obtain ⟨ht₂H, ht₂Q⟩ := Subgroup.mem_inf.1 ht₂
    refine ⟨t₁ * t₂, Subgroup.mem_inf.2 ⟨mul_mem ht₁H ht₂H,
      mul_mem (Subgroup.mem_sup_left ht₁Q) (Subgroup.mem_sup_right ht₂Q)⟩, ?_⟩
    have hc : t₁⁻¹ * θ t₁ * t₂ = t₂ * (t₁⁻¹ * θ t₁) :=
      hH _ (mul_mem (inv_mem ht₁H) (hθH t₁ ht₁H)) _ ht₂H
    calc (t₁ * t₂)⁻¹ * θ (t₁ * t₂) = t₂⁻¹ * (t₁⁻¹ * θ t₁ * t₂) * (t₂⁻¹ * θ t₂) := by
          rw [map_mul]; group
      _ = t₂⁻¹ * (t₂ * (t₁⁻¹ * θ t₁)) * (t₂⁻¹ * θ t₂) := by rw [hc]
      _ = (t₁⁻¹ * θ t₁) * (t₂⁻¹ * θ t₂) := by group
      _ = s₁ * s₂ := by rw [ht₁e, ht₂e]
  obtain ⟨t, htH, htθ, g, hg, hgθ, rfl⟩ := exists_fixed_split θ hH
    (le_normalizer_sup_of_commute hHQ₁ hHQ₂ hQ) hθH hθsup hlang hm hθm
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right Q₁ Q₂ hQ₁₂n] at hg
  obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hg
  set z := g₁⁻¹ * θ g₁ with hzdef
  have hz₂ : z = g₂ * (θ g₂)⁻¹ := by
    have h1 : θ g₁ * θ g₂ = g₁ * g₂ := by rw [← map_mul, hgθ]
    calc z = g₁⁻¹ * (θ g₁ * θ g₂) * (θ g₂)⁻¹ := by rw [hzdef]; group
      _ = g₁⁻¹ * (g₁ * g₂) * (θ g₂)⁻¹ := by rw [h1]
      _ = g₂ * (θ g₂)⁻¹ := by group
  have hzQ₁ : z ∈ Q₁ := mul_mem (inv_mem hg₁) (hθQ₁ g₁ hg₁)
  have hzQ₂ : z ∈ Q₂ := by rw [hz₂]; exact mul_mem hg₂ (inv_mem (hθQ₂ g₂ hg₂))
  have hzH : z ∈ H := hQ₁₂ (Subgroup.mem_inf.2 ⟨hzQ₁, hzQ₂⟩)
  obtain ⟨s₁, hs₁, hs₁e⟩ := hlang₁ z⁻¹ (Subgroup.mem_inf.2 ⟨inv_mem hzH, inv_mem hzQ₁⟩)
  obtain ⟨s₂, hs₂, hs₂e⟩ := hlang₂ z (Subgroup.mem_inf.2 ⟨hzH, hzQ₂⟩)
  obtain ⟨hs₁H, hs₁Q⟩ := Subgroup.mem_inf.1 hs₁
  obtain ⟨hs₂H, hs₂Q⟩ := Subgroup.mem_inf.1 hs₂
  have hθg₁ : θ g₁ = g₁ * z := by rw [hzdef]; group
  have hθg₂ : θ g₂ = z⁻¹ * g₂ := by rw [hz₂]; group
  have hθs₁ : θ s₁ = s₁ * z⁻¹ := by
    calc θ s₁ = s₁ * (s₁⁻¹ * θ s₁) := by group
      _ = s₁ * z⁻¹ := by rw [hs₁e]
  have hθs₂ : θ s₂ = s₂ * z := by
    calc θ s₂ = s₂ * (s₂⁻¹ * θ s₂) := by group
      _ = s₂ * z := by rw [hs₂e]
  have hzs₁ : z * s₁ = s₁ * z := hH z hzH s₁ hs₁H
  have hzs₁' : z * s₁⁻¹ = s₁⁻¹ * z := (Commute.inv_right (hzs₁ : Commute z s₁)).eq
  obtain ⟨u, hu⟩ : ∃ u : G, u = s₁⁻¹ * s₂⁻¹ := ⟨_, rfl⟩
  have huH : u ∈ H := by rw [hu]; exact mul_mem (inv_mem hs₁H) (inv_mem hs₂H)
  have hθu : θ u = u := by
    rw [hu, map_mul, map_inv, map_inv, hθs₁, hθs₂]
    calc (s₁ * z⁻¹)⁻¹ * (s₂ * z)⁻¹ = z * s₁⁻¹ * z⁻¹ * s₂⁻¹ := by group
      _ = s₁⁻¹ * z * z⁻¹ * s₂⁻¹ := by rw [hzs₁']
      _ = s₁⁻¹ * s₂⁻¹ := by group
  obtain ⟨b₁, hb₁⟩ : ∃ b₁ : G, b₁ = g₁ * s₁ := ⟨_, rfl⟩
  have hb₁Q : b₁ ∈ Q₁ := by rw [hb₁]; exact mul_mem hg₁ hs₁Q
  have hθb₁ : θ b₁ = b₁ := by
    rw [hb₁, map_mul, hθg₁, hθs₁]
    calc g₁ * z * (s₁ * z⁻¹) = g₁ * (z * s₁) * z⁻¹ := by group
      _ = g₁ * (s₁ * z) * z⁻¹ := by rw [hzs₁]
      _ = g₁ * s₁ := by group
  have hθb₂ : θ (s₂ * g₂) = s₂ * g₂ := by
    rw [map_mul, hθs₂, hθg₂]
    group
  have hu₁ : u⁻¹ * b₁ * u⁻¹⁻¹ ∈ Q₁ :=
    (Subgroup.mem_normalizer_iff.1 (hHQ₁ (inv_mem huH)) b₁).1 hb₁Q
  have hθu₁ : θ (u⁻¹ * b₁ * u⁻¹⁻¹) = u⁻¹ * b₁ * u⁻¹⁻¹ := by
    simp only [map_mul, map_inv, hθu, hθb₁]
  refine ⟨t * u, mul_mem htH huH, by rw [map_mul, htθ, hθu], u⁻¹ * b₁ * u⁻¹⁻¹, hu₁, hθu₁,
    s₂ * g₂, mul_mem hs₂Q hg₂, hθb₂, ?_⟩
  rw [hu, hb₁]
  group

end CFSG.HardMathSupport.Lang.TwE6Step3
