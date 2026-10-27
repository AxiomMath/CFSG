module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvBasic

public section

namespace CFSG.ComponentClassification.RankTwoBender

open Subgroup CFSG.Open CFSG.ComponentClassification.AschbacherToolkit
open CFSG.ComponentClassification.AschbacherToolkit.Bender

variable {M : Type*} [Group M]

theorem mulAut_mul_conj (α : MulAut M) (x : M) :
    α * MulAut.conj x = MulAut.conj (α x) * α := by
  ext y
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem conj_smul_eq_iff {p : ℕ} {S : Sylow p M} {x : M} :
    MulAut.conj x • S = S ↔ x ∈ normalizer ((S : Subgroup M) : Set M) := by
  rw [← Sylow.smul_def]
  exact Sylow.smul_eq_iff_mem_normalizer

theorem isPGroup_zpowers_of_mul_self (γ : MulAut M) (hγ : γ * γ = 1) :
    IsPGroup 2 (zpowers γ) := by
  have h2 : orderOf γ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, hγ])
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

theorem mem_normalizer_zpowers_of_commute {G : Type*} [Group G] {α β : G}
    (h : β * α = α * β) : β ∈ normalizer ((zpowers α : Subgroup G) : Set G) := by
  have hc : ∀ x ∈ zpowers α, β * x * β⁻¹ = x := by
    intro x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    rw [mul_inv_eq_iff_eq_mul]
    exact ((Commute.zpow_right (show Commute β α from h) k).eq)
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => (hc x hx).symm ▸ hx, fun hx => ?_⟩
  have h1 := hc _ hx
  have : x = β * x * β⁻¹ := by
    calc x = β⁻¹ * (β * x * β⁻¹) * β := by group
      _ = β⁻¹ * (β * (β * x * β⁻¹) * β⁻¹) * β := by rw [h1]
      _ = β * x * β⁻¹ := by group
  exact this ▸ hx

theorem exists_common_fixed_sylow [Finite M] (α β : MulAut M) (hα : α * α = 1) (hβ : β * β = 1)
    (hαβ : α * β = β * α) : ∃ S : Sylow 2 M, α • S = S ∧ β • S = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE : IsPGroup 2 (zpowers β ⊔ zpowers α : Subgroup (MulAut M)) :=
    IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_mul_self β hβ)
      (isPGroup_zpowers_of_mul_self α hα)
      (zpowers_le.mpr (mem_normalizer_zpowers_of_commute hαβ.symm))
  have hnd : ¬ 2 ∣ Nat.card (Sylow 2 M) := by
    intro h
    have := (card_sylow_modEq_one 2 M).symm.dvd
    omega
  obtain ⟨S, hS⟩ := hE.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 M) hnd
  exact ⟨S, hS ⟨α, le_sup_right (α := Subgroup (MulAut M)) (mem_zpowers α)⟩,
    hS ⟨β, le_sup_left (α := Subgroup (MulAut M)) (mem_zpowers β)⟩⟩

variable [Finite M]

theorem mul_self_adjust {R R₀ : Sylow 2 M}
    (hSE : fusionStronglyEmbedded (normalizer ((R : Subgroup M) : Set M))) (hne : R₀ ≠ R)
    {γ : MulAut M} (hγ : γ * γ = 1) (hγR : γ • R = R) {r : M} (hr : r ∈ (R : Subgroup M))
    (hR₀ : ((MulAut.conj r)⁻¹ * γ) • R₀ = R₀) :
    ((MulAut.conj r)⁻¹ * γ) * ((MulAut.conj r)⁻¹ * γ) = 1 := by
  have hsq : ((MulAut.conj r)⁻¹ * γ) * ((MulAut.conj r)⁻¹ * γ) =
      MulAut.conj (r⁻¹ * γ r⁻¹) := by
    rw [← map_inv, mul_assoc, ← mul_assoc γ, mulAut_mul_conj, mul_assoc, hγ, mul_one, ← map_mul]
  have hs : r⁻¹ * γ r⁻¹ ∈ (R : Subgroup M) :=
    (R : Subgroup M).mul_mem ((R : Subgroup M).inv_mem hr)
      (InvInner.apply_mem_of_smul_eq hγR ((R : Subgroup M).inv_mem hr))
  have hsN : r⁻¹ * γ r⁻¹ ∈ normalizer ((R₀ : Subgroup M) : Set M) := by
    rw [← conj_smul_eq_iff, ← hsq, mul_smul, hR₀, hR₀]
  rw [hsq, Omega.eq_one_of_mem_normalizer hSE hne hs hsN, map_one]

omit [Finite M] in
theorem adjust_smul_self {R : Sylow 2 M} {γ : MulAut M} (hγR : γ • R = R) {r : M}
    (hr : r ∈ (R : Subgroup M)) : ((MulAut.conj r)⁻¹ * γ) • R = R := by
  rw [mul_smul, hγR, ← map_inv, conj_smul_eq_iff]
  exact le_normalizer ((R : Subgroup M).inv_mem hr)

theorem exists_inner_of_commute_of_form [IsSimpleGroup M] {R R₀ : Sylow 2 M}
    (hSE : fusionStronglyEmbedded (normalizer ((R : Subgroup M) : Set M)))
    (hcard : Nat.card (Sylow 2 M) = Nat.card (R : Subgroup M) + 1) (hne : R₀ ≠ R)
    (Q : MulAut M → Prop)
    (h1 : ∀ γ : MulAut M, γ * γ = 1 → γ • R = R → γ • R₀ = R₀ → γ = 1 ∨ Q γ)
    (h2 : ∀ γ₁ γ₂ : MulAut M, γ₁ * γ₁ = 1 → γ₂ * γ₂ = 1 → γ₁ • R = R → γ₁ • R₀ = R₀ →
      γ₂ • R = R → γ₂ • R₀ = R₀ → Q γ₁ → Q γ₂ → ¬ Q (γ₁ * γ₂))
    (α β : MulAut M) (hα : α * α = 1) (hβ : β * β = 1) (hαβ : α * β = β * α) :
    (∃ y, α = MulAut.conj y) ∨ (∃ y, β = MulAut.conj y) ∨ ∃ y, α * β = MulAut.conj y := by
  obtain ⟨S, hαS, hβS⟩ := exists_common_fixed_sylow α β hα hβ hαβ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M S R
  set c := MulAut.conj g with hc
  have hcS : c • S = R := by rw [hc, ← Sylow.smul_def, hg]
  have hcR : c⁻¹ • R = S := by rw [← hcS, inv_smul_smul]
  set α₁ := c * α * c⁻¹ with hα₁
  set β₁ := c * β * c⁻¹ with hβ₁
  have hα₁R : α₁ • R = R := by rw [hα₁, mul_smul, mul_smul, hcR, hαS, hcS]
  have hβ₁R : β₁ • R = R := by rw [hβ₁, mul_smul, mul_smul, hcR, hβS, hcS]
  have hα₁β₁R : (α₁ * β₁) • R = R := by rw [mul_smul, hβ₁R, hα₁R]
  have hα₁2 : α₁ * α₁ = 1 := by
    rw [hα₁, show c * α * c⁻¹ * (c * α * c⁻¹) = c * (α * α) * c⁻¹ by group, hα, mul_one,
      mul_inv_cancel]
  have hβ₁2 : β₁ * β₁ = 1 := by
    rw [hβ₁, show c * β * c⁻¹ * (c * β * c⁻¹) = c * (β * β) * c⁻¹ by group, hβ, mul_one,
      mul_inv_cancel]
  have hα₁β₁2 : α₁ * β₁ * (α₁ * β₁) = 1 := by
    rw [hα₁, hβ₁, show c * α * c⁻¹ * (c * β * c⁻¹) * (c * α * c⁻¹ * (c * β * c⁻¹)) =
      c * (α * β * (α * β)) * c⁻¹ by group, show α * β * (α * β) = α * (β * α) * β by group,
      ← hαβ, show α * (α * β) * β = (α * α) * (β * β) by group, hα, hβ, mul_one, mul_one,
      mul_inv_cancel]
  have hinner : ∀ γ : MulAut M, (∃ y, c * γ * c⁻¹ = MulAut.conj y) → ∃ y, γ = MulAut.conj y := by
    rintro γ ⟨y, hy⟩
    refine ⟨g⁻¹ * y * g, ?_⟩
    rw [map_mul, map_mul, map_inv, ← hc, ← hy]
    group
  obtain ⟨r, hr, hrR₀⟩ := Omega.exists_conj_adjust hSE hcard hne α₁ hα₁R
  obtain ⟨s, hs, hsR₀⟩ := Omega.exists_conj_adjust hSE hcard hne β₁ hβ₁R
  set α₂ := (MulAut.conj r)⁻¹ * α₁ with hα₂
  set β₂ := (MulAut.conj s)⁻¹ * β₁ with hβ₂
  have hα₂2 := mul_self_adjust hSE hne hα₁2 hα₁R hr hrR₀
  have hβ₂2 := mul_self_adjust hSE hne hβ₁2 hβ₁R hs hsR₀
  have hα₂R := adjust_smul_self hα₁R hr
  have hβ₂R := adjust_smul_self hβ₁R hs
  set t := (r⁻¹ * α₁ s⁻¹)⁻¹ with ht
  have hprod : α₂ * β₂ = (MulAut.conj t)⁻¹ * (α₁ * β₁) := by
    calc α₂ * β₂ = MulAut.conj r⁻¹ * (α₁ * MulAut.conj s⁻¹) * β₁ := by
          rw [hα₂, hβ₂, map_inv, map_inv]
          group
      _ = MulAut.conj r⁻¹ * (MulAut.conj (α₁ s⁻¹) * α₁) * β₁ := by rw [mulAut_mul_conj]
      _ = MulAut.conj (r⁻¹ * α₁ s⁻¹) * (α₁ * β₁) := by
          rw [map_mul]
          group
      _ = (MulAut.conj t)⁻¹ * (α₁ * β₁) := by rw [← map_inv MulAut.conj t, ht, inv_inv]
  have ht' : t ∈ (R : Subgroup M) :=
    (R : Subgroup M).inv_mem ((R : Subgroup M).mul_mem ((R : Subgroup M).inv_mem hr)
      (InvInner.apply_mem_of_smul_eq hα₁R ((R : Subgroup M).inv_mem hs)))
  have hprodR₀ : ((MulAut.conj t)⁻¹ * (α₁ * β₁)) • R₀ = R₀ := by
    rw [← hprod, mul_smul, hsR₀, hrR₀]
  have hprod2 : α₂ * β₂ * (α₂ * β₂) = 1 := by
    rw [hprod]
    exact mul_self_adjust hSE hne hα₁β₁2 hα₁β₁R ht' hprodR₀
  have hprodR : (α₂ * β₂) • R = R := by rw [mul_smul, hβ₂R, hα₂R]
  have hprodR₀' : (α₂ * β₂) • R₀ = R₀ := by rw [mul_smul, hsR₀, hrR₀]
  by_contra hcon
  simp only [not_or, not_exists] at hcon
  obtain ⟨hna, hnb, hnab⟩ := hcon
  have hα₂1 : α₂ ≠ 1 := by
    intro h
    obtain ⟨y, hy⟩ := hinner α ⟨r, by rw [← hα₁, ← inv_mul_eq_one.mp h]⟩
    exact hna y hy
  have hβ₂1 : β₂ ≠ 1 := by
    intro h
    obtain ⟨y, hy⟩ := hinner β ⟨s, by rw [← hβ₁, ← inv_mul_eq_one.mp h]⟩
    exact hnb y hy
  have hprod1 : α₂ * β₂ ≠ 1 := by
    intro h
    rw [hprod] at h
    obtain ⟨y, hy⟩ := hinner (α * β) ⟨t, by
      rw [show c * (α * β) * c⁻¹ = α₁ * β₁ by rw [hα₁, hβ₁]; group, ← inv_mul_eq_one.mp h]⟩
    exact hnab y hy
  have hQa := (h1 α₂ hα₂2 hα₂R hrR₀).resolve_left hα₂1
  have hQb := (h1 β₂ hβ₂2 hβ₂R hsR₀).resolve_left hβ₂1
  have hQab := (h1 (α₂ * β₂) hprod2 hprodR hprodR₀').resolve_left hprod1
  exact h2 α₂ β₂ hα₂2 hβ₂2 hα₂R hrR₀ hβ₂R hsR₀ hQa hQb hQab

omit [Finite M] in
@[expose] def E4Inner (X : Type*) [Group X] : Prop :=
  ∀ α β : MulAut X, α * α = 1 → β * β = 1 → α * β = β * α →
    (∃ y, α = MulAut.conj y) ∨ (∃ y, β = MulAut.conj y) ∨ ∃ y, α * β = MulAut.conj y

omit [Finite M] in
theorem E4Inner.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (h : E4Inner Y) :
    E4Inner X := by
  intro α β hα hβ hαβ
  have hinner : ∀ γ : MulAut X, (∃ y, MulAut.congr e γ = MulAut.conj y) →
      ∃ y, γ = MulAut.conj y := by
    rintro γ ⟨y, hy⟩
    refine ⟨e.symm y, (MulAut.congr e).injective ?_⟩
    rw [hy, AutTransport.congr_conj, MulEquiv.apply_symm_apply]
  have h' := h (MulAut.congr e α) (MulAut.congr e β) (by rw [← map_mul, hα, map_one])
    (by rw [← map_mul, hβ, map_one]) (by rw [← map_mul, hαβ, map_mul])
  rcases h' with ha | hb | hab
  · exact Or.inl (hinner α ha)
  · exact Or.inr (Or.inl (hinner β hb))
  · exact Or.inr (Or.inr (hinner (α * β) (by rwa [map_mul])))

end CFSG.ComponentClassification.RankTwoBender
