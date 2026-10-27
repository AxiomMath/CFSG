module

public import CFSG.ClassicalInvolution.Asc77.AscE189Model
public import CFSG.ClassicalInvolution.Asc77.AscSixBasic

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

variable {X : Type} [Group X]

@[expose] def E189StdSwap (𝓕 : Set (Subgroup X)) : Prop :=
  ∀ F₁ ∈ 𝓕, ∀ z₁ : X, IsUniqueInvolution F₁ z₁ → ∀ ζ ∈ Subgroup.center X, ζ ≠ 1 →
    ζ * ζ = 1 → ∀ a : X, a * a = ζ → a * z₁ * a⁻¹ = ζ * z₁ →
      ∃ y α β : X, α ∈ F₁ ∧ β ∈ conjSub a F₁ ∧ α ^ 4 = 1 ∧ β ^ 4 = 1 ∧ y * a * y⁻¹ = α * β

theorem isPGroup_zpowers_of_pow_four {α : X} (h : α ^ 4 = 1) :
    IsPGroup 2 (Subgroup.zpowers α) := by
  have hdvd : orderOf α ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using h)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hcard : Nat.card (Subgroup.zpowers α) = 2 ^ k := by
    rw [Nat.card_zpowers, hk]
  exact IsPGroup.of_card hcard

theorem commutator_eq_of_involutions {z t : X} (hz : z * z = 1) (ht : t * t = 1) :
    ⁅z, t⁆ = z * t * z * t := by
  rw [commutatorElement_def, inv_eq_of_mul_eq_one_right hz, inv_eq_of_mul_eq_one_right ht]

theorem e189AtFam_of_std [Finite X] {𝓕 : Set (Subgroup X)}
    (hconj : ∀ F ∈ 𝓕, ∀ y : X, conjSub y F ∈ 𝓕)
    (hC : ∀ F ∈ 𝓕, ∀ z : X, IsUniqueInvolution F z → ∀ c : X, c * z = z * c → conjSub c F = F)
    (hS : E189StdSwap 𝓕) : E189AtFam X 𝓕 := by
  rintro N hN F₁ hF₁ z₁ hz₁ g h1 h2 h3 h4 -
  set t : X := g * z₁ * g⁻¹ with ht_def
  have ht2 : t * t = 1 := by
    calc t * t = g * (z₁ * z₁) * g⁻¹ := by rw [ht_def]; group
      _ = 1 := by rw [hz₁.sq]; group
  have hz1inv : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right hz₁.sq
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hζdef : ⁅z₁, t⁆ = z₁ * t * z₁ * t := commutator_eq_of_involutions hz₁.sq ht2
  set ζ : X := z₁ * t * z₁ * t with hζ_def
  have hζN : ζ ∈ N := hζdef ▸ h1
  have hζc : ζ ∈ Subgroup.center X := hN hζN
  have hcen : ∀ x : X, x * ζ = ζ * x := fun x => Subgroup.mem_center_iff.mp hζc x
  have hζ2 : ζ * ζ = 1 := by
    have hinv : ζ⁻¹ = t * z₁ * t * z₁ := by
      rw [hζ_def]
      simp only [mul_inv_rev, hz1inv, htinv, mul_assoc]
    have hconj' : t * z₁ * t * z₁ = ζ := by
      calc t * z₁ * t * z₁ = (z₁ * z₁) * t * z₁ * t * z₁ := by rw [hz₁.sq, one_mul]
        _ = z₁ * ζ * z₁ := by rw [hζ_def]; group
        _ = ζ * z₁ * z₁ := by rw [hcen z₁]
        _ = ζ := by rw [mul_assoc, hz₁.sq, mul_one]
    exact mul_eq_one_iff_eq_inv.mpr (hinv.trans hconj').symm
  have hζ1 : ζ ≠ 1 := by
    intro h
    have e2 : z₁ * t * z₁ = t := by
      have := eq_inv_of_mul_eq_one_left h
      rwa [htinv] at this
    have hcomm : t * z₁ = z₁ * t := by
      calc t * z₁ = z₁ * (z₁ * t * z₁) := by
            rw [← mul_assoc, ← mul_assoc, hz₁.sq, one_mul]
        _ = z₁ * t := by rw [e2]
    exact h3 (hC F₁ hF₁ z₁ hz₁ t hcomm)
  obtain ⟨a, ha_def⟩ : ∃ a : X, a = z₁ * t := ⟨_, rfl⟩
  have h2' : a ∉ N := by rw [ha_def]; exact h2
  have ha2 : a * a = ζ := by rw [ha_def, hζ_def]; group
  have haz : a * z₁ * a⁻¹ = ζ * z₁ := by
    have : a⁻¹ = t * z₁ := by
      rw [ha_def, mul_inv_rev, hz1inv, htinv]
    rw [this, ha_def, hζ_def]
    group
  obtain ⟨y, α, β, hα, hβ, hα4, hβ4, hy⟩ := hS F₁ hF₁ z₁ hz₁ ζ hζc hζ1 hζ2 a ha2 haz
  have hconjF : conjSub a F₁ = conjSub t F₁ := by
    rw [ha_def, conjSub_mul]
    exact conjSub_eq_of_mem_of_commutes hz₁.mem h4
  rw [hconjF] at hβ
  obtain ⟨R₁, hR₁, hR₁α⟩ := IsSylow2In.exists_ge (isPGroup_zpowers_of_pow_four hα4)
    (Subgroup.zpowers_le.mpr hα)
  obtain ⟨R₃, hR₃, hR₃β⟩ := IsSylow2In.exists_ge (isPGroup_zpowers_of_pow_four hβ4)
    (Subgroup.zpowers_le.mpr hβ)
  left
  refine ⟨conjSub t F₁, hconj F₁ hF₁ t, h3, h4, ⟨t, rfl⟩, t * z₁ * t⁻¹, hz₁.conj t, ?_, R₁, R₃,
    hR₁, hR₃, α * β, y⁻¹, Subgroup.mul_mem_sup (hR₁α (Subgroup.mem_zpowers α))
      (hR₃β (Subgroup.mem_zpowers β)), ?_, ?_, ?_⟩
  · rw [hz1inv, htinv]
    have : z₁ * (t * z₁ * t) = ζ := by rw [hζ_def]; group
    rw [this]
    exact hζN
  · intro hu
    apply h2'
    rw [← hy] at hu
    have hcu := Subgroup.mem_center_iff.mp (hN hu) y⁻¹
    have hu' : y⁻¹ * (y * a * y⁻¹) * y = a := by group
    have hu'' : y⁻¹ * (y * a * y⁻¹) * y = y * a * y⁻¹ := by
      rw [hcu, mul_assoc, inv_mul_cancel, mul_one]
    rw [← hu', hu'']
    exact hu
  · rw [← hy]
    have : y * a * y⁻¹ * (y * a * y⁻¹) = y * ζ * y⁻¹ := by
      calc y * a * y⁻¹ * (y * a * y⁻¹) = y * (a * a) * y⁻¹ := by group
        _ = y * ζ * y⁻¹ := by rw [ha2]
    rw [this, hcen y, mul_assoc, mul_inv_cancel, mul_one]
    exact hζN
  · rw [← hy]
    have : y⁻¹ * (y * a * y⁻¹) * y⁻¹⁻¹ = a := by group
    rw [this]
    have h3' : a⁻¹ * (z₁ * t) = 1 := by rw [ha_def]; group
    rw [h3']
    exact N.one_mem

theorem e189StdSwap_of_conjClass {F0 : Subgroup X} {d : X} (hd : IsUniqueInvolution F0 d)
    (hstd : ∀ ζ ∈ Subgroup.center X, ζ ≠ 1 → ζ * ζ = 1 → ∀ a : X, a * a = ζ →
      a * d * a⁻¹ = ζ * d → ∃ y α β : X, α ∈ F0 ∧ β ∈ conjSub a F0 ∧ α ^ 4 = 1 ∧ β ^ 4 = 1 ∧
        y * a * y⁻¹ = α * β) :
    E189StdSwap {F | ∃ g : X, F = conjSub g F0} := by
  rintro F₁ ⟨g₀, rfl⟩ z₁ hz₁ ζ hζ hζ1 hζ2 a ha2 haz
  have hz1 : z₁ = g₀ * d * g₀⁻¹ := hz₁.eq (hd.conj g₀)
  have hζg : g₀⁻¹ * ζ * g₀ = ζ := by
    have := Subgroup.mem_center_iff.mp hζ g₀⁻¹
    calc g₀⁻¹ * ζ * g₀ = ζ * g₀⁻¹ * g₀ := by rw [this]
      _ = ζ := by group
  rw [hz1] at haz
  obtain ⟨y, α, β, hα, hβ, hα4, hβ4, hy⟩ := hstd ζ hζ hζ1 hζ2 (g₀⁻¹ * a * g₀)
    (by
      calc g₀⁻¹ * a * g₀ * (g₀⁻¹ * a * g₀) = g₀⁻¹ * (a * a) * g₀ := by group
        _ = ζ := by rw [ha2, hζg])
    (by
      calc g₀⁻¹ * a * g₀ * d * (g₀⁻¹ * a * g₀)⁻¹
          = g₀⁻¹ * (a * (g₀ * d * g₀⁻¹) * a⁻¹) * g₀ := by group
        _ = g₀⁻¹ * (ζ * (g₀ * d * g₀⁻¹)) * g₀ := by rw [haz]
        _ = (g₀⁻¹ * ζ * g₀) * d := by group
        _ = ζ * d := by rw [hζg])
  refine ⟨g₀ * y * g₀⁻¹, g₀ * α * g₀⁻¹, g₀ * β * g₀⁻¹, conj_mem_conjSub hα, ?_, ?_, ?_, ?_⟩
  · rw [mem_conjSub_iff, mem_conjSub_iff]
    rw [mem_conjSub_iff] at hβ
    convert hβ using 1
    group
  · rw [conj_pow, hα4]
    group
  · rw [conj_pow, hβ4]
    group
  · calc g₀ * y * g₀⁻¹ * a * (g₀ * y * g₀⁻¹)⁻¹ = g₀ * (y * (g₀⁻¹ * a * g₀) * y⁻¹) * g₀⁻¹ := by
          group
      _ = g₀ * (α * β) * g₀⁻¹ := by rw [hy]
      _ = g₀ * α * g₀⁻¹ * (g₀ * β * g₀⁻¹) := by group

theorem e189AtFam_of_conjClass [Finite X] {F0 : Subgroup X} {d : X}
    (hd : IsUniqueInvolution F0 d) (hC : ∀ c : X, c * d = d * c → conjSub c F0 = F0)
    (hstd : ∀ ζ ∈ Subgroup.center X, ζ ≠ 1 → ζ * ζ = 1 → ∀ a : X, a * a = ζ →
      a * d * a⁻¹ = ζ * d → ∃ y α β : X, α ∈ F0 ∧ β ∈ conjSub a F0 ∧ α ^ 4 = 1 ∧ β ^ 4 = 1 ∧
        y * a * y⁻¹ = α * β) :
    E189AtFam X {F | ∃ g : X, F = conjSub g F0} := by
  refine e189AtFam_of_std ?_ ?_ (e189StdSwap_of_conjClass hd hstd)
  · rintro F ⟨g, rfl⟩ y
    exact ⟨y * g, (conjSub_mul y g F0).symm⟩
  · rintro F ⟨g₀, rfl⟩ z hz c hc
    have hz' : z = g₀ * d * g₀⁻¹ := hz.eq (hd.conj g₀)
    have hc' : (g₀⁻¹ * c * g₀) * d = d * (g₀⁻¹ * c * g₀) := by
      rw [hz'] at hc
      calc g₀⁻¹ * c * g₀ * d = g₀⁻¹ * (c * (g₀ * d * g₀⁻¹)) * g₀ := by group
        _ = g₀⁻¹ * ((g₀ * d * g₀⁻¹) * c) * g₀ := by rw [hc]
        _ = d * (g₀⁻¹ * c * g₀) := by group
    have := hC _ hc'
    rw [← conjSub_mul, show c * g₀ = g₀ * (g₀⁻¹ * c * g₀) by group, conjSub_mul, this]


theorem isUniqueInvolution_of_isClassicalSL2 {F : Type} [Field F] [Finite F] {J : Subgroup X}
    {d : X} (h : CFSG.ClassicalInvolution.IsClassicalSL2 F J d) (hodd : Odd (Nat.card F)) :
    IsUniqueInvolution J d where
  mem := h.mem
  ne_one := fun h1 => by
    have := h.orderOf_eq_two
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  sq := by
    have := pow_orderOf_eq_one d
    rw [h.orderOf_eq_two] at this
    simpa [pow_two] using this
  unique := fun y hy hy2 => by
    by_cases h1 : y = 1
    · exact Or.inl h1
    · exact Or.inr (h.eq_of_orderOf_eq_two hodd hy
        (orderOf_eq_prime (by rw [pow_two]; exact hy2) h1))

theorem conjSub_eq_of_isClassicalSL2 {F : Type} [Field F] {J : Subgroup X} {d : X}
    (h : CFSG.ClassicalInvolution.IsClassicalSL2 F J d) {c : X} (hc : c * d = d * c) :
    conjSub c J = J :=
  conjSub_eq_of_mem_normalizer
    (h.centralizer_le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hc))

end CFSG.ClassicalInvolution.Asc77
