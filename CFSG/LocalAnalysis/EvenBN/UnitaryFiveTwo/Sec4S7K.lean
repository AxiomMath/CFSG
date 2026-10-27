module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7Mod2
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7I

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {d : Data G} {K₀ : Subgroup G}

section Defs



@[expose] noncomputable def Data.B₁ (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀) :
    Subgroup G :=
  (d.A₁.comap (Data.delta h hKU hf)).map (Data.Nn h hKU hf).subtype

@[expose] noncomputable def Data.ZQ (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀) :
    Subgroup G :=
  (d.ZX₄.comap (Data.delta h hKU hf)).map (Data.Nn h hKU hf).subtype


variable (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀)

include h hKU in
theorem Data.Hyp.mem_B₁_iff {x : G} :
    x ∈ Data.B₁ h hKU hf ↔ ∃ _ : x ∈ Data.Nn h hKU hf, x * (d.t * x * d.t) ∈ d.A₁ := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n.2, hn⟩
  · rintro ⟨hx, ha⟩
    exact ⟨⟨x, hx⟩, ha, rfl⟩

include h hKU in
theorem Data.Hyp.mem_ZQ_iff {x : G} :
    x ∈ Data.ZQ h hKU hf ↔ ∃ _ : x ∈ Data.Nn h hKU hf, x * (d.t * x * d.t) ∈ d.ZX₄ := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n.2, hn⟩
  · rintro ⟨hx, ha⟩
    exact ⟨⟨x, hx⟩, ha, rfl⟩

include h hKU in
theorem Data.Hyp.B₁_le_Nn : Data.B₁ h hKU hf ≤ Data.Nn h hKU hf := by
  rintro _ ⟨n, -, rfl⟩
  exact n.2

include h hKU in
theorem Data.Hyp.ZQ_le_Nn : Data.ZQ h hKU hf ≤ Data.Nn h hKU hf := by
  rintro _ ⟨n, -, rfl⟩
  exact n.2

include h hKU in
theorem Data.Hyp.range_delta_eq_A₂_sup_K₂ :
    (Data.delta h hKU hf).range = d.A₂ ⊔ d.K₂ := by
  have hle : (Data.delta h hKU hf).range ≤ d.A₂ ⊔ d.K₂ := by
    rintro _ ⟨n, rfl⟩
    exact h.delta_mem_A₂_sup_K₂ hKU hf n
  have hK₂A₂ : d.K₂ ≤ normalizer (d.A₂ : Set G) := by
    rintro _ ⟨k, hk, rfl⟩
    refine mem_normalizer_fintype fun x hx => ?_
    obtain ⟨a, ha, rfl⟩ := hx
    have h1 : k * a * k⁻¹ ∈ A₂sub := (mem_normalizer_iff.1 (K₂sub_le_normalizer_A₂sub hk) a).1 ha
    exact ⟨k * a * k⁻¹, h1, by rw [map_mul, map_mul, map_inv]⟩
  have hinf : d.K₂ ⊓ d.A₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨k, hk, rfl⟩, ⟨a, ha, hka⟩⟩
    have : a = k := d.ι_injective hka
    rw [this] at ha
    have hk1 : k ∈ A₂sub ⊓ K₂sub := ⟨ha, hk⟩
    rw [A₂sub_inf_K₂sub] at hk1
    rw [Subgroup.mem_bot.1 hk1, map_one]
    exact one_mem _
  have hcard := PGrp.card_sup_mul_card_inf (A := d.K₂) (B := d.A₂) hK₂A₂
  rw [hinf, Subgroup.card_bot, mul_one] at hcard
  have hK₂card : Nat.card d.K₂ = 60 := by
    rw [← h.map_theta_Lam₁ hKU hf, Subgroup.card_map_of_injective (Data.theta_injective h hf),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Data.Lam₁_le_K₀ h hKU hf)).toEquiv,
      h.card_Lam₁ hKU hf]
  have hA₂card : Nat.card d.A₂ = 2 ^ 8 := by
    rw [Data.A₂, d.card_pull, card_A₂sub]
  have hrange : Nat.card (Data.delta h hKU hf).range = 15360 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (h.delta_injective hKU hf)).toEquiv,
      h.card_Nn hKU hf]
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hrange, sup_comm, hcard, hK₂card, hA₂card]
  norm_num

end Defs

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
