module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WreathInner

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

variable {Γ : Type*} [Group Γ] {N₁ N₂ : Subgroup Γ} {σ : Γ}

namespace WreathData

variable (h : WreathData N₁ N₂ σ)
include h

theorem symm : WreathData N₂ N₁ σ where
  comm a ha b hb := (h.comm b hb a ha).symm
  disj := h.disj.symm
  sq := h.sq
  swap₁ := h.swap₂
  swap₂ := h.swap₁

theorem conj_conj (x : Γ) : σ * (σ * x * σ⁻¹) * σ⁻¹ = x := by
  calc σ * (σ * x * σ⁻¹) * σ⁻¹ = (σ * σ) * x * (σ * σ)⁻¹ := by group
    _ = x := by rw [h.sq]; group

theorem conj_mem₂ {n u : Γ} (hn : n ∈ N₁ ⊔ N₂) (hu : u ∈ N₂) : n * u * n⁻¹ ∈ N₂ := by
  obtain ⟨n₁, hn₁, n₂, hn₂, rfl⟩ := h.dec hn
  have h1 := h.conj_prod hn₁ N₁.one_mem hn₂ hu
  simp only [mul_one, one_mul, mul_inv_cancel] at h1
  rw [h1]
  exact N₂.mul_mem (N₂.mul_mem hn₂ hu) (N₂.inv_mem hn₂)

theorem swap_components {x₁ x₂ y₁ y₂ : Γ} (hx₁ : x₁ ∈ N₁) (hx₂ : x₂ ∈ N₂) (hy₁ : y₁ ∈ N₁)
    (hy₂ : y₂ ∈ N₂) (hxy : σ * (x₁ * x₂) * σ⁻¹ = y₁ * y₂) :
    σ * x₂ * σ⁻¹ = y₁ ∧ σ * x₁ * σ⁻¹ = y₂ := by
  have h1 : (σ * x₂ * σ⁻¹) * (σ * x₁ * σ⁻¹) = y₁ * y₂ := by
    rw [h.comm _ (h.swap₂ x₂ hx₂) _ (h.swap₁ x₁ hx₁), ← hxy]
    group
  exact wreath_uniq h.disj (h.swap₂ x₂ hx₂) hy₁ (h.swap₁ x₁ hx₁) hy₂ h1

theorem comm_components {u a₁ v a₂ : Γ} (hu : u ∈ N₁) (ha₁ : a₁ ∈ N₁) (hv : v ∈ N₂)
    (ha₂ : a₂ ∈ N₂) (hc : (u * v) * (a₁ * a₂) = (a₁ * a₂) * (u * v)) :
    u * a₁ = a₁ * u ∧ v * a₂ = a₂ * v := by
  have h1 : (u * a₁) * (v * a₂) = (a₁ * u) * (a₂ * v) := by
    calc (u * a₁) * (v * a₂) = u * (a₁ * v) * a₂ := by group
      _ = u * (v * a₁) * a₂ := by rw [h.comm a₁ ha₁ v hv]
      _ = (u * v) * (a₁ * a₂) := by group
      _ = (a₁ * a₂) * (u * v) := hc
      _ = a₁ * (a₂ * u) * v := by group
      _ = a₁ * (u * a₂) * v := by rw [h.comm u hu a₂ ha₂]
      _ = (a₁ * u) * (a₂ * v) := by group
  exact wreath_uniq h.disj (N₁.mul_mem hu ha₁) (N₁.mul_mem ha₁ hu) (N₂.mul_mem hv ha₂)
    (N₂.mul_mem ha₂ hv) h1

theorem exists_components_involution {t : Γ} (ht : t ∈ N₁ ⊔ N₂) (hσt : σ * t * σ⁻¹ = t)
    (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    ∃ t₁ ∈ N₁, ∃ t₂ ∈ N₂, t = t₁ * t₂ ∧ t₁ * t₁ = 1 ∧ t₂ * t₂ = 1 ∧ σ * t₁ * σ⁻¹ = t₂ ∧
      σ * t₂ * σ⁻¹ = t₁ ∧ t₁ ≠ 1 ∧ t₂ ≠ 1 := by
  obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := h.dec ht
  obtain ⟨hs2, hs1⟩ := h.swap_components ht₁ ht₂ ht₁ ht₂ hσt
  have hsq : (t₁ * t₁) * (t₂ * t₂) = 1 * 1 := by
    calc (t₁ * t₁) * (t₂ * t₂) = t₁ * (t₁ * t₂) * t₂ := by group
      _ = t₁ * (t₂ * t₁) * t₂ := by rw [h.comm t₁ ht₁ t₂ ht₂]
      _ = (t₁ * t₂) * (t₁ * t₂) := by group
      _ = 1 * 1 := by rw [ht2, one_mul]
  obtain ⟨h11, h22⟩ := wreath_uniq h.disj (N₁.mul_mem ht₁ ht₁) N₁.one_mem
    (N₂.mul_mem ht₂ ht₂) N₂.one_mem hsq
  refine ⟨t₁, ht₁, t₂, ht₂, rfl, h11, h22, hs1, hs2, ?_, ?_⟩
  · rintro rfl
    apply ht1
    rw [← hs1]
    group
  · rintro rfl
    apply ht1
    rw [← hs2]
    group

theorem exists_components_swap {a t₁ t₂ : Γ} (ht₁ : t₁ ∈ N₁) (ht₂ : t₂ ∈ N₂)
    (ha : a ∈ N₁ ⊔ N₂) (hσa : σ * a * σ⁻¹ = a * (t₁ * t₂)) :
    ∃ a₁ ∈ N₁, ∃ a₂ ∈ N₂, a = a₁ * a₂ ∧ σ * a₂ * σ⁻¹ = a₁ * t₁ ∧
      σ * a₁ * σ⁻¹ = a₂ * t₂ := by
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := h.dec ha
  have h1 : σ * (a₁ * a₂) * σ⁻¹ = (a₁ * t₁) * (a₂ * t₂) := by
    rw [hσa]
    calc a₁ * a₂ * (t₁ * t₂) = a₁ * (a₂ * t₁) * t₂ := by group
      _ = a₁ * (t₁ * a₂) * t₂ := by rw [h.comm t₁ ht₁ a₂ ha₂]
      _ = (a₁ * t₁) * (a₂ * t₂) := by group
  obtain ⟨h2, h3⟩ := h.swap_components ha₁ ha₂ (N₁.mul_mem ha₁ ht₁) (N₂.mul_mem ha₂ ht₂) h1
  exact ⟨a₁, ha₁, a₂, ha₂, rfl, h2, h3⟩

theorem mem_sup_of_comm {u c : Γ} (hidx : (N₁ ⊔ N₂).index = 2) (hσM : σ ∉ N₁ ⊔ N₂)
    (hu : u ∈ N₁) (hu1 : u ≠ 1) (hσu : σ * u * σ⁻¹ ∈ N₂) (hcu : c * u = u * c) :
    c ∈ N₁ ⊔ N₂ := by
  by_contra hc
  have hn : c * σ ∈ N₁ ⊔ N₂ := (mul_mem_iff_of_index_two hidx).2 (iff_of_false hc hσM)
  have h1 : (c * σ) * (σ * u * σ⁻¹) * (c * σ)⁻¹ = u := by
    calc (c * σ) * (σ * u * σ⁻¹) * (c * σ)⁻¹ = c * ((σ * σ) * u * (σ * σ)⁻¹) * c⁻¹ := by group
      _ = c * u * c⁻¹ := by rw [h.sq]; group
      _ = u := by rw [hcu]; group
  have h2 : u ∈ N₂ := by
    rw [← h1]
    exact h.conj_mem₂ hn hσu
  have h3 : u ∈ N₁ ⊓ N₂ := ⟨hu, h2⟩
  rw [h.disj.eq_bot, mem_bot] at h3
  exact hu1 h3

end WreathData

@[expose] def WreathData.comp (h : WreathData N₁ N₂ σ) (C : Subgroup Γ) : Subgroup Γ where
  carrier := {u | u ∈ N₁ ∧ ∃ v ∈ N₂, u * v ∈ C}
  mul_mem' := by
    rintro u u' ⟨hu, v, hv, huv⟩ ⟨hu', v', hv', huv'⟩
    refine ⟨N₁.mul_mem hu hu', v * v', N₂.mul_mem hv hv', ?_⟩
    have h1 : u * u' * (v * v') = (u * v) * (u' * v') := by
      calc u * u' * (v * v') = u * (u' * v) * v' := by group
        _ = u * (v * u') * v' := by rw [h.comm u' hu' v hv]
        _ = (u * v) * (u' * v') := by group
    rw [h1]
    exact C.mul_mem huv huv'
  one_mem' := ⟨N₁.one_mem, 1, N₂.one_mem, by rw [mul_one]; exact C.one_mem⟩
  inv_mem' := by
    rintro u ⟨hu, v, hv, huv⟩
    refine ⟨N₁.inv_mem hu, v⁻¹, N₂.inv_mem hv, ?_⟩
    rw [h.comm u⁻¹ (N₁.inv_mem hu) v⁻¹ (N₂.inv_mem hv), ← mul_inv_rev]
    exact C.inv_mem huv

namespace WreathData

variable (h : WreathData N₁ N₂ σ)
include h

theorem comp_le (C : Subgroup Γ) : h.comp C ≤ N₁ := fun _ hu => hu.1

theorem mem_comp_of_mul_mem {C : Subgroup Γ} {u v : Γ} (hu : u ∈ N₁) (hv : v ∈ N₂)
    (huv : u * v ∈ C) : u ∈ h.comp C := ⟨hu, v, hv, huv⟩

theorem mem_comp_symm_of_mul_mem {C : Subgroup Γ} {u v : Γ} (hu : u ∈ N₁) (hv : v ∈ N₂)
    (huv : u * v ∈ C) : v ∈ h.symm.comp C :=
  ⟨hv, u, hu, by rw [← h.comm u hu v hv]; exact huv⟩

theorem isPGroup_comp {C : Subgroup Γ} (hC : IsPGroup 2 C) : IsPGroup 2 (h.comp C) := by
  intro g
  obtain ⟨hu, v, hv, huv⟩ := g.2
  obtain ⟨k, hk⟩ := hC ⟨(g : Γ) * v, huv⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : ((g : Γ) * v) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h2 : (g : Γ) ^ 2 ^ k * v ^ 2 ^ k = 1 := by
    rw [← Commute.mul_pow (h.comm _ hu v hv)]
    exact h1
  have h3 : (g : Γ) ^ 2 ^ k ∈ N₁ ⊓ N₂ := by
    refine ⟨N₁.pow_mem hu _, ?_⟩
    rw [eq_inv_of_mul_eq_one_left h2]
    exact N₂.inv_mem (N₂.pow_mem hv _)
  rw [h.disj.eq_bot, mem_bot] at h3
  simpa using h3

theorem card_inf_le_mul [Finite Γ] (C : Subgroup Γ) :
    Nat.card ↥((N₁ ⊔ N₂) ⊓ C) ≤ Nat.card (h.comp C) * Nat.card (h.symm.comp C) := by
  let g : ↥(h.comp C) × ↥(h.symm.comp C) → Γ := fun p => (p.1 : Γ) * p.2
  have hsub : (((N₁ ⊔ N₂) ⊓ C : Subgroup Γ) : Set Γ) ⊆ Set.range g := by
    rintro c ⟨hcM, hcC⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := h.dec hcM
    exact ⟨(⟨u, h.mem_comp_of_mul_mem hu hv hcC⟩, ⟨v, h.mem_comp_symm_of_mul_mem hu hv hcC⟩),
      rfl⟩
  calc Nat.card ↥((N₁ ⊔ N₂) ⊓ C) ≤ Nat.card (Set.range g) :=
        Nat.card_mono (Set.toFinite _) hsub
    _ ≤ Nat.card (↥(h.comp C) × ↥(h.symm.comp C)) := Finite.card_range_le g
    _ = _ := Nat.card_prod _ _

theorem mem_of_card_comp_le [Finite Γ] {C : Subgroup Γ} (hCM : C ≤ N₁ ⊔ N₂)
    (hcard : Nat.card (h.comp C) * Nat.card (h.symm.comp C) ≤ Nat.card C) {u : Γ}
    (hu : u ∈ h.comp C) : u ∈ C := by
  let g : ↥(h.comp C) × ↥(h.symm.comp C) → Γ := fun p => (p.1 : Γ) * p.2
  have hsub : (C : Set Γ) ⊆ Set.range g := by
    intro c hcC
    obtain ⟨u, hu, v, hv, rfl⟩ := h.dec (hCM hcC)
    exact ⟨(⟨u, h.mem_comp_of_mul_mem hu hv hcC⟩, ⟨v, h.mem_comp_symm_of_mul_mem hu hv hcC⟩),
      rfl⟩
  have hle : (Set.range g).ncard ≤ (C : Set Γ).ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact (Finite.card_range_le g).trans (by rw [Nat.card_prod]; exact hcard)
  have heq := Set.eq_of_subset_of_ncard_le hsub hle (Set.toFinite _)
  have hmem : u ∈ Set.range g := ⟨(⟨u, hu⟩, 1), by simp [g]⟩
  rw [← heq] at hmem
  exact hmem

end WreathData

end CFSG.EvenSporadicStandard.Fin76b
