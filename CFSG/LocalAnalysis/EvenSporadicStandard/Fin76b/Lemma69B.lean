module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma69C

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

@[expose] def E2 {G : Type*} [Group G] (E : Subgroup G) (t : G) : Set G :=
  {e | e ∈ E ∧ e * e = 1 ∧ e ≠ 1 ∧ e ≠ t}

@[expose] def E4 {G : Type*} [Group G] (E : Subgroup G) (t : G) : Set G := {e | e ∈ E ∧ e * e = t}

@[expose] def blk {G : Type*} [Group G] (s : G) (C : Set G) : Set G := (fun e => s * e) '' C

namespace Hyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B : Subgroup G} {S : Subgroup G}
  (h : Hyp69 L z t T₀ E Q x β B S)

include h

theorem E2_sub : E2 E t ⊆ E := fun _ he => he.1

theorem E4_sub : E4 E t ⊆ E := fun _ he => he.1

theorem E0_sub : ({1, t} : Set G) ⊆ E := by
  rintro e (rfl | rfl)
  · exact one_mem _
  · exact h.t_mem_E

theorem mem_blk {s u : G} {C : Set G} : u ∈ blk s C ↔ ∃ e ∈ C, u = s * e := by
  constructor
  · rintro ⟨e, he, rfl⟩; exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩; exact ⟨e, he, rfl⟩

theorem blk_disjoint {s₁ s₂ : G} (hs₁ : s₁ ∈ S) (hs₂ : s₂ ∈ S) (h1 : s₁⁻¹ * s₂ ≠ 1)
    (h2 : s₁⁻¹ * s₂ ≠ t) {C₁ C₂ : Set G} (hC₁ : C₁ ⊆ E) (hC₂ : C₂ ⊆ E) :
    Disjoint (blk s₁ C₁) (blk s₂ C₂) := by
  rw [Set.disjoint_left]
  rintro u hu hu'
  obtain ⟨e₁, he₁, rfl⟩ := (mem_blk h).1 hu
  obtain ⟨e₂, he₂, he⟩ := (mem_blk h).1 hu'
  have h3 : s₁⁻¹ * s₂ = e₁ * e₂⁻¹ := by
    calc s₁⁻¹ * s₂ = s₁⁻¹ * (s₂ * e₂) * e₂⁻¹ := by group
      _ = s₁⁻¹ * (s₁ * e₁) * e₂⁻¹ := by rw [← he]
      _ = e₁ * e₂⁻¹ := by group
  have h4 : s₁⁻¹ * s₂ ∈ E := by
    rw [h3]; exact mul_mem (hC₁ he₁) (inv_mem (hC₂ he₂))
  rcases h.S_inf_E (mul_mem (inv_mem hs₁) hs₂) h4 with h5 | h5
  · exact h1 h5
  · exact h2 h5

theorem blk_inter {s : G} {C₁ C₂ : Set G} : blk s C₁ ∩ blk s C₂ = blk s (C₁ ∩ C₂) := by
  ext u
  constructor
  · rintro ⟨⟨e, he, rfl⟩, ⟨e', he', hee'⟩⟩
    have : e = e' := mul_left_cancel hee'.symm
    subst this
    exact ⟨e, ⟨he, he'⟩, rfl⟩
  · rintro ⟨e, ⟨he1, he2⟩, rfl⟩
    exact ⟨⟨e, he1, rfl⟩, ⟨e, he2, rfl⟩⟩

theorem exists_decomp {α : G} (hα : AlphaSpec S z t α) {u : G} (hu : u ∈ S ⊔ E) :
    ∃ e ∈ E, u = e ∨ u = z * e ∨ u = α * e ∨ u = (α * z) * e := by
  obtain ⟨s, hs, e, he, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer h.E_le_cent_S hu
  have htE := h.t_mem_E
  have htc : ∀ f : G, t * f = f * t → True := fun _ _ => trivial
  rcases hα.list s hs with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1]
  · exact ⟨e, he, Or.inl (one_mul e)⟩
  · exact ⟨t * e, mul_mem htE he, Or.inl rfl⟩
  · exact ⟨e, he, Or.inr (Or.inl rfl)⟩
  · exact ⟨t * e, mul_mem htE he, Or.inr (Or.inl (by group))⟩
  · exact ⟨e, he, Or.inr (Or.inr (Or.inl rfl))⟩
  · exact ⟨t * e, mul_mem htE he, Or.inr (Or.inr (Or.inl (by group)))⟩
  · exact ⟨e, he, Or.inr (Or.inr (Or.inr rfl))⟩
  · exact ⟨t * e, mul_mem htE he, Or.inr (Or.inr (Or.inr (by group)))⟩

theorem z_alpha {α : G} (hα : AlphaSpec S z t α) : z * α = t * (α * z) := by
  have h1 := hα.rel
  calc z * α = (t * t) * (z * α) := by rw [h.t_sq, one_mul]
    _ = t * (t * (z * α)) := by rw [mul_assoc]
    _ = t * (α * z) := by rw [← h1]

theorem r_sq {α : G} (hα : AlphaSpec S z t α) : (α * z) * (α * z) = t := by
  have hαt : α * t = t * α := h.t_comm_S α hα.mem
  calc (α * z) * (α * z) = α * (z * α) * z := by group
    _ = α * (t * (α * z)) * z := by rw [h.z_alpha hα]
    _ = t * (α * (α * z)) * z := by
      calc α * (t * (α * z)) * z = (α * t) * (α * z) * z := by group
        _ = (t * α) * (α * z) * z := by rw [hαt]
        _ = t * (α * (α * z)) * z := by group
    _ = t * ((α * α) * (z * z)) := by group
    _ = t := by rw [hα.sq, h.z_sq]; group

theorem alpha_z_mem {α : G} (hα : AlphaSpec S z t α) : α * z ∈ S := mul_mem hα.mem h.zS

theorem classify {α : G} (hα : AlphaSpec S z t α) {u : G} (hu : u ∈ S ⊔ E) (hu2 : u * u = 1)
    (hu1 : u ≠ 1) (hut : u ≠ t) :
    u ∈ blk z {1, t} ∨ u ∈ blk z (E2 E t) ∨ u ∈ blk α {1, t} ∨ u ∈ blk α (E2 E t) ∨
      u ∈ E2 E t ∨ u ∈ blk (α * z) (E4 E t) := by
  obtain ⟨e, he, hcase⟩ := h.exists_decomp hα hu
  have key : ∀ s ∈ S, s * s = 1 → u = s * e → e * e = 1 := by
    intro s hs hs2 hus
    have hc : e * s = s * e := (h.S_comm_E s hs e he).symm
    calc e * e = (s * s) * (e * e) := by rw [hs2, one_mul]
      _ = (s * e) * (s * e) := by
        calc (s * s) * (e * e) = s * (s * e) * e := by group
          _ = s * (e * s) * e := by rw [hc]
          _ = (s * e) * (s * e) := by group
      _ = 1 := by rw [← hus]; exact hu2
  have split : e * e = 1 → ∀ s, (u = s * e) → (e = 1 ∨ e = t ∨ e ∈ E2 E t) := by
    intro hee s _
    by_cases h1 : e = 1
    · exact Or.inl h1
    by_cases h2 : e = t
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr ⟨he, hee, h1, h2⟩)
  rcases hcase with hc | hc | hc | hc
  · right; right; right; right; left
    subst hc
    exact ⟨he, hu2, hu1, hut⟩
  · have hee := key z h.zS h.z_sq hc
    rcases split hee z hc with h1 | h1 | h1
    · left; exact (h.mem_blk).2 ⟨e, Or.inl h1, hc⟩
    · left; exact (h.mem_blk).2 ⟨e, Or.inr h1, hc⟩
    · right; left; exact (h.mem_blk).2 ⟨e, h1, hc⟩
  · have hee := key α hα.mem hα.sq hc
    rcases split hee α hc with h1 | h1 | h1
    · right; right; left; exact (h.mem_blk).2 ⟨e, Or.inl h1, hc⟩
    · right; right; left; exact (h.mem_blk).2 ⟨e, Or.inr h1, hc⟩
    · right; right; right; left; exact (h.mem_blk).2 ⟨e, h1, hc⟩
  · right; right; right; right; right
    refine (h.mem_blk).2 ⟨e, ⟨he, ?_⟩, hc⟩
    have hs := h.alpha_z_mem hα
    have hcom : e * (α * z) = (α * z) * e := (h.S_comm_E _ hs e he).symm
    have h1 : t * (e * e) = 1 := by
      calc t * (e * e) = ((α * z) * (α * z)) * (e * e) := by rw [h.r_sq hα]
        _ = (α * z) * ((α * z) * e) * e := by group
        _ = (α * z) * (e * (α * z)) * e := by rw [hcom]
        _ = ((α * z) * e) * ((α * z) * e) := by group
        _ = 1 := by rw [← hc]; exact hu2
    calc e * e = (t * t) * (e * e) := by rw [h.t_sq, one_mul]
      _ = t * (t * (e * e)) := by rw [mul_assoc]
      _ = t := by rw [h1, mul_one]

theorem alpha_conj_z {α : G} (hα : AlphaSpec S z t α) : α * z * α⁻¹ = z * t := by
  have hzt : z * t = t * z := (h.t_comm_S z h.zS).symm ▸ rfl
  calc α * z * α⁻¹ = (t * (z * α)) * α⁻¹ := by rw [hα.rel]
    _ = t * z := by group
    _ = z * t := (h.t_comm_S z h.zS).symm

theorem z_conj_alpha {α : G} (hα : AlphaSpec S z t α) : z * α * z⁻¹ = α * t := by
  have hαt : α * t = t * α := h.t_comm_S α hα.mem
  calc z * α * z⁻¹ = (t * (α * z)) * z⁻¹ := by rw [h.z_alpha hα]
    _ = t * α := by group
    _ = α * t := hαt.symm

theorem z_mem_M : z ∈ normalizer ((S ⊔ E : Subgroup G) : Set G) :=
  le_normalizer (mem_sup_left h.zS)

theorem dich_blk {s : G} (hs : s ∈ S) {C : Set G} (hC : C = E2 E t ∨ C = E4 E t) {O : Set G}
    (hO : ∀ m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G), ∀ u ∈ O, m * u * m⁻¹ ∈ O) :
    blk s C ⊆ O ∨ Disjoint (blk s C) O := by
  by_cases hex : ∃ e₁ ∈ C, s * e₁ ∈ O
  · left
    obtain ⟨e₁, he₁, hse₁⟩ := hex
    rintro u ⟨e₂, he₂, rfl⟩
    have horb : ∃ w ∈ L ⊓ centralizer ({t} : Set G), w * e₁ * w⁻¹ = e₂ := by
      rcases hC with rfl | rfl
      · exact h.W_orbit_two he₁.1 he₁.2.1 he₁.2.2.1 he₁.2.2.2 he₂.1 he₂.2.1 he₂.2.2.1 he₂.2.2.2
      · exact h.W_orbit_four he₁.1 he₁.2 he₂.1 he₂.2
    obtain ⟨w, hw, hwe⟩ := horb
    have := hO w (h.W_mem_M hw) _ hse₁
    have e1 : w * (s * e₁) * w⁻¹ = s * e₂ := by
      calc w * (s * e₁) * w⁻¹ = (w * s) * e₁ * w⁻¹ := by group
        _ = (s * w) * e₁ * w⁻¹ := by rw [h.W_cent_S hw hs]
        _ = s * (w * e₁ * w⁻¹) := by group
        _ = s * e₂ := by rw [hwe]
    rwa [e1] at this
  · right
    rw [Set.disjoint_left]
    rintro u ⟨e, he, rfl⟩ hu
    exact hex ⟨e, he, hu⟩

end Hyp69

end CFSG.EvenSporadicStandard.Fin76b
