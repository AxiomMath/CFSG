module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G}

theorem z4j_d17_Gset {S Vg V : Subgroup G} {β : G} (hVg : IsPGroup 2 Vg) (hVV : V ≤ Vg)
    (hVn : ∀ g ∈ Vg, ∀ v ∈ V, g * v * g⁻¹ ∈ V) (hV4 : Nat.card V = 4)
    (hVe : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a ∧ a * a = 1)
    (htV : ∀ g : G, ∀ v ∈ V, g * t * g⁻¹ ≠ v)
    (hVβ : V ≤ centralizer ({β} : Set G)) {g₀ : G} (hβ : β = g₀ * t * g₀⁻¹)
    (hcard : Nat.card ↥(Vg ⊓ centralizer ({β} : Set G)) = 128)
    (hconj : ∀ (g : G) (P : Subgroup G), IsPGroup 2 P →
      P ≤ centralizer ({g * t * g⁻¹} : Set G) → Nat.card P = 128 →
      ∃ k : G, P.map (MulAut.conj k).toMonoidHom = S)
    (h17 : ∀ V'' : Subgroup G, V'' ≤ S → (∀ s ∈ S, ∀ v ∈ V'', s * v * s⁻¹ ∈ V'') →
      Nat.card V'' = 4 → (∀ a ∈ V'', ∀ b ∈ V'', a * b = b * a ∧ a * a = 1) →
      (∀ g : G, ∀ v ∈ V'', g * t * g⁻¹ ≠ v) →
      17 ≤ {x : G | x ∈ S ⊓ centralizer (V'' : Set G) ∧ x * x = 1}.ncard) :
    17 ≤ {x : G | x ∈ Vg ⊓ centralizer ({β} : Set G) ⊓ centralizer (V : Set G) ∧
      x * x = 1}.ncard := by
  let P : Subgroup G := Vg ⊓ centralizer ({β} : Set G)
  have hP2 : IsPGroup 2 P := hVg.to_le inf_le_left
  have hPcent : P ≤ centralizer ({g₀ * t * g₀⁻¹} : Set G) := by
    rw [← hβ]; exact inf_le_right
  have hPcard : Nat.card P = 128 := hcard
  obtain ⟨k, hk⟩ := hconj g₀ P hP2 hPcent hPcard
  let c : G →* G := (MulAut.conj k).toMonoidHom
  have hc : ∀ x : G, c x = k * x * k⁻¹ := fun x => by
    simp only [c, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hcinj : Function.Injective c := (MulAut.conj k).injective
  have hVP : V ≤ P := le_inf hVV hVβ
  let V'' : Subgroup G := V.map c
  have hV''S : V'' ≤ S := by
    rw [← hk]
    exact Subgroup.map_mono hVP
  have hV''norm : ∀ s ∈ S, ∀ v ∈ V'', s * v * s⁻¹ ∈ V'' := by
    intro s hs v hv
    rw [Subgroup.mem_map] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    have hs' : s ∈ P.map c := by rw [hk]; exact hs
    rw [Subgroup.mem_map] at hs'
    obtain ⟨p, hp, rfl⟩ := hs'
    have hpVg : p ∈ Vg := (Subgroup.mem_inf.mp hp).1
    have hmem : c (p * u * p⁻¹) ∈ V'' := Subgroup.mem_map_of_mem c (hVn p hpVg u hu)
    simpa only [map_mul, map_inv] using hmem
  have hV''card : Nat.card V'' = 4 := by
    rw [Subgroup.card_map_of_injective (f := c) (K := V) hcinj, hV4]
  have hV''ea : ∀ a ∈ V'', ∀ b ∈ V'', a * b = b * a ∧ a * a = 1 := by
    intro a ha b hb
    rw [Subgroup.mem_map] at ha hb
    obtain ⟨u, hu, rfl⟩ := ha
    obtain ⟨u', hu', rfl⟩ := hb
    refine ⟨?_, ?_⟩
    · rw [← map_mul, ← map_mul, (hVe u hu u' hu').1]
    · rw [← map_mul, (hVe u hu u hu).2, map_one]
  have hV''t : ∀ g : G, ∀ v ∈ V'', g * t * g⁻¹ ≠ v := by
    intro g v hv heq
    rw [Subgroup.mem_map] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    rw [hc u] at heq
    have hconj_eq : (k⁻¹ * g) * t * (k⁻¹ * g)⁻¹ = u := by
      calc (k⁻¹ * g) * t * (k⁻¹ * g)⁻¹
          = k⁻¹ * (g * t * g⁻¹) * k := by group
        _ = k⁻¹ * (k * u * k⁻¹) * k := by rw [heq]
        _ = u := by group
    exact htV (k⁻¹ * g) u hu hconj_eq
  have h17' := h17 V'' hV''S hV''norm hV''card hV''ea hV''t
  have hsub : {x : G | x ∈ S ⊓ centralizer (V'' : Set G) ∧ x * x = 1} ⊆
      c '' {x : G | x ∈ Vg ⊓ centralizer ({β} : Set G) ⊓ centralizer (V : Set G) ∧
        x * x = 1} := by
    intro x hx
    obtain ⟨⟨hxS, hxcent⟩, hxx⟩ := hx
    have hxS' : x ∈ P.map c := by rw [hk]; exact hxS
    rw [Subgroup.mem_map] at hxS'
    obtain ⟨p, hp, hp_eq⟩ := hxS'
    have hpVg : p ∈ Vg := (Subgroup.mem_inf.mp hp).1
    have hpcentβ : p ∈ centralizer ({β} : Set G) := (Subgroup.mem_inf.mp hp).2
    have hpp : p * p = 1 := by
      apply hcinj
      rw [map_mul, hp_eq, hxx, map_one]
    have hpcentV : p ∈ centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have huV'' : c u ∈ V'' := Subgroup.mem_map_of_mem c hu
      have hcomm : c u * x = x * c u := (Subgroup.mem_centralizer_iff.mp hxcent) (c u) huV''
      apply hcinj
      rw [map_mul, map_mul, hp_eq]
      exact hcomm
    exact ⟨p, ⟨⟨⟨hpVg, hpcentβ⟩, hpcentV⟩, hpp⟩, hp_eq⟩
  have hle : {x : G | x ∈ S ⊓ centralizer (V'' : Set G) ∧ x * x = 1}.ncard ≤
      (c '' {x : G | x ∈ Vg ⊓ centralizer ({β} : Set G) ⊓ centralizer (V : Set G) ∧
        x * x = 1}).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_image_of_injective _ hcinj] at hle
  exact le_trans h17' hle

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
