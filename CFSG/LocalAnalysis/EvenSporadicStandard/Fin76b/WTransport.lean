module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.RootFacts

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

variable {G : Type*} [Group G]

@[expose] def rootSet (X : Subgroup G) (t : G) : Set G := {x | x ∈ X ∧ x * x = t}

theorem image_val_roots {X : Subgroup G} {t : G} (ht : t ∈ X) :
    Subtype.val '' {x : ↥X | x * x = ⟨t, ht⟩} = rootSet X t := by
  ext x
  constructor
  · rintro ⟨⟨y, hy⟩, h, rfl⟩
    exact ⟨hy, congrArg Subtype.val h⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, Subtype.ext h, rfl⟩

theorem map_rootGroup {X : Subgroup G} {t : G} (ht : t ∈ X) :
    (rootGroup ↥X ⟨t, ht⟩).map X.subtype = closure (rootSet X t) := by
  rw [rootGroup, MonoidHom.map_closure, Subgroup.coe_subtype, image_val_roots ht]

theorem map_centralizer_subtype {X : Subgroup G} {t : G} (ht : t ∈ X) :
    (centralizer ({⟨t, ht⟩} : Set ↥X)).map X.subtype = X ⊓ centralizer ({t} : Set G) := by
  ext y
  simp only [Subgroup.mem_map, mem_centralizer_singleton_iff, Subgroup.mem_inf,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, congrArg Subtype.val hx⟩
  · rintro ⟨hy, hc⟩
    exact ⟨⟨y, hy⟩, Subtype.ext hc, rfl⟩

theorem closure_rootSet_le (X : Subgroup G) (t : G) : closure (rootSet X t) ≤ X :=
  (closure_le X).2 fun _ hx => hx.1

theorem RootFactsFor.of_ambient {X : Subgroup G} {t : G} (ht : t ∈ X)
    (h1 : Nat.card ↥(X ⊓ centralizer ({t} : Set G)) = 1920)
    (h2 : (rootSet X t).ncard ≤ 20)
    (h3 : Nat.card ↥(closure (rootSet X t)) = 32)
    (h4 : ∀ l ∈ X, (∀ r ∈ X, r * r = t → l * r = r * l) → l = 1 ∨ l = t)
    (h5 : ∃ β ∈ X, β * t = t * β ∧ orderOf β = 3 ∧
      Nat.card ↥(closure (rootSet X t) ⊓ centralizer ({β} : Set G)) = 8 ∧
      ∃ d₁ ∈ closure (rootSet X t) ⊓ centralizer ({β} : Set G),
        ∃ d₂ ∈ closure (rootSet X t) ⊓ centralizer ({β} : Set G), d₁ * d₂ ≠ d₂ * d₁) :
    RootFactsFor ↥X ⟨t, ht⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_centralizer_subtype ht, Subgroup.card_map_of_injective X.subtype_injective] at h1
    exact h1
  · rw [← Set.ncard_image_of_injective _ (Subtype.val_injective (p := (· ∈ X))), image_val_roots ht]
    exact h2
  · rw [← map_rootGroup ht, Subgroup.card_map_of_injective X.subtype_injective] at h3
    exact h3
  · intro l hl
    have := h4 (l : G) l.2 fun r hr hrr =>
      congrArg Subtype.val (hl ⟨r, hr⟩ (Subtype.ext hrr))
    rcases this with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · obtain ⟨β, hβX, hβt, hβ3, hcard, d₁, hd₁, d₂, hd₂, hne⟩ := h5
    have himg : (rootGroup ↥X ⟨t, ht⟩ ⊓ centralizer ({(⟨β, hβX⟩ : ↥X)} : Set ↥X)).map X.subtype =
        closure (rootSet X t) ⊓ centralizer ({β} : Set G) := by
      rw [Subgroup.map_inf _ _ _ X.subtype_injective, map_rootGroup ht,
        map_centralizer_subtype hβX, ← inf_assoc, inf_of_le_left (closure_rootSet_le X t)]
    have hmem : ∀ d ∈ closure (rootSet X t) ⊓ centralizer ({β} : Set G),
        ∃ y ∈ rootGroup ↥X ⟨t, ht⟩ ⊓ centralizer ({(⟨β, hβX⟩ : ↥X)} : Set ↥X), (y : G) = d := by
      intro d hd
      rw [← himg] at hd
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hd
      exact ⟨y, hy, rfl⟩
    obtain ⟨y₁, hy₁, rfl⟩ := hmem d₁ hd₁
    obtain ⟨y₂, hy₂, rfl⟩ := hmem d₂ hd₂
    refine ⟨⟨β, hβX⟩, Subtype.ext hβt, ?_, ?_, y₁, hy₁, y₂, hy₂, fun hc => hne ?_⟩
    · rw [← Subgroup.orderOf_coe]
      exact hβ3
    · rw [← himg, Subgroup.card_map_of_injective X.subtype_injective] at hcard
      exact hcard
    · exact congrArg Subtype.val hc

end CFSG.EvenSporadicStandard.Fin76b
