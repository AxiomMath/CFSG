module

public import CFSG.Fischer.NoF25.Defs
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Tactic.Group

public section

namespace CFSG.Fischer

@[expose] def Oset {Y : Type*} [Group Y] (C : Set Y) (k : ℕ) : Set (Set Y) :=
  {G | ∃ r : Y, (∀ x ∈ C, r * x * r⁻¹ ∈ C) ∧ (∀ x ∈ C, r * (r * x * r⁻¹) * r⁻¹ = x) ∧
    G = {x | x ∈ C ∧ r * x * r⁻¹ = x} ∧ G.ncard = k}

section Group

variable {Y : Type*} [Group Y]

@[expose] def osetPerm {C : Set Y} {r : Y} (hn : ∀ x ∈ C, r * x * r⁻¹ ∈ C)
    (hi : ∀ x ∈ C, r * (r * x * r⁻¹) * r⁻¹ = x) : Equiv.Perm C :=
  Function.Involutive.toPerm (fun x : C => ⟨r * x * r⁻¹, hn x x.2⟩)
    (fun x => Subtype.ext (hi x x.2))

theorem Oset_eq_image (C : Set Y) (k : ℕ) :
    Oset C k = (fun F : Set C => Subtype.val '' F) '' fixSets (inducedPerms C) k := by
  ext G
  constructor
  · rintro ⟨r, hn, hi, rfl, hk⟩
    refine ⟨{x | osetPerm hn hi x = x}, ⟨osetPerm hn hi, ⟨r, fun x => rfl⟩, ?_, rfl, ?_⟩, ?_⟩
    · exact Equiv.ext fun x => Subtype.ext (hi x x.2)
    · rw [← hk, ← Set.ncard_image_of_injective _ Subtype.val_injective]
      congr 1
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.2, congrArg Subtype.val hx⟩
      · rintro ⟨hy, hyr⟩
        exact ⟨⟨y, hy⟩, Subtype.ext hyr, rfl⟩
    · ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.2, congrArg Subtype.val hx⟩
      · rintro ⟨hy, hyr⟩
        exact ⟨⟨y, hy⟩, Subtype.ext hyr, rfl⟩
  · rintro ⟨F, ⟨σ, ⟨r, hr⟩, hσ, rfl, hk⟩, rfl⟩
    refine ⟨r, fun x hx => ?_, fun x hx => ?_, ?_, ?_⟩
    · rw [← hr ⟨x, hx⟩]
      exact (σ ⟨x, hx⟩).2
    · have h1 : (σ (σ ⟨x, hx⟩) : Y) = x := by rw [← Equiv.Perm.mul_apply, hσ]; rfl
      rw [hr, hr] at h1
      exact h1
    · ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.2, (hr x).symm.trans (congrArg Subtype.val hx)⟩
      · rintro ⟨hy, hyr⟩
        exact ⟨⟨y, hy⟩, Subtype.ext ((hr ⟨y, hy⟩).trans hyr), rfl⟩
    · rw [Set.ncard_image_of_injective _ Subtype.val_injective]
      exact hk

theorem ncard_Oset (C : Set Y) (k : ℕ) :
    (Oset C k).ncard = (fixSets (inducedPerms C) k).ncard := by
  rw [Oset_eq_image]
  refine Set.ncard_image_of_injective _ fun F F' h => ?_
  exact Set.image_injective.2 Subtype.val_injective h

theorem Oset_conj (g : Y) (C : Set Y) (k : ℕ) :
    Oset ((fun x => g * x * g⁻¹) '' C) k = (fun G => (fun x => g * x * g⁻¹) '' G) '' Oset C k := by
  have hinj : Function.Injective fun x : Y => g * x * g⁻¹ := fun x y h => by
    simpa using h
  ext G
  constructor
  · rintro ⟨r, hn, hi, rfl, hk⟩
    set r' := g⁻¹ * r * g
    have hconj : ∀ x, g * (r' * x * r'⁻¹) * g⁻¹ = r * (g * x * g⁻¹) * r⁻¹ := fun x => by
      simp only [r']; group
    refine ⟨{x | x ∈ C ∧ r' * x * r'⁻¹ = x}, ⟨r', fun x hx => ?_, fun x hx => ?_, rfl, ?_⟩, ?_⟩
    · obtain ⟨y, hy, hyx⟩ := hn _ ⟨x, hx, rfl⟩
      have : y = r' * x * r'⁻¹ := hinj (hyx.trans (hconj x).symm)
      rw [← this]
      exact hy
    · apply hinj
      dsimp only
      rw [hconj, hconj]
      exact hi _ ⟨x, hx, rfl⟩
    · rw [← hk, ← Set.ncard_image_of_injective _ hinj]
      congr 1
      ext y
      constructor
      · rintro ⟨x, ⟨hx, hxr⟩, rfl⟩
        refine ⟨⟨x, hx, rfl⟩, ?_⟩
        dsimp only
        rw [← hconj, hxr]
      · rintro ⟨⟨x, hx, rfl⟩, hyr⟩
        refine ⟨x, ⟨hx, hinj ?_⟩, rfl⟩
        dsimp only at hyr ⊢
        rw [hconj, hyr]
    · ext y
      constructor
      · rintro ⟨x, ⟨hx, hxr⟩, rfl⟩
        refine ⟨⟨x, hx, rfl⟩, ?_⟩
        dsimp only
        rw [← hconj, hxr]
      · rintro ⟨⟨x, hx, rfl⟩, hyr⟩
        refine ⟨x, ⟨hx, hinj ?_⟩, rfl⟩
        dsimp only at hyr ⊢
        rw [hconj, hyr]
  · rintro ⟨G', ⟨r, hn, hi, rfl, hk⟩, rfl⟩
    set r' := g * r * g⁻¹
    have hconj : ∀ x, r' * (g * x * g⁻¹) * r'⁻¹ = g * (r * x * r⁻¹) * g⁻¹ := fun x => by
      simp only [r']; group
    refine ⟨r', ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      dsimp only
      rw [hconj]
      exact ⟨_, hn x hx, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      dsimp only
      rw [hconj, hconj, hi x hx]
    · ext y
      constructor
      · rintro ⟨x, ⟨hx, hxr⟩, rfl⟩
        refine ⟨⟨x, hx, rfl⟩, ?_⟩
        dsimp only
        rw [hconj, hxr]
      · rintro ⟨⟨x, hx, rfl⟩, hyr⟩
        refine ⟨x, ⟨hx, hinj ?_⟩, rfl⟩
        dsimp only at hyr ⊢
        rw [← hconj, hyr]
    · rw [Set.ncard_image_of_injective _ hinj]
      exact hk

theorem ncard_Oset_conj (g : Y) (C : Set Y) (k : ℕ) :
    (Oset ((fun x => g * x * g⁻¹) '' C) k).ncard = (Oset C k).ncard := by
  have hinj : Function.Injective fun x : Y => g * x * g⁻¹ := fun x y h => by
    simpa using h
  rw [Oset_conj]
  exact Set.ncard_image_of_injective _ (Set.image_injective.2 hinj)

end Group

theorem false_of_double_count {X : Type*} {B : Set X} (hBf : B.Finite) (hB : B.ncard = 25)
    (𝓑 : Set (Set X)) (hsub : ∀ F ∈ 𝓑, F ⊆ B) (h9 : ∀ F ∈ 𝓑, F.ncard = 9)
    (hdeg : ∀ b ∈ B, {F | F ∈ 𝓑 ∧ b ∈ F}.ncard = 759) : False := by
  classical
  have h𝓑f : 𝓑.Finite := (Set.Finite.finite_subsets hBf).subset fun F hF => hsub F hF
  set s := hBf.toFinset
  set t := h𝓑f.toFinset
  have hm : ∀ a ∈ s, (t.bipartiteAbove (fun a F => a ∈ F) a).card = 759 := by
    intro a ha
    rw [Set.Finite.mem_toFinset] at ha
    rw [← hdeg a ha, ← Set.ncard_coe_finset]
    congr 1
    ext F
    simp [Finset.bipartiteAbove, t]
  have hn : ∀ F ∈ t, (s.bipartiteBelow (fun a F => a ∈ F) F).card = 9 := by
    intro F hF
    rw [Set.Finite.mem_toFinset] at hF
    rw [← h9 F hF, ← Set.ncard_coe_finset]
    congr 1
    ext a
    simp only [Finset.bipartiteBelow, Finset.coe_filter, Set.Finite.mem_toFinset, s]
    exact ⟨fun h => h.2, fun h => ⟨hsub F hF h, h⟩⟩
  have h := Finset.card_mul_eq_card_mul (fun a F => a ∈ F) hm hn
  have hs : s.card = 25 := by rw [← hB, ← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
  rw [hs] at h
  omega

end CFSG.Fischer
