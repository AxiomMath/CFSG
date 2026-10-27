module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.ComponentClassification.SymmetricLocal

open Equiv

variable {Ω : Type*}

section Subtype

variable {p : Ω → Prop} [DecidablePred p]

theorem apply_iff_of_forall_not {g : Perm Ω} (hg : ∀ x, ¬ p x → g x = x) (x : Ω) :
    p (g x) ↔ p x := by
  constructor
  · intro h
    by_contra hx
    exact hx (hg x hx ▸ h)
  · intro hx
    by_contra h
    have hgx : g x = x := g.injective (hg (g x) h)
    rw [hgx] at h
    exact h hx

theorem ofSubtype_subtypePerm_of_forall_not {g : Perm Ω} (hg : ∀ x, ¬ p x → g x = x) :
    Perm.ofSubtype (g.subtypePerm (apply_iff_of_forall_not hg)) = g :=
  Perm.ofSubtype_subtypePerm _ fun x hx => by_contra fun h => hx (hg x h)

theorem mem_range_ofSubtype_iff {g : Perm Ω} :
    g ∈ (Perm.ofSubtype : Perm (Subtype p) →* Perm Ω).range ↔ ∀ x, ¬ p x → g x = x := by
  constructor
  · rintro ⟨f, rfl⟩ x hx
    exact Perm.ofSubtype_apply_of_not_mem f hx
  · intro hg
    exact ⟨_, ofSubtype_subtypePerm_of_forall_not hg⟩

theorem mem_map_ofSubtype_alternatingGroup_iff [Fintype Ω] [DecidableEq Ω]
    [Fintype (Subtype p)] {g : Perm Ω} :
    g ∈ (alternatingGroup (Subtype p)).map Perm.ofSubtype ↔
      (∀ x, ¬ p x → g x = x) ∧ Perm.sign g = 1 := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine ⟨fun x hx => Perm.ofSubtype_apply_of_not_mem f hx, ?_⟩
    rw [Perm.sign_ofSubtype]
    exact hf
  · rintro ⟨hg, hsign⟩
    refine ⟨g.subtypePerm (apply_iff_of_forall_not hg), ?_,
      ofSubtype_subtypePerm_of_forall_not hg⟩
    rw [SetLike.mem_coe, Perm.mem_alternatingGroup, ← Perm.sign_ofSubtype,
      ofSubtype_subtypePerm_of_forall_not hg]
    exact hsign

theorem card_map_ofSubtype_alternatingGroup [Fintype Ω] [DecidableEq Ω]
    [Fintype (Subtype p)] :
    Nat.card ((alternatingGroup (Subtype p)).map Perm.ofSubtype) =
      Nat.card (alternatingGroup (Subtype p)) :=
  Subgroup.card_map_of_injective Perm.ofSubtype_injective

end Subtype

theorem eq_alternatingGroup_or_eq_top [Fintype Ω] [DecidableEq Ω] {T : Subgroup (Perm Ω)}
    (hT : alternatingGroup Ω ≤ T) : T = alternatingGroup Ω ∨ T = ⊤ := by
  by_cases h : T ≤ alternatingGroup Ω
  · exact Or.inl (le_antisymm h hT)
  · right
    obtain ⟨g, hgT, hg⟩ := Set.not_subset.mp h
    have hg' : Perm.sign g = -1 := (Int.units_eq_one_or (Perm.sign g)).resolve_left hg
    refine eq_top_iff.mpr fun k _ => ?_
    rcases Int.units_eq_one_or (Perm.sign k) with hk | hk
    · exact hT hk
    · have hkg : k * g⁻¹ ∈ T := hT (by
        rw [Perm.mem_alternatingGroup, map_mul, map_inv, hk, hg']
        decide)
      simpa only [inv_mul_cancel_right] using mul_mem hkg hgT

theorem alternatingGroup_ne_top [Fintype Ω] [DecidableEq Ω] {a b : Ω} (hab : a ≠ b) :
    alternatingGroup Ω ≠ ⊤ := by
  intro h
  have hswap : swap a b ∈ alternatingGroup Ω := h ▸ Subgroup.mem_top _
  rw [Perm.mem_alternatingGroup, Perm.sign_swap hab] at hswap
  exact absurd hswap (by decide)

end CFSG.ComponentClassification.SymmetricLocal
