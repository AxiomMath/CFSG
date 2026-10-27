module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitFCCA7Base

public section

namespace CFSG.ComponentClassification.FooteLit.FCC

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.Foote5
open CFSG.ClassicalInvolution.Hat2A7 (A7)
open CFSG.ComponentClassification.FooteLit.Aut5A7

@[expose] def s45 : Finset (Fin 7) := {0, 1, 2, 3, 6}

@[expose] def m45 : Subgroup A7 := (alternatingGroup.ofSubtype s45).range

theorem mem_m45 (g : A7) : g ∈ m45 ↔ (g : Perm (Fin 7)) 4 = 4 ∧ (g : Perm (Fin 7)) 5 = 5 := by
  rw [m45, alternatingGroup.mem_range_ofSubtype_iff]
  constructor
  · intro h
    have hs : ∀ x : Fin 7, (g : Perm (Fin 7)) x ≠ x → x ∈ s45 :=
      fun x hx => h (Perm.mem_support.mpr hx)
    refine ⟨?_, ?_⟩
    · by_contra h4
      exact absurd (hs 4 h4) (by decide)
    · by_contra h5
      exact absurd (hs 5 h5) (by decide)
  · rintro ⟨h4, h5⟩ x hx
    rw [Perm.mem_support] at hx
    have hx4 : x ≠ 4 := fun h => hx (by subst h; exact h4)
    have hx5 : x ≠ 5 := fun h => hx (by subst h; exact h5)
    have key : ∀ y : Fin 7, y ≠ 4 → y ≠ 5 → y ∈ s45 := by decide
    exact key x hx4 hx5

theorem isSimpleGroup_m45 : IsSimpleGroup m45 := by
  have e5 : (s45 : Type) ≃ Fin 5 := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; decide)
  have : IsSimpleGroup (alternatingGroup (s45 : Type)) := (Equiv.altCongrHom e5).isSimpleGroup
  exact (MonoidHom.ofInjective (alternatingGroup.ofSubtype_injective (s := s45))).symm.isSimpleGroup

theorem card_m45 : Nat.card m45 = 60 := by
  rw [m45, ← Nat.card_congr
    (MonoidHom.ofInjective (alternatingGroup.ofSubtype_injective (s := s45))).toEquiv]
  have : Nontrivial (s45 : Type) := ⟨⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide⟩⟩
  have h := two_mul_nat_card_alternatingGroup (α := (s45 : Type))
  have h5 : Nat.card (s45 : Type) = 5 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    decide
  rw [Nat.card_perm, h5, show Nat.factorial 5 = 120 by decide] at h
  omega

@[expose] def c012 : A7 := ⟨swap 0 1 * swap 1 2, by rw [Perm.mem_alternatingGroup]; decide⟩
@[expose] def c123 : A7 := ⟨swap 1 2 * swap 2 3, by rw [Perm.mem_alternatingGroup]; decide⟩
@[expose] def c236 : A7 := ⟨swap 2 3 * swap 3 6, by rw [Perm.mem_alternatingGroup]; decide⟩
@[expose] def t0123 : A7 := ⟨swap 0 1 * swap 2 3, by rw [Perm.mem_alternatingGroup]; decide⟩
@[expose] def t0213 : A7 := ⟨swap 0 2 * swap 1 3, by rw [Perm.mem_alternatingGroup]; decide⟩

theorem eq_of_commute_m45 {π : Perm (Fin 7)} (h1 : π * (c012 : Perm (Fin 7)) = c012 * π)
    (h2 : π * (c123 : Perm (Fin 7)) = c123 * π) (h3 : π * (c236 : Perm (Fin 7)) = c236 * π) :
    π = 1 ∨ π = swap 4 5 := by
  have key : ∀ x y : Fin 7, ((c012 : Perm (Fin 7)) y = y ↔ (c012 : Perm (Fin 7)) x = x) →
      ((c123 : Perm (Fin 7)) y = y ↔ (c123 : Perm (Fin 7)) x = x) →
      ((c236 : Perm (Fin 7)) y = y ↔ (c236 : Perm (Fin 7)) x = x) →
      y = x ∨ (x = 4 ∧ y = 5) ∨ (x = 5 ∧ y = 4) := by decide
  have hπx : ∀ x, π x = x ∨ (x = 4 ∧ π x = 5) ∨ (x = 5 ∧ π x = 4) := fun x =>
    key x (π x) (fixed_iff_of_commute h1 x) (fixed_iff_of_commute h2 x)
      (fixed_iff_of_commute h3 x)
  have hval : ∀ x : Fin 7, x ≠ 4 → x ≠ 5 → π x = x := fun x hx4 hx5 => by
    rcases hπx x with h | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hx4
    · exact absurd h hx5
  have h45 : (π 4 = 4 ∧ π 5 = 5) ∨ (π 4 = 5 ∧ π 5 = 4) := by
    rcases hπx 4 with h4 | ⟨-, h4⟩ | ⟨h, -⟩
    · rcases hπx 5 with h5 | ⟨h, -⟩ | ⟨-, h5⟩
      · exact Or.inl ⟨h4, h5⟩
      · exact absurd h (by decide)
      · exact absurd (π.injective (h5.trans h4.symm)) (by decide)
    · rcases hπx 5 with h5 | ⟨h, -⟩ | ⟨-, h5⟩
      · exact absurd (π.injective (h5.trans h4.symm)) (by decide)
      · exact absurd h (by decide)
      · exact Or.inr ⟨h4, h5⟩
    · exact absurd h (by decide)
  rcases h45 with ⟨h4, h5⟩ | ⟨h4, h5⟩
  · left
    ext x
    by_cases hx4 : x = 4
    · subst hx4
      simp [h4]
    · by_cases hx5 : x = 5
      · subst hx5
        simp [h5]
      · simp [hval x hx4 hx5]
  · right
    ext x
    by_cases hx4 : x = 4
    · subst hx4
      simp [h4]
    · by_cases hx5 : x = 5
      · subst hx5
        simp [h5]
      · rw [hval x hx4 hx5, swap_apply_of_ne_of_ne hx4 hx5]

theorem fcc_swap45 : FCConcl A7 (autPerm.symm (swap 4 5)) m45 := by
  refine ⟨fun g hg => ?_, ?_, fun N hNM hNn hN1 => ?_, fun α hα => ?_⟩
  ·
    rw [mem_m45] at hg
    show g ∈ MonoidHom.eqLocus (autPerm.symm (swap 4 5)).toMonoidHom (MonoidHom.id A7)
    rw [mem_eqLocus_iff, mul_swap_eq_swap_mul, hg.1, hg.2]
  ·
    have h1 := two_mul_card_eqLocus_le (τ := swap (4 : Fin 7) 5) (by decide)
    rw [Perm.nat_card_centralizer, cycleType_swap45] at h1
    have h2 := le_trans h1 (by decide : _ ≤ 240)
    rw [card_m45]
    omega
  ·
    have := isSimpleGroup_m45
    have hn : (N.subgroupOf m45).Normal := ⟨fun n hn g => by
      rw [mem_subgroupOf] at hn ⊢
      simpa using hNn g g.2 n hn⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf m45) with h | h
    · exfalso
      apply hN1
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hNM hx⟩ : m45) ∈ N.subgroupOf m45 := hx
      rw [h, mem_bot] at hx'
      exact mem_bot.mpr (congrArg Subtype.val hx')
    · have hle : m45 ≤ N := subgroupOf_eq_top.mp h
      refine ⟨t0123, hle ((mem_m45 _).mpr (by decide)), t0213, hle ((mem_m45 _).mpr (by decide)),
        by decide, by decide, by decide, by decide, by decide, by decide⟩
  ·
    have hπ := eq_of_commute_m45 (commute_of_fix (hα c012 ((mem_m45 _).mpr (by decide))))
      (commute_of_fix (hα c123 ((mem_m45 _).mpr (by decide))))
      (commute_of_fix (hα c236 ((mem_m45 _).mpr (by decide))))
    rcases hπ with h | h
    · left
      apply autPerm.injective
      rw [h, map_one]
    · right
      apply autPerm.injective
      rw [h, MulEquiv.apply_symm_apply]

end CFSG.ComponentClassification.FooteLit.FCC
