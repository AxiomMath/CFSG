module

public import CFSG.LocalAnalysis.Replacement.ThompsonSubgroup
public import Mathlib.GroupTheory.PGroup
import CFSG.LocalAnalysis.Replacement.ReplacementStep
import Mathlib.Data.Set.Finite.Lemmas

public section

namespace CFSG

namespace GlaubermanReplacement

open Subgroup

theorem forall_le_or_exists_le_normalizer {p : ℕ} (hp : Nat.Prime p) (hodd : Odd p)
    {S : Type*} [Group S] [Finite S] (hS : IsPGroup p S) (B : Subgroup S) (hB : B.Normal)
    (hclass : ⁅B, B⁆ ≤ (center B).map B.subtype) (hBZ : ⁅B, B⁆ ≤ thompsonCenter S) :
    (∀ A ∈ maxOrderAbelianSubgroups S, B ≤ A) ∨
      ∃ A ∈ maxOrderAbelianSubgroups S, ¬ B ≤ A ∧ B ≤ normalizer (A : Set S) := by
  refine or_iff_not_imp_left.2 fun h ↦ ?_
  push Not at h
  have : Finite (Subgroup S) := Finite.of_injective _ SetLike.coe_injective
  obtain ⟨A, ⟨hA, hBA⟩, hmax⟩ := Set.exists_max_image
    {A | A ∈ maxOrderAbelianSubgroups S ∧ ¬ B ≤ A} (fun A ↦ Nat.card ↥(B ⊓ normalizer (A : Set S)))
    (Set.toFinite _) h
  refine ⟨A, hA, hBA, by_contra fun hBA' ↦ ?_⟩
  obtain ⟨A', hA', hBA'', hlt⟩ := exists_replacement hp hodd hS hB hclass hBZ hA hBA'
  exact (card_lt_of_lt hlt).not_ge (hmax A' ⟨hA', hBA''⟩)

end GlaubermanReplacement

end CFSG
