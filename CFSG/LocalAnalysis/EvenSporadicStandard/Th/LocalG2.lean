module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalData2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalIn2

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {G : Type} [Group G]

theorem ThLocalWitness2.toLocalIn2 {L : Subgroup G} {B₀ A₀ Aa₀ : Subgroup ↥L} {b₀ : ↥L}
    (W : ThLocalWitness2 B₀ A₀ Aa₀ b₀) :
    ThLocalIn2 (B₀.map L.subtype) (A₀.map L.subtype) (Aa₀.map L.subtype) (b₀ : G) := by
  have hmem : ∀ K : Subgroup ↥L, ∀ x : G, x ∈ K.map L.subtype ↔ ∃ h : x ∈ L, (⟨x, h⟩ : L) ∈ K :=
    fun K x => by
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · rintro ⟨h, hx⟩
        exact ⟨⟨x, h⟩, hx, rfl⟩
  refine ⟨Subgroup.map_mono W.Aa_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨hxL, hx0⟩ := (hmem _ _).1 hx
    obtain ⟨hyL, hy0⟩ := (hmem _ _).1 hy
    exact congrArg Subtype.val (W.Aa_comm _ hx0 _ hy0)
  · rw [Subgroup.card_map_of_injective L.subtype_injective]
    exact W.Aa_card
  · intro x hx
    obtain ⟨hxL, hx0⟩ := (hmem _ _).1 hx
    simpa using congrArg Subtype.val (W.Aa_exp _ hx0)
  · intro y
    constructor
    · intro hy
      obtain ⟨hyL, hy0⟩ := (hmem _ _).1 hy
      obtain ⟨x₀, hx₀, hxy⟩ := (W.A_eq_sq _).1 hy0
      exact ⟨(x₀ : G), ⟨x₀, hx₀, rfl⟩, by simpa using congrArg Subtype.val hxy⟩
    · rintro ⟨x, hx, hxy⟩
      obtain ⟨hxL, hx0⟩ := (hmem _ _).1 hx
      refine (hmem _ _).2 ⟨by rw [← hxy]; exact L.pow_mem hxL 2, ?_⟩
      refine (W.A_eq_sq _).2 ⟨⟨x, hxL⟩, hx0, Subtype.ext (by simpa using hxy)⟩
  · intro Y hYB hYc hYcard
    have hYL : Y ≤ L := fun y hy => by
      obtain ⟨h, _⟩ := (hmem _ _).1 (hYB hy)
      exact h
    set Y₀ : Subgroup ↥L := Y.comap L.subtype with hY₀
    have hmapY : Y₀.map L.subtype = Y := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, hYL hx⟩, hx, rfl⟩
    have h1 : Y₀ ≤ B₀ := fun y hy => by
      obtain ⟨_, hy0⟩ := (hmem _ _).1 (hYB hy)
      exact hy0
    have h2 : ∀ x ∈ Y₀, ∀ y ∈ Y₀, x * y = y * x := fun x hx y hy =>
      Subtype.ext (hYc _ hx _ hy)
    have h3 : Nat.card Y₀ = 2 ^ 8 := by
      rw [← hYcard, ← hmapY, Subgroup.card_map_of_injective L.subtype_injective]
    have h4 := W.Aa_unique Y₀ h1 h2 h3
    rw [← hmapY, h4]
  · exact (hmem _ _).2 ⟨b₀.2, by simpa using W.b_mem⟩
  · intro h
    obtain ⟨_, h0⟩ := (hmem _ _).1 h
    exact W.b_not_mem (by simpa using h0)
  · simpa using congrArg Subtype.val W.b_sq
  · intro x hx
    obtain ⟨hxL, hx0⟩ := (hmem _ _).1 hx
    simpa using congrArg Subtype.val (W.b_inv _ hx0)

end CFSG.EvenSporadicStandard.ThStd
