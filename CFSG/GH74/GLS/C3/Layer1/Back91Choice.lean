module

public import CFSG.GH74.GLS.C3.Layer1.BackConj
public import CFSG.GH74.GLS.C3.Layer1.U1aSetup

public section

namespace CFSG.GH74.GLS.C3.Layer1.Back

open Subgroup CFSG CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem exists_best_conj {M T Q : Subgroup G} (hT : IsSylowOf 2 T M) (hQ : IsPGroup 2 ↥Q)
    (hne : ∃ g : G, g ∉ M ∧ 2 ≤ pRank 2 ↥(conjugate Q g ⊓ M)) :
    ∃ g : G, g ∉ M ∧ 2 ≤ pRank 2 ↥(conjugate Q g ⊓ M) ∧ conjugate Q g ⊓ M ≤ T ∧
      ∀ g' : G, g' ∉ M → 2 ≤ pRank 2 ↥(conjugate Q g' ⊓ M) →
        toLex (pRank 2 ↥(conjugate Q g' ⊓ M), Nat.card ↥(conjugate Q g' ⊓ M)) ≤
          toLex (pRank 2 ↥(conjugate Q g ⊓ M), Nat.card ↥(conjugate Q g ⊓ M)) := by
  let S : Set G := {g | g ∉ M ∧ 2 ≤ pRank 2 ↥(conjugate Q g ⊓ M)}
  let f : G → ℕ ×ₗ ℕ := fun g =>
    toLex (pRank 2 ↥(conjugate Q g ⊓ M), Nat.card ↥(conjugate Q g ⊓ M))
  obtain ⟨g₀, hg₀, hmax⟩ := Set.exists_max_image S f S.toFinite (by
    obtain ⟨g, hg⟩ := hne
    exact ⟨g, hg⟩)
  have hV : IsPGroup 2 ↥(conjugate Q g₀ ⊓ M) := (isPGroup_conjugate' hQ g₀).to_le inf_le_left
  obtain ⟨m, hmM, hm⟩ := U1a.exists_mem_conj_le hT (inf_le_right : conjugate Q g₀ ⊓ M ≤ M) hV
  have hconj : conjugate Q (g₀ * m) ⊓ M = conjugate (conjugate Q g₀ ⊓ M) m := by
    rw [conjugate_mul', conjugate_inf' _ _ m, conjugate_of_mem hmM]
  have hfeq : f (g₀ * m) = f g₀ := by
    show toLex (pRank 2 ↥(conjugate Q (g₀ * m) ⊓ M), Nat.card ↥(conjugate Q (g₀ * m) ⊓ M)) =
      toLex (pRank 2 ↥(conjugate Q g₀ ⊓ M), Nat.card ↥(conjugate Q g₀ ⊓ M))
    rw [hconj, pRank_conjugate', card_conjugate']
  have hnot : g₀ * m ∉ M := by
    intro h
    apply hg₀.1
    have := M.mul_mem h (M.inv_mem hmM)
    simpa using this
  refine ⟨g₀ * m, hnot, ?_, ?_, fun g' hg'1 hg'2 => ?_⟩
  · rw [hconj, pRank_conjugate']; exact hg₀.2
  · rw [hconj]
    intro x hx
    rw [mem_conjugate_iff'] at hx
    have := hm _ hx
    have e : m⁻¹ * (m * x * m⁻¹) * m = x := by group
    rwa [e] at this
  · have := hmax g' ⟨hg'1, hg'2⟩
    rw [← hfeq] at this
    exact this

end CFSG.GH74.GLS.C3.Layer1.Back
