module

public import CFSG.GH74.GLS.C3.Layer1.BkS4Wr
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

section Aux

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Back
open scoped commutatorElement

variable {G : Type} [Group G]

theorem IsD8.exists_central_sq {P : Subgroup G} (h : IsD8 P) :
    ∃ z ∈ P, z ≠ 1 ∧ z * z = 1 ∧ (∀ p ∈ P, p * z = z * p) ∧
      (∀ w ∈ P, (∀ p ∈ P, p * w = w * p) → w = 1 ∨ w = z) ∧
      ∀ g ∈ P, g * g ≠ 1 → g * g = z := by
  obtain ⟨z, hzP, hz1, hzz, hzc, hzu⟩ := h.exists_z
  refine ⟨z, hzP, hz1, hzz, hzc, hzu, fun g hg hg2 => ?_⟩
  obtain ⟨e⟩ := h
  have hsqc : ∀ g h : DihedralGroup 4, (g * g) * h = h * (g * g) := by decide
  have hcen : ∀ p ∈ P, p * (g * g) = (g * g) * p := by
    intro p hp
    have h1 : (⟨p, hp⟩ : ↥P) * (⟨g, hg⟩ * ⟨g, hg⟩) = (⟨g, hg⟩ * ⟨g, hg⟩) * ⟨p, hp⟩ := by
      apply e.injective
      rw [map_mul, map_mul, map_mul, map_mul]
      exact (hsqc _ _).symm
    exact congrArg Subtype.val h1
  rcases hzu (g * g) (P.mul_mem hg hg) hcen with h1 | h1
  · exact absurd h1 hg2
  · exact h1

theorem two_le_pRank_of_isD8 [Finite G] {P : Subgroup G} (h : IsD8 P) : 2 ≤ pRank 2 ↥P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hzP, -, hz2, -⟩ := h.exists_z
  obtain ⟨D, hDP, hDel, hD4, -⟩ := h.exists_four_containing hzP hz2
  have h1 := card_eq_two_pow_pRank hDel
  rw [hD4] at h1
  have h2 : (2 : ℕ) ^ 2 = 2 ^ pRank 2 ↥D := by simpa using h1
  have h3 : pRank 2 ↥D = 2 := (Nat.pow_right_injective le_rfl h2).symm
  have := pRank_mono' hDP
  omega

end Aux

end CFSG.GH74.GLS.C3.Layer1.Bk
