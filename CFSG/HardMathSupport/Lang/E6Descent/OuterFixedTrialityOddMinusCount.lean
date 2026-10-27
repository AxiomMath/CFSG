module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnAsm
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Positivity.Finset

public section

open scoped Pointwise

namespace CFSG.GH74.BNPair

open CFSG.GH74.GLS.SP

namespace RankTwoSystem

variable {X : Type*} [Group X] {D : RankTwoSystem X 3} {θ : X ≃* X}

theorem IsPolarity.card_foldFix [Finite X] (hθ : D.IsPolarity θ) {c₀ : X}
    (hc₀ : c₀ ∈ dc D.B D.N D.w₀) (hc₀f : θ c₀ = c₀) :
    Nat.card ↥(foldFix θ) =
      Nat.card ↥(D.B ⊓ foldFix θ) * (1 + Nat.card ↥(D.U ⊓ foldFix θ)) := by
  have hmemB : ∀ g : ↥(foldFix θ), g ∈ D.B.subgroupOf (foldFix θ) ↔ (g : X) ∈ D.B :=
    fun g => Subgroup.mem_subgroupOf
  have hmemU : ∀ g : ↥(foldFix θ), g ∈ D.U.subgroupOf (foldFix θ) ↔ (g : X) ∈ D.U :=
    fun g => Subgroup.mem_subgroupOf
  have hw₀ : D.w₀ ≠ 1 := fun h => by
    have := D.rank2.dih.altWord_inj (i := 3) (j := 0) le_rfl (by norm_num)
      (h.trans (altWord_zero D.w₁ D.w₂).symm)
    omega
  have hc₀B : c₀ ∉ D.B := fun h => hw₀ ((D.bw_eq hc₀).symm.trans (D.bw_eq (mem_dc_one.2 h)))
  let c : ↥(foldFix θ) := ⟨c₀, hc₀f⟩
  have hcB : c ∉ D.B.subgroupOf (foldFix θ) := fun h => hc₀B ((hmemB c).1 h)
  have hUB : D.U.subgroupOf (foldFix θ) ≤ D.B.subgroupOf (foldFix θ) := fun g hg =>
    (hmemB g).2 (D.U_le_B ((hmemU g).1 hg))
  have hcell : ∀ g : ↥(foldFix θ), g ∈ D.B.subgroupOf (foldFix θ) ∨
      ∃ b ∈ D.B.subgroupOf (foldFix θ), ∃ u ∈ D.U.subgroupOf (foldFix θ), g = b * c * u := by
    intro g
    rcases hθ.fixed_mem_B_or_top (mem_foldFix.1 g.2) with hg | hg
    · exact Or.inl ((hmemB g).2 hg)
    · obtain ⟨b, hb, hbf, u, hu, huf, hgbu⟩ :=
        hθ.top_decomp hc₀ hg hc₀f (mem_foldFix.1 g.2)
      exact Or.inr ⟨⟨b, hbf⟩, (hmemB _).2 hb, ⟨u, huf⟩, (hmemU _).2 hu, Subtype.ext hgbu⟩
  have hinj : ∀ b ∈ D.B.subgroupOf (foldFix θ), ∀ b' ∈ D.B.subgroupOf (foldFix θ),
      ∀ u ∈ D.U.subgroupOf (foldFix θ), ∀ u' ∈ D.U.subgroupOf (foldFix θ),
      b * c * u = b' * c * u' → b = b' ∧ u = u' := by
    intro b hb b' hb' u hu u' hu' h
    obtain ⟨h1, h2⟩ := top_unique hc₀ ((hmemB b).1 hb) ((hmemB b').1 hb') ((hmemU u).1 hu)
      ((hmemU u').1 hu') (congrArg Subtype.val h)
    exact ⟨Subtype.ext h1, Subtype.ext h2⟩
  have hindex := index_eq_one_add_card_of_cells (D.B.subgroupOf (foldFix θ))
    (D.U.subgroupOf (foldFix θ)) hUB c hcB hcell hinj
  have hBc : Nat.card ↥(D.B.subgroupOf (foldFix θ)) = Nat.card ↥(D.B ⊓ foldFix θ) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right)).toEquiv
  have hUc : Nat.card ↥(D.U.subgroupOf (foldFix θ)) = Nat.card ↥(D.U ⊓ foldFix θ) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right)).toEquiv
  rw [← hBc, ← hUc, ← hindex]
  exact (Subgroup.card_mul_index (D.B.subgroupOf (foldFix θ))).symm

end RankTwoSystem

end CFSG.GH74.BNPair
