module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSep

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

namespace TwinDisc



section Dich

variable {X : Type} [Group X] [Finite X] {Δ : Set (Subgroup X)}

theorem dstarAdj_of_commutes_gen (hΔ : HypOmegaGen Δ) {K J : Subgroup X} (hJ : J ∈ Δ) (hne : J ≠ K)
    (hc : Commutes J K) : dstarAdj Δ K J := by
  obtain ⟨R, hR, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := X)) (bot_le : ⊥ ≤ J)
  have hRset : R ∈ RSet Δ := mem_RSet_of_isSylow2In hJ hR
  obtain ⟨U, hUR, hUc, hcard⟩ := (Sec6Gen.isQuatSub_of_mem_RSet hΔ hRset).exists_cyclic_index_two
  have hrel : U.relIndex R = 2 := by
    have h1 := Subgroup.relIndex_mul_card U R
    rw [inf_eq_left.mpr hUR, hcard] at h1
    have hU0 : 0 < Nat.card U := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hU0 h1
  have hUJ : U ≤ J := hUR.trans hR.1
  exact ⟨hJ, Or.inl ⟨hJ, hne, U, ⟨R, hRset, hUR, hUc, hrel⟩, hUJ, fun u hu =>
    mem_normalizer_iff_conjSub_eq.mpr (conjSub_eq_of_mem_of_commutes (hUJ hu) hc)⟩⟩

theorem dichotomy_of_thm4RTwin {n : ℕ} (h4 : Thm4RTwinBelow 3 n) (hlt : Nat.card X < n)
    (hΔ : HypOmegaGen Δ) (h2 : ∀ J ∈ Δ, IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J))
    (hq : ∀ J ∈ Δ, ∀ P : Subgroup X, IsSylow2In P J →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (3 - 2))))
    (hA : ∀ L ∈ Δ, AEmpty Δ L) (hO : classicalInvolutionOddCore X = ⊥) {L : Subgroup X}
    (hL : L ∈ Δ) :
    (∀ M ∈ Δ, M ∈ dstarComp Δ L) ∨ (∀ M ∈ Δ, ∃ y : X, conjSub y L = M) := by
  have h4' := h4 X hlt Δ hΔ h2 hq hA hO
  by_cases hall : ∀ M ∈ Δ, ∃ y : X, conjSub y L = M
  · exact Or.inr hall
  left
  push Not at hall
  obtain ⟨M₀, hM₀, hM₀c⟩ := hall
  have hLM₀ : M₀ ≠ L := fun h => hM₀c 1 (by rw [conjSub_one, h])
  have hc0 : Commutes L M₀ := h4' L hL M₀ hM₀ (fun ⟨g, hg⟩ => hM₀c g hg)
  have hadj0 : dstarAdj Δ L M₀ := dstarAdj_of_commutes_gen hΔ hM₀ hLM₀ hc0.symm
  intro M hM
  by_cases hMc : ∃ y : X, conjSub y L = M
  · obtain ⟨y, rfl⟩ := hMc
    have hnot : ¬ ∃ g : X, conjSub g (conjSub y L) = M₀ := by
      rintro ⟨g, hg⟩
      exact hM₀c (g * y) (by rw [conjSub_mul]; exact hg)
    have hc1 : Commutes (conjSub y L) M₀ := h4' _ hM M₀ hM₀ hnot
    have hne : M₀ ≠ conjSub y L := fun h => hnot ⟨1, by rw [conjSub_one, h]⟩
    exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single hadj0)
      (dstarAdj_of_commutes_gen hΔ hM hne.symm hc1)
  · have hc : Commutes L M := h4' L hL M hM (fun ⟨g, hg⟩ => hMc ⟨g, hg⟩)
    have hne : M ≠ L := fun h => hMc ⟨1, by rw [conjSub_one, h]⟩
    exact Relation.ReflTransGen.single (dstarAdj_of_commutes_gen hΔ hM hne hc.symm)

end Dich

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
