module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1Next
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiEndingMain
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1BranchEnd

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

section HKS

theorem SzC1Stage.false_of_eightCorner (h8 : SzEightCorner) {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {f a : ℕ} {t : G} {T : Subgroup G} {d : G} {V U U₁ : Subgroup G} {k : ℕ}
    (h : SzC1Stage G L f a t T d V U U₁ k) : False := by
  suffices key : ∀ (m : ℕ) (V U U₁ : Subgroup G) (k : ℕ), Nat.card G - Nat.card V = m →
      SzC1Stage G L f a t T d V U U₁ k → False from key _ V U U₁ k rfl h
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro V U U₁ k hm h
    obtain ⟨-, hμ, hlam, hν⟩ := h.nu_eq_zero_of_eightCorner h8
    obtain ⟨U', U₁', h'⟩ := h.next hμ hlam hν
    refine ih _ ?_ _ _ _ _ rfl h'
    have hq : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := h.ha; rw [h.hfa]; omega)
    have h1 : Nat.card V < Nat.card (U₁ ⊓ centralizer (szT₁ L T : Set G) : Subgroup G) := by
      rw [h.card, h'.card]
      exact Nat.pow_lt_pow_right hq (by omega)
    have h2 := Subgroup.card_le_card_group (U₁ ⊓ centralizer (szT₁ L T : Set G))
    omega

theorem szC1ExclusionData_of_eightCorner (h8 : SzEightCorner) : SzC1ExclusionData := by
  intro G _ _ L f t T a K _ _ _ d u v κ R₂ U U₁ h ha hfa hK hdL hodd hc hκ hR _ _ _ hTR _ _ hU
    hinv _
  exact (SzC1Stage.of_data h ha hfa hK hdL hodd hc hκ hR hTR hU hinv).false_of_eightCorner h8

end HKS

end CFSG.SeitzReduction.RankOne
