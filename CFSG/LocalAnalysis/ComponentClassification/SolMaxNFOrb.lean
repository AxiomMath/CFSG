module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNFOrbDisc

public section

namespace CFSG.ComponentClassification.SolMax

open Equiv NFOrb

theorem altPairFamilySupportInput_holds :
    ∀ (ι Ω : Type) [Fintype ι] [DecidableEq ι] [Fintype Ω] [DecidableEq Ω] (t : ι → ι → Perm Ω),
      5 ≤ Fintype.card ι → Fintype.card Ω ≤ 2 * Fintype.card ι + 3 →
      (∀ c d e, t c d * t d e = t c e) → (∀ c d, t c d = t d c) →
      (∀ τ ∈ alternatingGroup ι, ∃ π : Perm Ω, ∀ c d, π * t c d * π⁻¹ = t (τ c) (τ d)) →
      ∀ c d, (t c d).support.card ≤ 4 := by
  intro ι Ω _ _ _ _ t h5 hΩ ht hs hequiv a b
  classical
  have hclass : ∀ ω, (∀ c d, t c d ω = ω) ∨ ∃ c, IsCenter t ω c := by
    intro ω
    by_contra hbad
    rw [not_or, not_forall, not_exists] at hbad
    obtain ⟨⟨p, hp⟩, hnc⟩ := hbad
    rw [not_forall] at hp
    obtain ⟨q, hpq⟩ := hp
    by_cases hdisc : ∀ c d, c ≠ d → t c d ω ≠ ω
    · exact false_of_discrete ht hs h5 hΩ hequiv hdisc
    push Not at hdisc
    obtain ⟨d, e, hde, hfix⟩ := hdisc
    by_cases h3 : ∃ x, t p x ω ≠ ω ∧ t q x ω ≠ ω
    · obtain ⟨x, hpx, hqx⟩ := h3
      exact false_of_three ht hs h5 hΩ hequiv hpq hpx hqx hde hfix
    push Not at h3
    have hcut : ∀ x, t p x ω = ω ∨ t q x ω = ω := fun x => by
      by_cases h : t p x ω = ω
      · exact Or.inl h
      · exact Or.inr (h3 x h)
    have hqp : t q p ω ≠ ω := by rw [hs]; exact hpq
    have hcut' : ∀ x, t q x ω = ω ∨ t p x ω = ω := fun x => (hcut x).symm
    have hsecond : ∀ u v : ι, t u v ω ≠ ω → (∀ x, t u x ω = ω ∨ t v x ω = ω) →
        ∃ u', u' ≠ u ∧ t u u' ω = ω := by
      intro u v huv hcutuv
      by_contra hno
      push Not at hno
      apply hnc u
      refine ⟨fun x y hx hy => ?_, fun x hx => hno x hx⟩
      have hxv := (hcutuv x).resolve_left (hno x hx)
      have hyv := (hcutuv y).resolve_left (hno y hy)
      exact pair_fix_trans ht (by rw [hs]; exact hxv) hyv
    obtain ⟨p', hp'1, hp'2⟩ := hsecond p q hpq hcut
    obtain ⟨q', hq'1, hq'2⟩ := hsecond q p hqp hcut'
    exact false_of_cut ht hs h5 hΩ hequiv hpq hcut hp'1 hp'2 hq'1 hq'2
  have hsub : (t a b).support ⊆ (Finset.univ.filter fun ω => IsCenter t ω a) ∪
      (Finset.univ.filter fun ω => IsCenter t ω b) := by
    intro ω hω
    rw [Perm.mem_support] at hω
    rcases hclass ω with h0 | ⟨c, hc⟩
    · exact absurd (h0 a b) hω
    · by_cases hca : c = a
      · subst hca
        simp [hc]
      by_cases hcb : c = b
      · subst hcb
        simp [hc]
      · exact absurd (hc.1 a b (Ne.symm hca) (Ne.symm hcb)) hω
  calc (t a b).support.card ≤ ((Finset.univ.filter fun ω => IsCenter t ω a) ∪
        (Finset.univ.filter fun ω => IsCenter t ω b)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ.filter fun ω => IsCenter t ω a).card +
        (Finset.univ.filter fun ω => IsCenter t ω b).card := Finset.card_union_le _ _
    _ ≤ 2 + 2 := add_le_add (card_center_le_two h5 hΩ hequiv a)
        (card_center_le_two h5 hΩ hequiv b)

end CFSG.ComponentClassification.SolMax
