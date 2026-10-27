module

public import CFSG.HardMathSupport.Malle.E27Lie.Cross.AssemblyIn

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.ExcLeaf

open TauCeti
open CFSG.HardMathSupport.Malle.E27Lie (InnerLeaf)
open CFSG.HardMathSupport.Curtis.UnitaryLevi (InnerCoveredExcCrossOpen)

@[expose] def IdxExc (τ : PrimePower → LieTypeIndex) (r : ℕ) (i : LieTypeIndex) : Prop :=
  ∃ q : PrimePower, q.p ≠ 3 ∧ q.card % 3 = r ∧ i = τ q

@[expose] def IdxTrialityD4 (i : LieTypeIndex) : Prop :=
  ∃ q : PrimePower, q.p ≠ 3 ∧ i = .trialityD4 q

theorem card_mod_three_of_p_ne {q : PrimePower} (hq : q.p ≠ 3) :
    q.card % 3 = 1 ∨ q.card % 3 = 2 := by
  have hp : q.p.Prime := q.prime_p
  have h3 : ¬ 3 ∣ q.card := by
    rw [PrimePower.card_def]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    exact hq this.symm
  omega

theorem innerLeaf_excOpen_of_cells
    (hF41 : InnerLeaf (IdxExc .F4 1)) (hF42 : InnerLeaf (IdxExc .F4 2))
    (hE61 : InnerLeaf (IdxExc .E6 1)) (hE62 : InnerLeaf (IdxExc .E6 2))
    (h2E61 : InnerLeaf (IdxExc .twistedE6 1)) (h2E62 : InnerLeaf (IdxExc .twistedE6 2))
    (hE71 : InnerLeaf (IdxExc .E7 1)) (hE72 : InnerLeaf (IdxExc .E7 2))
    (hE81 : InnerLeaf (IdxExc .E8 1)) (hE82 : InnerLeaf (IdxExc .E8 2))
    (h3D4 : InnerLeaf IdxTrialityD4) : InnerLeaf InnerCoveredExcCrossOpen := by
  intro X _ _ K R T z h hz d hd e
  obtain ⟨q, hq, hi⟩ := hd
  have hr := card_mod_three_of_p_ne hq
  rcases hi with hi | hi | hi | hi | hi | hi
  · rcases hr with hr | hr
    · exact hF41 h hz d ⟨q, hq, hr, hi⟩ e
    · exact hF42 h hz d ⟨q, hq, hr, hi⟩ e
  · rcases hr with hr | hr
    · exact hE61 h hz d ⟨q, hq, hr, hi⟩ e
    · exact hE62 h hz d ⟨q, hq, hr, hi⟩ e
  · rcases hr with hr | hr
    · exact h2E61 h hz d ⟨q, hq, hr, hi⟩ e
    · exact h2E62 h hz d ⟨q, hq, hr, hi⟩ e
  · rcases hr with hr | hr
    · exact hE71 h hz d ⟨q, hq, hr, hi⟩ e
    · exact hE72 h hz d ⟨q, hq, hr, hi⟩ e
  · rcases hr with hr | hr
    · exact hE81 h hz d ⟨q, hq, hr, hi⟩ e
    · exact hE82 h hz d ⟨q, hq, hr, hi⟩ e
  · exact h3D4 h hz d ⟨q, hq, hi⟩ e

end CFSG.HardMathSupport.Curtis.Coordinator.ExcLeaf
