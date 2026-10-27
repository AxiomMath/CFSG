module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models

public section

namespace CFSG.HardMathSupport.Timmesfeld.FieldBonus

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Models TauCeti
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

theorem exists_lieModel_valid (d : ValidLieTypeIndex) :
    ∃ (t : StatedLieTag) (n p f : ℕ), LieModel (CFSGIndex.lie d).Group t n p f ∧
      ¬(t = .PSL ∧ n = 2 ∧ p = 3 ∧ f = 2) := by
  obtain ⟨d, hv⟩ := d
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  cases d with
  | A r q =>
    refine ⟨_, _, _, _, lieModel_typeA r q hv, ?_⟩
    rintro ⟨-, h2, h3, h4⟩
    have hr : r = 1 := by omega
    have hnd := ((LieTypeIndex.valid_iff _).1 hv).2
    refine hnd ((LieTypeIndex.isDuplicateRepresentative_iff _).2 (Or.inl ⟨hr, Or.inr (Or.inr ?_)⟩))
    rw [PrimePower.card_def, h3, h4]
    norm_num
  | twistedA r q =>
    exact ⟨_, _, _, _, lieModel_of_classical
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv (MulEquiv.refl _)),
      by simp⟩
  | B r q =>
    have hr : 2 ≤ r := hrange.1
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · exact ⟨_, _, _, _, lieModel_of_classical
        (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv (MulEquiv.refl _)), by simp⟩
    · by_cases hp : q.p = 2
      · exact ⟨_, _, _, _, lieModel_of_classical
          (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp hr3
            (MulEquiv.refl _)), by simp⟩
      · exact ⟨_, _, _, _, lieModel_of_classical
          (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp hr3
            (MulEquiv.refl _)), by simp⟩
  | C r q =>
    exact ⟨_, _, _, _, lieModel_of_classical
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv (MulEquiv.refl _)), by simp⟩
  | D r q =>
    exact ⟨_, _, _, _, lieModel_of_classical
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv (MulEquiv.refl _)),
      by simp⟩
  | twistedD r q =>
    exact ⟨_, _, _, _, lieModel_of_classical
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv (MulEquiv.refl _)),
      by simp⟩
  | E6 q =>
    exact ⟨_, _, _, _, lieModel_lie (t := .E6) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E6 q, hv⟩
      ⟨rfl, rfl⟩, by simp⟩
  | E7 q =>
    exact ⟨_, _, _, _, lieModel_lie (t := .E7) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E7 q, hv⟩
      ⟨rfl, rfl⟩, by simp⟩
  | E8 q =>
    exact ⟨_, _, _, _, lieModel_lie (t := .E8) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E8 q, hv⟩
      ⟨rfl, rfl⟩, by simp⟩
  | F4 q =>
    exact ⟨_, _, _, _, lieModel_lie (t := .F4) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.F4 q, hv⟩
      ⟨rfl, rfl⟩, by simp⟩
  | G2 q =>
    have h3q : 3 ≤ q.p ^ q.exponent := by simpa only [PrimePower.card_def] using hrange
    exact ⟨_, _, _, _, lieModel_lie (t := .G2) ⟨q.prime_p, q.exponent_pos, rfl, h3q⟩ ⟨.G2 q, hv⟩
      ⟨rfl, rfl⟩, by simp⟩
  | twistedE6 q =>
    exact ⟨_, _, _, _, lieModel_lie (t := .twistedE6) ⟨q.prime_p, q.exponent_pos, rfl⟩
      ⟨.twistedE6 q, hv⟩ ⟨rfl, rfl⟩, by simp⟩
  | trialityD4 q =>
    exact ⟨_, _, _, _, lieModel_lie (t := .trialityD4) ⟨q.prime_p, q.exponent_pos, rfl⟩
      ⟨.trialityD4 q, hv⟩ ⟨rfl, rfl⟩, by simp⟩
  | suzuki m =>
    have hm1 : 1 ≤ m := hrange
    exact ⟨_, _, _, _, lieModel_lie (t := .twistedB2) (p := 2) (f := 2 * m + 1)
      ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.suzuki m, hv⟩ ⟨rfl, rfl⟩,
      by simp⟩
  | reeG2 m =>
    have hm1 : 1 ≤ m := hrange
    exact ⟨_, _, _, _, lieModel_lie (t := .twistedG2) (p := 3) (f := 2 * m + 1)
      ⟨Nat.prime_three, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.reeG2 m, hv⟩ ⟨rfl, rfl⟩,
      by simp⟩
  | reeF4 m =>
    have hm1 : 1 ≤ m := hrange
    exact ⟨_, _, _, _, lieModel_lie (t := .twistedF4) (p := 2) (f := 2 * m + 1)
      ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.reeF4 m, hv⟩ ⟨rfl, rfl⟩,
      by simp⟩
  | tits =>
    exact ⟨_, _, _, _, lieModel_lie (t := .Tits) (p := 2) (f := 1)
      ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩ ⟨.tits, hv⟩ ⟨rfl, rfl⟩, by simp⟩

end CFSG.HardMathSupport.Timmesfeld.FieldBonus
