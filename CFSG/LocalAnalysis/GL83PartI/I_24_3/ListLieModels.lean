module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models

public section

namespace GL83.I243.CoverList

open TauCeti CFSG.Assembly.LowTwoRank CFSG.Models
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier (lieModel_typeA lieModel_lie
  lieModel_of_classical)

theorem exists_lieModel_spec (d : ValidLieTypeIndex) :
    ∃ (t : StatedLieTag) (n p f : ℕ), LieModel (CFSGIndex.lie d).Group t n p f ∧
      p = d.1.characteristic ∧ 0 < f ∧
      (t = .PSL → ∃ (r : ℕ) (q : PrimePower), d.1 = .A r q) ∧
      (t = .PSU → ∃ (r : ℕ) (q : PrimePower), d.1 = .twistedA r q) := by
  obtain ⟨d, hv⟩ := d
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  cases d with
  | A r q =>
    exact ⟨_, _, _, _, lieModel_typeA r q hv, (LieTypeIndex.characteristic_A _ _).symm,
      q.exponent_pos, fun _ => ⟨r, q, rfl⟩, (fun h => nomatch h)⟩
  | twistedA r q =>
    exact ⟨_, _, _, _, lieModel_of_classical
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv (MulEquiv.refl _)),
      (LieTypeIndex.characteristic_twistedA _ _).symm, q.exponent_pos, (fun h => nomatch h),
      fun _ => ⟨r, q, rfl⟩⟩
  | B r q =>
    have hr : 2 ≤ r := hrange.1
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · exact ⟨_, _, _, _, lieModel_of_classical
        (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv (MulEquiv.refl _)),
        (LieTypeIndex.characteristic_B _ _).symm, q.exponent_pos, (fun h => nomatch h),
        (fun h => nomatch h)⟩
    · by_cases hp : q.p = 2
      · exact ⟨_, _, _, _, lieModel_of_classical
          (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp hr3
            (MulEquiv.refl _)),
          (LieTypeIndex.characteristic_B _ _).symm, q.exponent_pos, (fun h => nomatch h),
          (fun h => nomatch h)⟩
      · exact ⟨_, _, _, _, lieModel_of_classical
          (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp hr3
            (MulEquiv.refl _)),
          (LieTypeIndex.characteristic_B _ _).symm, q.exponent_pos, (fun h => nomatch h),
          (fun h => nomatch h)⟩
  | C r q =>
    exact ⟨_, _, _, _, lieModel_of_classical
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv (MulEquiv.refl _)),
      (LieTypeIndex.characteristic_C _ _).symm, q.exponent_pos, (fun h => nomatch h),
      (fun h => nomatch h)⟩
  | D r q =>
    exact ⟨_, _, _, _, lieModel_of_classical
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv (MulEquiv.refl _)),
      (LieTypeIndex.characteristic_D _ _).symm, q.exponent_pos, (fun h => nomatch h),
      (fun h => nomatch h)⟩
  | twistedD r q =>
    exact ⟨_, _, _, _, lieModel_of_classical
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv (MulEquiv.refl _)),
      (LieTypeIndex.characteristic_twistedD _ _).symm, q.exponent_pos, (fun h => nomatch h),
      (fun h => nomatch h)⟩
  | E6 q =>
    exact ⟨_, _, _, _, lieModel_lie (t := .E6) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E6 q, hv⟩
      ⟨rfl, rfl⟩, (LieTypeIndex.characteristic_E6 _).symm, q.exponent_pos,
      (fun h => nomatch h), (fun h => nomatch h)⟩
  | E7 q =>
    exact ⟨_, _, _, _, lieModel_lie (t := .E7) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E7 q, hv⟩
      ⟨rfl, rfl⟩, (LieTypeIndex.characteristic_E7 _).symm, q.exponent_pos,
      (fun h => nomatch h), (fun h => nomatch h)⟩
  | E8 q =>
    exact ⟨_, _, _, _, lieModel_lie (t := .E8) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E8 q, hv⟩
      ⟨rfl, rfl⟩, (LieTypeIndex.characteristic_E8 _).symm, q.exponent_pos,
      (fun h => nomatch h), (fun h => nomatch h)⟩
  | F4 q =>
    exact ⟨_, _, _, _, lieModel_lie (t := .F4) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.F4 q, hv⟩
      ⟨rfl, rfl⟩, (LieTypeIndex.characteristic_F4 _).symm, q.exponent_pos,
      (fun h => nomatch h), (fun h => nomatch h)⟩
  | G2 q =>
    have h3q : 3 ≤ q.p ^ q.exponent := by simpa only [PrimePower.card_def] using hrange
    exact ⟨_, _, _, _, lieModel_lie (t := .G2) ⟨q.prime_p, q.exponent_pos, rfl, h3q⟩ ⟨.G2 q, hv⟩
      ⟨rfl, rfl⟩, (LieTypeIndex.characteristic_G2 _).symm, q.exponent_pos,
      (fun h => nomatch h), (fun h => nomatch h)⟩
  | twistedE6 q =>
    exact ⟨_, _, _, _, lieModel_lie (t := .twistedE6) ⟨q.prime_p, q.exponent_pos, rfl⟩
      ⟨.twistedE6 q, hv⟩ ⟨rfl, rfl⟩, (LieTypeIndex.characteristic_twistedE6 _).symm,
      q.exponent_pos, (fun h => nomatch h), (fun h => nomatch h)⟩
  | trialityD4 q =>
    exact ⟨_, _, _, _, lieModel_lie (t := .trialityD4) ⟨q.prime_p, q.exponent_pos, rfl⟩
      ⟨.trialityD4 q, hv⟩ ⟨rfl, rfl⟩, (LieTypeIndex.characteristic_trialityD4 _).symm,
      q.exponent_pos, (fun h => nomatch h), (fun h => nomatch h)⟩
  | suzuki m =>
    have hm1 : 1 ≤ m := hrange
    exact ⟨_, _, _, _, lieModel_lie (t := .twistedB2) (p := 2) (f := 2 * m + 1)
      ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.suzuki m, hv⟩ ⟨rfl, rfl⟩,
      (LieTypeIndex.characteristic_suzuki _).symm, by omega, (fun h => nomatch h),
      (fun h => nomatch h)⟩
  | reeG2 m =>
    have hm1 : 1 ≤ m := hrange
    exact ⟨_, _, _, _, lieModel_lie (t := .twistedG2) (p := 3) (f := 2 * m + 1)
      ⟨Nat.prime_three, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.reeG2 m, hv⟩ ⟨rfl, rfl⟩,
      (LieTypeIndex.characteristic_reeG2 _).symm, by omega, (fun h => nomatch h),
      (fun h => nomatch h)⟩
  | reeF4 m =>
    have hm1 : 1 ≤ m := hrange
    exact ⟨_, _, _, _, lieModel_lie (t := .twistedF4) (p := 2) (f := 2 * m + 1)
      ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.reeF4 m, hv⟩ ⟨rfl, rfl⟩,
      (LieTypeIndex.characteristic_reeF4 _).symm, by omega, (fun h => nomatch h),
      (fun h => nomatch h)⟩
  | tits =>
    exact ⟨_, _, _, _, lieModel_lie (t := .Tits) (p := 2) (f := 1)
      ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩ ⟨.tits, hv⟩ ⟨rfl, rfl⟩,
      LieTypeIndex.characteristic_tits.symm, Nat.one_pos, (fun h => nomatch h),
      (fun h => nomatch h)⟩

end GL83.I243.CoverList
