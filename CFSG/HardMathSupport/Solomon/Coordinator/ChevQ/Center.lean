module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Defs
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Models CFSG.Blueprint.Multiplier TauCeti
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
open CFSG.Open (GriessAllModelsStatement)

theorem exists_lieModel_char (d : ValidLieTypeIndex) :
    ∃ (t : StatedLieTag) (n p f : ℕ), p = d.1.characteristic ∧
      LieModel (CFSGIndex.lie d).Group t n p f := by
  obtain ⟨d, hv⟩ := d
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  cases d with
  | A r q => exact ⟨_, _, _, _, by simp, lieModel_typeA r q hv⟩
  | twistedA r q =>
    exact ⟨_, _, _, _, by simp, lieModel_of_classical
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv (MulEquiv.refl _))⟩
  | B r q =>
    have hr : 2 ≤ r := hrange.1
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · exact ⟨_, _, _, _, by simp, lieModel_of_classical
        (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv (MulEquiv.refl _))⟩
    · by_cases hp : q.p = 2
      · exact ⟨_, _, _, _, by simp, lieModel_of_classical
          (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp hr3
            (MulEquiv.refl _))⟩
      · exact ⟨_, _, _, _, by simp, lieModel_of_classical
          (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp hr3
            (MulEquiv.refl _))⟩
  | C r q =>
    exact ⟨_, _, _, _, by simp, lieModel_of_classical
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv (MulEquiv.refl _))⟩
  | D r q =>
    exact ⟨_, _, _, _, by simp, lieModel_of_classical
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv (MulEquiv.refl _))⟩
  | twistedD r q =>
    exact ⟨_, _, _, _, by simp, lieModel_of_classical
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv (MulEquiv.refl _))⟩
  | E6 q =>
    exact ⟨_, _, _, _, by simp, lieModel_lie (t := .E6) ⟨q.prime_p, q.exponent_pos, rfl⟩
      ⟨.E6 q, hv⟩ ⟨rfl, rfl⟩⟩
  | E7 q =>
    exact ⟨_, _, _, _, by simp, lieModel_lie (t := .E7) ⟨q.prime_p, q.exponent_pos, rfl⟩
      ⟨.E7 q, hv⟩ ⟨rfl, rfl⟩⟩
  | E8 q =>
    exact ⟨_, _, _, _, by simp, lieModel_lie (t := .E8) ⟨q.prime_p, q.exponent_pos, rfl⟩
      ⟨.E8 q, hv⟩ ⟨rfl, rfl⟩⟩
  | F4 q =>
    exact ⟨_, _, _, _, by simp, lieModel_lie (t := .F4) ⟨q.prime_p, q.exponent_pos, rfl⟩
      ⟨.F4 q, hv⟩ ⟨rfl, rfl⟩⟩
  | G2 q =>
    have h3q : 3 ≤ q.p ^ q.exponent := by simpa only [PrimePower.card_def] using hrange
    exact ⟨_, _, _, _, by simp, lieModel_lie (t := .G2) ⟨q.prime_p, q.exponent_pos, rfl, h3q⟩
      ⟨.G2 q, hv⟩ ⟨rfl, rfl⟩⟩
  | twistedE6 q =>
    exact ⟨_, _, _, _, by simp, lieModel_lie (t := .twistedE6) ⟨q.prime_p, q.exponent_pos, rfl⟩
      ⟨.twistedE6 q, hv⟩ ⟨rfl, rfl⟩⟩
  | trialityD4 q =>
    exact ⟨_, _, _, _, by simp, lieModel_lie (t := .trialityD4) ⟨q.prime_p, q.exponent_pos, rfl⟩
      ⟨.trialityD4 q, hv⟩ ⟨rfl, rfl⟩⟩
  | suzuki m =>
    have hm1 : 1 ≤ m := hrange
    exact ⟨_, _, _, _, by simp, lieModel_lie (t := .twistedB2) (p := 2) (f := 2 * m + 1)
      ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.suzuki m, hv⟩ ⟨rfl, rfl⟩⟩
  | reeG2 m =>
    have hm1 : 1 ≤ m := hrange
    exact ⟨_, _, _, _, by simp, lieModel_lie (t := .twistedG2) (p := 3) (f := 2 * m + 1)
      ⟨Nat.prime_three, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.reeG2 m, hv⟩ ⟨rfl, rfl⟩⟩
  | reeF4 m =>
    have hm1 : 1 ≤ m := hrange
    exact ⟨_, _, _, _, by simp, lieModel_lie (t := .twistedF4) (p := 2) (f := 2 * m + 1)
      ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.reeF4 m, hv⟩ ⟨rfl, rfl⟩⟩
  | tits =>
    exact ⟨_, _, _, _, by simp, lieModel_lie (t := .Tits) (p := 2) (f := 1)
      ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩ ⟨.tits, hv⟩ ⟨rfl, rfl⟩⟩

theorem card_le_center_torsion {L : Type} [Group L] [Finite L] {p : ℕ} {E : Subgroup L}
    (hE : CFSG.Open.IsElemAbelian p E) (hZ : E ≤ Subgroup.center L) :
    Nat.card E ≤ Nat.card {z : Subgroup.center L // z ^ p = 1} := by
  refine Nat.card_le_card_of_injective (fun x => ⟨⟨x.1, hZ x.2⟩, Subtype.ext (hE.2 x.1 x.2)⟩) ?_
  intro x y hxy
  exact Subtype.ext (congrArg (fun w : {z : Subgroup.center L // z ^ p = 1} => (w.1 : L)) hxy)

theorem center64_of_griess (hGA : GriessAllModelsStatement) : Center64 := by
  intro p hp hp2 Y _ _ hq _ d ⟨e⟩ hdp
  by_contra hlt
  have h2 : 2 ≤ CFSG.Open.pRank p (Subgroup.center Y) := by omega
  obtain ⟨E, hEZ, hEab, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (Subgroup.center Y)
  have hp2' : p ^ 2 ≤ Nat.card E := by
    rw [hEcard]
    exact Nat.pow_le_pow_right hp.pos h2
  have hcube := hp2'.trans (card_le_center_torsion hEab hEZ)
  obtain ⟨t, n, p', f, hp'd, hm⟩ := exists_lieModel_char d
  have hle := center_torsion_le hGA hq e hm hp
  have hp3 : 3 ≤ p := hp.two_le.lt_of_ne (Ne.symm hp2)
  by_cases hp5 : 5 ≤ p
  · have h1 := hcube.trans (hle.trans (torsBound_le_of_five_le hp5 t n p' f))
    have h2' : p < p ^ 2 := by nlinarith
    omega
  · have hp3' : p = 3 := by
      have := hp.eq_one_or_self_of_dvd 2
      interval_cases p <;> simp_all
    subst hp3'
    have h9 : 9 ≤ torsBound 3 t n p' f := by
      have : 3 ^ 2 ≤ torsBound 3 t n p' f := hcube.trans hle
      simpa using this
    obtain ⟨-, -, rfl, -⟩ := eq_psu_four_three_of_nine_le h9
    exact hdp hp'd

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
