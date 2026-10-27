module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294DeltaOrth
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294DeltaLinear
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294DeltaClassical
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294DeltaExc

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThree.PartTwo.Census

section


theorem deltaTowerAt_lie (d : TauCeti.ValidLieTypeIndex) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hA : ∀ (m : ℕ) (q : TauCeti.PrimePower), d.1 = .A m q → 2 ≤ m →
      ¬ p ∣ Nat.gcd (m + 1) (q.card - 1))
    (hU : ∀ (m : ℕ) (q : TauCeti.PrimePower), d.1 = .twistedA m q →
      ¬ p ∣ Nat.gcd (m + 1) (q.card + 1)) :
    DeltaTowerAt p (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  cases d with
  | A m q =>
    have hm1 : 1 ≤ m := hrange.1
    rcases Nat.lt_or_ge m 2 with h1 | hm2
    · obtain rfl : m = 1 := by omega
      exact DeltaTowerAt.of_catA_one hv
    · exact DeltaTowerAt.of_catA hm2 hv hp (hA m q rfl hm2)
  | twistedA m q => exact DeltaTowerAt.of_cat_twistedA hv hp (hU m q rfl)
  | B r q =>
    have hr2 : 2 ≤ r := hrange.1
    rcases Nat.lt_or_ge r 3 with hr3 | hr3
    · obtain rfl : r = 2 := by omega
      exact DeltaTowerAt.of_catB_two hv
    · by_cases hq2 : q.p = 2
      · exact DeltaTowerAt.of_catB_even hr3 hq2 hv
      · exact DeltaTowerAt.of_statedOdd
          (statedClassicalModel_typeB_odd r q hv hq2 hr3 (MulEquiv.refl _))
  | C r q => exact DeltaTowerAt.of_catC hv
  | D r q =>
    have hr4 : 4 ≤ r := hrange
    rcases Nat.eq_or_lt_of_le hr4 with h4 | h5
    · subst h4
      exact DeltaTowerAt.of_statedPlus_four
        (statedClassicalModel_typeD 4 q hv (MulEquiv.refl _)) hp hp5
    · exact DeltaTowerAt.of_statedPlus_five h5
        (statedClassicalModel_typeD r q hv (MulEquiv.refl _)) hp hp5
  | twistedD r q =>
    exact DeltaTowerAt.of_statedMinus
      (statedClassicalModel_typeTwistedD r q hv (MulEquiv.refl _)) hp hp5
  | E6 q => exact DeltaTowerAt.of_catE6 hv hp hp5
  | E7 q => exact DeltaTowerAt.of_catE7 hv hp hp5
  | E8 q => exact DeltaTowerAt.of_catE8 hv
  | F4 q => exact DeltaTowerAt.of_catF4 hv
  | G2 q => exact DeltaTowerAt.of_catG2 hv
  | twistedE6 q => exact DeltaTowerAt.of_cat_twistedE6 hv hp hp5
  | trialityD4 q => exact DeltaTowerAt.of_cat_trialityD4 hv
  | suzuki m => exact DeltaTowerAt.of_cat_suzuki hv
  | reeG2 m => exact DeltaTowerAt.of_cat_reeG2 hv
  | reeF4 m => exact DeltaTowerAt.of_cat_reeF4 hv
  | tits => exact DeltaTowerAt.of_cat_tits hv hp (by omega)

end

section


theorem kdInndiagP5_holds : KDInndiagP5 := by
  refine kdInndiagP5_of_at ?_
  intro p hp h5 L _ _ hs hnab hcat hnl
  obtain ⟨i, ⟨e⟩⟩ := hcat
  refine DeltaTowerAt.kdInndiagAt (DeltaTowerAt.of_mulEquiv e ?_)
  cases i with
  | cyclic r hr =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _))
  | alternating n hn => exact DeltaTowerAt.of_alternating hn hp h5
  | sporadic s => exact DeltaTowerAt.of_sporadic s hp h5
  | lie d =>
    refine deltaTowerAt_lie d hp h5 ?_ ?_
    · intro m q hd _
      obtain ⟨d', hv⟩ := d
      change d' = .A m q at hd
      subst hd
      exact not_dvd_gcd_of_not_isLinearOrUnitaryAt_A hv e hnl
    · intro m q hd
      obtain ⟨d', hv⟩ := d
      change d' = .twistedA m q at hd
      subst hd
      exact not_dvd_gcd_of_not_isLinearOrUnitaryAt_twistedA hv e hnl

end

end CFSG.LocalAnalysis.RankFourTheoremC
