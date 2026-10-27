module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCoreS
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow
public import CFSG.LocalAnalysis.AGLEmbeddingD2.FiveCover
public import CFSG.LieType.SeitzGeneration.ExcPlaneFamilies
public import CFSG.HardMathSupport.Foote.FamilyReduction.ClassicalFive

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint.Multiplier
open CFSG.RankThree.PartTwo.Sec4.Census (tableOrder card_center_dvd_tableOrder
  three_dvd_tableOrder_cases)
open CFSG.AGLEmbeddingD2.FiveCover (five_le_dvd_tableOrder_cases)

private theorem false_of_dvd_tableOrder_of_ne {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {t : StatedLieTag} {n p' f : ℕ} (hchar : p ≠ p')
    (ht : t ≠ .PSL) (hu : t ≠ .PSU) (h6 : t ≠ .E6) (ht6 : t ≠ .twistedE6)
    (h : p ∣ tableOrder t n p' f) : False := by
  rcases CFSG.LieType.SeitzGeneration.eq_three_or_five_le hp hp2 with rfl | h5
  · rcases three_dvd_tableOrder_cases h with
      ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, hp3, -⟩ | ⟨-, -, hp3, -⟩ |
        ⟨-, -, hp3, -⟩ | ⟨-, -, hp3, -⟩
    · exact ht h
    · exact hu h
    · exact h6 h
    · exact ht6 h
    · exact hchar hp3.symm
    · exact hchar hp3.symm
    · exact hchar hp3.symm
    · exact hchar hp3.symm
  · rcases five_le_dvd_tableOrder_cases hp h5 h with ⟨h, -⟩ | ⟨h, -⟩
    · exact ht h
    · exact hu h

private theorem multIdx_A (hGA : CFSG.Open.GriessAllModelsStatement) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A r q).Valid) {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group)
    (hchar : p ≠ (TauCeti.LieTypeIndex.A r q).characteristic)
    (hZ : IsPGroup p (Subgroup.center K)) (hne : Subgroup.center K ≠ ⊥) :
    p ∣ r + 1 ∧ p ∣ q.card - 1 := by
  have hnt : Nontrivial (Subgroup.center K) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  have hpc : p ∣ Nat.card (Subgroup.center K) :=
    (pGroup_card_of_dvd hp hZ hnt (dvd_refl _)).1
  have hK' : CFSG.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hK
  have hm : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .PSL (r + 1) q.p q.exponent :=
    CFSG.Models.lieModel_A r q hv e
  have hdvd : p ∣ tableOrder .PSL (r + 1) q.p q.exponent :=
    hpc.trans (card_center_dvd_tableOrder hGA hK' (MulEquiv.refl _) hm)
  have hchar' : p ≠ q.p := by
    rwa [TauCeti.LieTypeIndex.characteristic_A] at hchar
  rcases CFSG.LieType.SeitzGeneration.eq_three_or_five_le hp hp2 with rfl | h5
  · rcases three_dvd_tableOrder_cases hdvd with
      ⟨-, h1, h2⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, hp3, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact ⟨h1, by simpa only [TauCeti.PrimePower.card_def] using h2⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact (hchar' hp3.symm).elim
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  · rcases five_le_dvd_tableOrder_cases hp h5 hdvd with ⟨-, h1, h2⟩ | ⟨h, -⟩
    · exact ⟨h1, by simpa only [TauCeti.PrimePower.card_def] using h2⟩
    · exact absurd h (by decide)

private theorem multIdx_twistedA (hGA : CFSG.Open.GriessAllModelsStatement) (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group)
    (hchar : p ≠ (TauCeti.LieTypeIndex.twistedA r q).characteristic)
    (hZ : IsPGroup p (Subgroup.center K)) (hne : Subgroup.center K ≠ ⊥) :
    p ∣ r + 1 ∧ p ∣ q.card + 1 := by
  have hnt : Nontrivial (Subgroup.center K) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  have hpc : p ∣ Nat.card (Subgroup.center K) :=
    (pGroup_card_of_dvd hp hZ hnt (dvd_refl _)).1
  have hK' : CFSG.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hK
  have hm : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .PSU (r + 1) q.p q.exponent :=
    lieModel_twistedA' r q hv e
  have hdvd : p ∣ tableOrder .PSU (r + 1) q.p q.exponent :=
    hpc.trans (card_center_dvd_tableOrder hGA hK' (MulEquiv.refl _) hm)
  have hchar' : p ≠ q.p := by
    rwa [TauCeti.LieTypeIndex.characteristic_twistedA] at hchar
  rcases CFSG.LieType.SeitzGeneration.eq_three_or_five_le hp hp2 with rfl | h5
  · rcases three_dvd_tableOrder_cases hdvd with
      ⟨h, -⟩ | ⟨-, h1, h2⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, hp3, -⟩
    · exact absurd h (by decide)
    · exact ⟨h1, by simpa only [TauCeti.PrimePower.card_def] using h2⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact (hchar' hp3.symm).elim
  · rcases five_le_dvd_tableOrder_cases hp h5 hdvd with ⟨h, -⟩ | ⟨-, h1, h2⟩
    · exact absurd h (by decide)
    · exact ⟨h1, by simpa only [TauCeti.PrimePower.card_def] using h2⟩

private theorem multIdx_E6 (hGA : CFSG.Open.GriessAllModelsStatement) (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.E6 q).Valid) {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group)
    (hchar : p ≠ (TauCeti.LieTypeIndex.E6 q).characteristic)
    (hZ : IsPGroup p (Subgroup.center K)) (hne : Subgroup.center K ≠ ⊥) :
    p = 3 ∧ 3 ∣ q.card - 1 := by
  have hnt : Nontrivial (Subgroup.center K) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  have hpc : p ∣ Nat.card (Subgroup.center K) :=
    (pGroup_card_of_dvd hp hZ hnt (dvd_refl _)).1
  have hK' : CFSG.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hK
  have hm : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .E6 0 q.p q.exponent :=
    CFSG.Models.lieModel_of_namesTag (t := .E6) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E6 q, hv⟩ ⟨rfl, rfl⟩ e
  have hdvd : p ∣ tableOrder .E6 0 q.p q.exponent :=
    hpc.trans (card_center_dvd_tableOrder hGA hK' (MulEquiv.refl _) hm)
  rcases CFSG.LieType.SeitzGeneration.eq_three_or_five_le hp hp2 with rfl | h5
  · rcases three_dvd_tableOrder_cases hdvd with
      ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h1⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact ⟨rfl, by simpa only [TauCeti.PrimePower.card_def] using h1⟩
    all_goals exact absurd h (by decide)
  · rcases five_le_dvd_tableOrder_cases hp h5 hdvd with ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)

private theorem multIdx_twistedE6 (hGA : CFSG.Open.GriessAllModelsStatement) (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group)
    (hchar : p ≠ (TauCeti.LieTypeIndex.twistedE6 q).characteristic)
    (hZ : IsPGroup p (Subgroup.center K)) (hne : Subgroup.center K ≠ ⊥) :
    p = 3 ∧ 3 ∣ q.card + 1 := by
  have hnt : Nontrivial (Subgroup.center K) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  have hpc : p ∣ Nat.card (Subgroup.center K) :=
    (pGroup_card_of_dvd hp hZ hnt (dvd_refl _)).1
  have hK' : CFSG.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hK
  have hm : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .twistedE6 0 q.p q.exponent :=
    CFSG.Models.lieModel_of_namesTag (t := .twistedE6) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.twistedE6 q, hv⟩ ⟨rfl, rfl⟩ e
  have hdvd : p ∣ tableOrder .twistedE6 0 q.p q.exponent :=
    hpc.trans (card_center_dvd_tableOrder hGA hK' (MulEquiv.refl _) hm)
  rcases CFSG.LieType.SeitzGeneration.eq_three_or_five_le hp hp2 with rfl | h5
  · rcases three_dvd_tableOrder_cases hdvd with
      ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h1⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact ⟨rfl, by simpa only [TauCeti.PrimePower.card_def] using h1⟩
    all_goals exact absurd h (by decide)
  · rcases five_le_dvd_tableOrder_cases hp h5 hdvd with ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)

private theorem false_of_model_of_ne (hGA : CFSG.Open.GriessAllModelsStatement) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) (hpc : p ∣ Nat.card (Subgroup.center K))
    {t : StatedLieTag} {n p' f : ℕ}
    (hm : CFSG.Models.LieModel (K ⧸ Subgroup.center K) t n p' f)
    (hchar : p ≠ p') (ht : t ≠ .PSL) (hu : t ≠ .PSU) (h6 : t ≠ .E6)
    (ht6 : t ≠ .twistedE6) : False :=
  false_of_dvd_tableOrder_of_ne hp hp2 hchar ht hu h6 ht6
    (hpc.trans (card_center_dvd_tableOrder hGA hK (MulEquiv.refl _) hm))

theorem kd264MultLie_of_table (hGA : CFSG.Open.GriessAllModelsStatement) (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) : KD264MultLie p := by
  intro K _ _ hK d
  obtain ⟨i, hv⟩ := d
  rintro ⟨e⟩ hchar hZ hne
  have hnt : Nontrivial (Subgroup.center K) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  have hpc : p ∣ Nat.card (Subgroup.center K) :=
    (pGroup_card_of_dvd hp hZ hnt (dvd_refl _)).1
  have hK' : CFSG.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hK
  cases i with
  | A r q => exact multIdx_A hGA p hp hp2 hv hK e hchar hZ hne
  | twistedA r q => exact multIdx_twistedA hGA p hp hp2 hv hK e hchar hZ hne
  | B r q =>
    have hchar' : p ≠ q.p := by rwa [TauCeti.LieTypeIndex.characteristic_B] at hchar
    rcases CFSG.Models.lieModel_B r q hv e with hm | hm
    · exact (false_of_model_of_ne hGA hp hp2 hK' hpc hm hchar' (by decide) (by decide)
        (by decide) (by decide)).elim
    · exact (false_of_model_of_ne hGA hp hp2 hK' hpc hm hchar' (by decide) (by decide)
        (by decide) (by decide)).elim
  | C r q =>
    have hchar' : p ≠ q.p := by rwa [TauCeti.LieTypeIndex.characteristic_C] at hchar
    exact (false_of_model_of_ne hGA hp hp2 hK' hpc (CFSG.Models.lieModel_C r q hv e) hchar'
      (by decide) (by decide) (by decide) (by decide)).elim
  | D r q =>
    have hchar' : p ≠ q.p := by rwa [TauCeti.LieTypeIndex.characteristic_D] at hchar
    exact (false_of_model_of_ne hGA hp hp2 hK' hpc (CFSG.Models.lieModel_D r q hv e) hchar'
      (by decide) (by decide) (by decide) (by decide)).elim
  | twistedD r q =>
    have hchar' : p ≠ q.p := by rwa [TauCeti.LieTypeIndex.characteristic_twistedD] at hchar
    exact (false_of_model_of_ne hGA hp hp2 hK' hpc (CFSG.Models.lieModel_twistedD r q hv e)
      hchar' (by decide) (by decide) (by decide) (by decide)).elim
  | E6 q => exact multIdx_E6 hGA p hp hp2 hv hK e hchar hZ hne
  | E7 q =>
    have hchar' : p ≠ q.p := by rwa [TauCeti.LieTypeIndex.characteristic_E7] at hchar
    exact (false_of_model_of_ne hGA hp hp2 hK' hpc
      (CFSG.Models.lieModel_of_namesTag (t := .E7) (p := q.p) (f := q.exponent)
        ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E7 q, hv⟩ ⟨rfl, rfl⟩ e) hchar'
      (by decide) (by decide) (by decide) (by decide)).elim
  | E8 q =>
    have hchar' : p ≠ q.p := by rwa [TauCeti.LieTypeIndex.characteristic_E8] at hchar
    exact (false_of_model_of_ne hGA hp hp2 hK' hpc
      (CFSG.Models.lieModel_of_namesTag (t := .E8) (p := q.p) (f := q.exponent)
        ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E8 q, hv⟩ ⟨rfl, rfl⟩ e) hchar'
      (by decide) (by decide) (by decide) (by decide)).elim
  | F4 q =>
    have hchar' : p ≠ q.p := by rwa [TauCeti.LieTypeIndex.characteristic_F4] at hchar
    exact (false_of_model_of_ne hGA hp hp2 hK' hpc
      (CFSG.Models.lieModel_of_namesTag (t := .F4) (p := q.p) (f := q.exponent)
        ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.F4 q, hv⟩ ⟨rfl, rfl⟩ e) hchar'
      (by decide) (by decide) (by decide) (by decide)).elim
  | G2 q =>
    have hchar' : p ≠ q.p := by rwa [TauCeti.LieTypeIndex.characteristic_G2] at hchar
    have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have h3q : 3 ≤ q.p ^ q.exponent := by
      simpa only [TauCeti.PrimePower.card_def] using hrange
    exact (false_of_model_of_ne hGA hp hp2 hK' hpc
      (CFSG.Models.lieModel_of_namesTag (t := .G2) (p := q.p) (f := q.exponent)
        ⟨q.prime_p, q.exponent_pos, rfl, h3q⟩ ⟨.G2 q, hv⟩ ⟨rfl, rfl⟩ e) hchar'
      (by decide) (by decide) (by decide) (by decide)).elim
  | twistedE6 q => exact multIdx_twistedE6 hGA p hp hp2 hv hK e hchar hZ hne
  | trialityD4 q =>
    have hchar' : p ≠ q.p := by rwa [TauCeti.LieTypeIndex.characteristic_trialityD4] at hchar
    exact (false_of_model_of_ne hGA hp hp2 hK' hpc
      (CFSG.Models.lieModel_of_namesTag (t := .trialityD4) (p := q.p) (f := q.exponent)
        ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.trialityD4 q, hv⟩ ⟨rfl, rfl⟩ e) hchar'
      (by decide) (by decide) (by decide) (by decide)).elim
  | suzuki m =>
    have hchar' : p ≠ 2 := by rwa [TauCeti.LieTypeIndex.characteristic_suzuki] at hchar
    have hm1 : 1 ≤ m := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    exact (false_of_model_of_ne hGA hp hp2 hK' hpc
      (CFSG.Models.lieModel_of_namesTag (t := .twistedB2) (p := 2) (f := 2 * m + 1)
        ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.suzuki m, hv⟩
        ⟨rfl, rfl⟩ e) hchar' (by decide) (by decide) (by decide) (by decide)).elim
  | reeG2 m =>
    have hchar' : p ≠ 3 := by rwa [TauCeti.LieTypeIndex.characteristic_reeG2] at hchar
    have hm1 : 1 ≤ m := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    exact (false_of_model_of_ne hGA hp hp2 hK' hpc
      (CFSG.Models.lieModel_of_namesTag (t := .twistedG2) (p := 3) (f := 2 * m + 1)
        ⟨Nat.prime_three, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.reeG2 m, hv⟩
        ⟨rfl, rfl⟩ e) hchar' (by decide) (by decide) (by decide) (by decide)).elim
  | reeF4 m =>
    have hchar' : p ≠ 2 := by rwa [TauCeti.LieTypeIndex.characteristic_reeF4] at hchar
    have hm1 : 1 ≤ m := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    exact (false_of_model_of_ne hGA hp hp2 hK' hpc
      (CFSG.Models.lieModel_of_namesTag (t := .twistedF4) (p := 2) (f := 2 * m + 1)
        ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.reeF4 m, hv⟩
        ⟨rfl, rfl⟩ e) hchar' (by decide) (by decide) (by decide) (by decide)).elim
  | tits =>
    have hchar' : p ≠ 2 := by rwa [TauCeti.LieTypeIndex.characteristic_tits] at hchar
    exact (false_of_model_of_ne hGA hp hp2 hK' hpc
      (CFSG.Models.lieModel_of_namesTag (t := .Tits) (p := 2) (f := 1)
        ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩ ⟨.tits, hv⟩ ⟨rfl, rfl⟩ e) hchar'
      (by decide) (by decide) (by decide) (by decide)).elim

theorem kd264MultLie_holds (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : KD264MultLie p :=
  kd264MultLie_of_table CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement p hp
    hp2

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
