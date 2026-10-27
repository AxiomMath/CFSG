module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
import CFSG.LocalAnalysis.OddStandard.SporadicRow.ThreeDvdClassical
import CFSG.LocalAnalysis.OddStandard.SporadicRow.ThreeDvdExceptional
import CFSG.Adapters.TauCetiLieModels

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ CFSG.Assembly.LowTwoRank


theorem dvdAux_not_three_dvd_two_pow (f : ℕ) : ¬ 3 ∣ 2 ^ f := fun h => by
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  omega

theorem dvdAux_three_dvd_of_lieModel {G : Type} [Group G] {t : StatedLieTag} {n f : ℕ}
    (hL : CFSG.Blueprint.LieModel G t n 2 f)
    (ht : t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .G2 ∨ t = .F4 ∨
      t = .trialityD4) :
    3 ∣ Nat.card G := by
  have hadm := hL.admissible
  obtain ⟨-, hmul, -⟩ :=
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput G t n 2 f hadm hL
  have hq := dvdAux_not_three_dvd_two_pow f
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact CFSG.ComponentClassification.HarrisLit.T1.SporRow.three_dvd_of_classical hadm
      (by simp) hq hmul
  · exact CFSG.ComponentClassification.HarrisLit.T1.SporRow.three_dvd_of_classical hadm
      (by simp) hq hmul
  · exact CFSG.ComponentClassification.HarrisLit.T1.SporRow.three_dvd_of_classical hadm
      (by simp) hq hmul
  · exact CFSG.ComponentClassification.HarrisLit.T1.SporRow.three_dvd_of_classical hadm
      (by simp) hq hmul
  · exact CFSG.ComponentClassification.HarrisLit.T1.SporRow.three_dvd_of_exceptional hadm
      (by simp) hq hmul
  · exact CFSG.ComponentClassification.HarrisLit.T1.SporRow.three_dvd_of_exceptional hadm
      (by simp) hq hmul
  · exact CFSG.ComponentClassification.HarrisLit.T1.SporRow.three_dvd_of_exceptional hadm
      (by simp) hq hmul

theorem dvdAux_card_eq_numerator {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (hL : CFSG.Blueprint.LieModel G t n p f)
    (hd : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor t n (p ^ f) = 1) :
    Nat.card G = CFSG.ComponentClassification.CatLeaf.lieOrderNumerator t n (p ^ f) := by
  obtain ⟨-, hmul, -⟩ :=
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput G t n p f hL.admissible hL
  rw [hd, mul_one] at hmul
  exact hmul

theorem dvdAux_blueprint_of_models {G : Type} [Group G] {t : StatedLieTag} {n f : ℕ}
    (ht : t ∈ CFSG.Blueprint.classicalTags) (h : CFSG.Models.LieModel G t n 2 f) :
    CFSG.Blueprint.LieModel G t n 2 f :=
  CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel ht h

theorem dvd_card_of_bal207Index {p : ℕ} (d : TauCeti.ValidLieTypeIndex) (hd : Bal207Index p d.1) :
    p ∣ Nat.card (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  have hB := CFSG.TauCetiBridge.Even.chevalleyBridgesAll
  cases d with
  | B r q =>
    obtain ⟨rfl, h⟩ := hd
    have hp : q.p = 2 := by rcases h with ⟨⟨h, -⟩, -⟩ | ⟨⟨h, -⟩, -⟩ <;> exact h
    rcases CFSG.Models.lieModel_B r q hv (MulEquiv.refl _) with hL | hL
    · rw [hp] at hL
      exact dvdAux_three_dvd_of_lieModel
        (dvdAux_blueprint_of_models (by simp [CFSG.Blueprint.classicalTags]) hL) (by simp)
    · rw [hp] at hL
      exact absurd hL.1.2.2.2 (by simp)
  | twistedA r q =>
    obtain ⟨rfl, h⟩ := hd
    have hp : q.p = 2 := by
      rcases h with ⟨⟨h, -⟩ | ⟨h, -⟩, -⟩ | ⟨⟨h, -⟩, -⟩ <;> exact h
    have hL := CFSG.Models.lieModel_twistedA r q hv (MulEquiv.refl _)
    have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = 2 := by
      rw [← hp]
      exact TauCeti.LieTypeIndex.characteristic_twistedA r q
    rw [hc] at hL
    exact dvdAux_three_dvd_of_lieModel
      (dvdAux_blueprint_of_models (by simp [CFSG.Blueprint.classicalTags]) hL) (by simp)
  | D r q =>
    obtain ⟨rfl, h⟩ := hd
    have hp : q.p = 2 := by
      rcases h with ⟨⟨h, -⟩ | ⟨h, -⟩, -⟩ | ⟨⟨h, -⟩, -⟩ <;> exact h
    have hL := CFSG.Models.lieModel_D r q hv (MulEquiv.refl _)
    rw [hp] at hL
    exact dvdAux_three_dvd_of_lieModel
      (dvdAux_blueprint_of_models (by simp [CFSG.Blueprint.classicalTags]) hL) (by simp)
  | twistedD r q =>
    obtain ⟨rfl, h, -⟩ := hd
    have hp : q.p = 2 := by rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> exact h
    have hL := CFSG.Models.lieModel_twistedD r q hv (MulEquiv.refl _)
    rw [hp] at hL
    exact dvdAux_three_dvd_of_lieModel
      (dvdAux_blueprint_of_models (by simp [CFSG.Blueprint.classicalTags]) hL) (by simp)
  | trialityD4 q =>
    obtain ⟨rfl, hp, -⟩ := hd
    have hL : CFSG.Blueprint.LieModel (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group
        .trialityD4 0 2 q.exponent :=
      .inr (.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags],
        ⟨Nat.prime_two, q.exponent_pos, rfl⟩,
        CFSG.StandardType.ChevTwo.twistedChevalleyModel_of_bridge hB.trialityD4 q hv hp
          (MulEquiv.refl _)⟩)
    exact dvdAux_three_dvd_of_lieModel hL (by simp)
  | G2 q =>
    obtain ⟨rfl, hp, hf⟩ := hd
    have h3 : 3 ≤ 2 ^ q.exponent := by rw [hf]; norm_num
    have hL : CFSG.Blueprint.LieModel (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group
        .G2 0 2 q.exponent :=
      .inr (.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags],
        ⟨Nat.prime_two, q.exponent_pos, rfl, h3⟩,
        CFSG.StandardType.ChevTwo.untwistedChevalleyModel_of_bridge hB.g2 q hv hp
          (MulEquiv.refl _)⟩)
    exact dvdAux_three_dvd_of_lieModel hL (by simp)
  | F4 q =>
    obtain ⟨rfl, hp, -⟩ := hd
    have hL : CFSG.Blueprint.LieModel (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group
        .F4 0 2 q.exponent :=
      .inr (.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags],
        ⟨Nat.prime_two, q.exponent_pos, rfl⟩,
        CFSG.StandardType.ChevTwo.untwistedChevalleyModel_of_bridge hB.f4 q hv hp
          (MulEquiv.refl _)⟩)
    exact dvdAux_three_dvd_of_lieModel hL (by simp)
  | tits =>
    have hL : CFSG.Blueprint.LieModel (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group .Tits 0 2 1 :=
      .inr (.inr (.inl ⟨rfl, by simp [CFSG.Blueprint.reeTitsTags],
        CFSG.StandardType.ChevTwo.reeTitsModel_of_tits hv (MulEquiv.refl _)⟩))
    rw [dvdAux_card_eq_numerator hL rfl]
    rcases hd with rfl | rfl
    · show 3 ∣ 17971200
      norm_num
    · show 5 ∣ 17971200
      norm_num
  | suzuki m =>
    obtain ⟨rfl, rfl⟩ := hd
    have hL : CFSG.Blueprint.LieModel (TauCeti.CFSGIndex.lie ⟨.suzuki 2, hv⟩).Group
        .twistedB2 0 2 (2 * 2 + 1) :=
      .inr (.inr (.inr ⟨rfl, rfl,
        CFSG.StandardType.ChevTwo.suzukiModel_of_valid 2 hv (MulEquiv.refl _)⟩))
    rw [dvdAux_card_eq_numerator hL rfl]
    show 5 ∣ (2 ^ (2 * 2 + 1)) ^ 2 * ((2 ^ (2 * 2 + 1)) ^ 2 + 1) * (2 ^ (2 * 2 + 1) - 1)
    norm_num
  | reeF4 m =>
    obtain ⟨rfl, rfl⟩ := hd
    have hL : CFSG.Blueprint.LieModel (TauCeti.CFSGIndex.lie ⟨.reeF4 2, hv⟩).Group
        .twistedF4 0 2 (2 * 2 + 1) :=
      .inr (.inr (.inl ⟨rfl, by simp [CFSG.Blueprint.reeTitsTags],
        CFSG.StandardType.ChevTwo.reeTitsModel_of_reeF4 2 hv (MulEquiv.refl _)⟩))
    rw [dvdAux_card_eq_numerator hL rfl]
    show 5 ∣ (2 ^ (2 * 2 + 1)) ^ 12 * ((2 ^ (2 * 2 + 1)) ^ 6 + 1) * ((2 ^ (2 * 2 + 1)) ^ 4 - 1) *
      ((2 ^ (2 * 2 + 1)) ^ 3 + 1) * (2 ^ (2 * 2 + 1) - 1)
    norm_num
  | A r q => exact absurd hd (by simp [Bal207Index])
  | C r q => exact absurd hd (by simp [Bal207Index])
  | E6 q => exact absurd hd (by simp [Bal207Index])
  | E7 q => exact absurd hd (by simp [Bal207Index])
  | E8 q => exact absurd hd (by simp [Bal207Index])
  | twistedE6 q => exact absurd hd (by simp [Bal207Index])
  | reeG2 m => exact absurd hd (by simp [Bal207Index])

theorem bal207Dvd_holds : Bal207Dvd := by
  intro X _ _ p K _ _ hK
  obtain ⟨d, hd, ⟨e⟩⟩ := hK
  have h1 : p ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := by
    rw [Nat.card_congr e.toEquiv]
    exact dvd_card_of_bal207Index d hd
  exact h1.trans (Subgroup.card_quotient_dvd_card _)

end CFSG.HardMathSupport.Dickson.Bal207
