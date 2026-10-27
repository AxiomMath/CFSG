module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.K144ILabel
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (FamExc)

private theorem exists_label_of_marking_aux {X : Type} [Group X] {P : GLALabel → Prop}
    (h : HasLabel X P) : ∃ lab : GLALabel, P lab ∧ HasLabel X (· = lab) := by
  obtain ⟨hX, lab, hlam, hraw⟩ := h
  obtain ⟨_, _, _, _, -, -, -, hS⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  exact ⟨lab, hS, hX, lab, hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩

private theorem not_famExc_of_markTag_classical {lab : GLALabel} {t : StatedLieTag}
    (ht : t ∈ CFSG.Blueprint.classicalTags) (h : CFSG.StandardType.markTag lab = t)
    (hc : CFSG.StandardType.markChar lab = 2) : ¬ FamExc lab := by
  rcases lab with ⟨tg, r, nn⟩
  have hmem : CFSG.StandardType.markTag ⟨tg, r, nn⟩ ∈ CFSG.Blueprint.classicalTags := by
    rw [h]; exact ht
  cases tg <;>
    simp [FamExc, CFSG.StandardType.markTag, CFSG.StandardType.markChar,
      CFSG.Blueprint.classicalTags] at hmem hc ⊢

private theorem exists_classical_lieModel {S : Type} [Group S] (D : TauCeti.ValidLieTypeIndex)
    (hchar : D.1.characteristic = 2) (hLie : I1419ClassLie D.1) (e : S ≃* D.Group) :
    ∃ (t : StatedLieTag) (n f : ℕ), t ∈ CFSG.Blueprint.classicalTags ∧
      CFSG.Blueprint.LieModel S t n 2 f := by
  obtain ⟨d, hv⟩ := D
  cases d with
  | A r q =>
    have hq : q.p = 2 := by simpa using hchar
    have h := CFSG.Models.lieModel_A r q hv e
    rw [hq] at h
    exact ⟨.PSL, r + 1, q.exponent, by decide,
      CFSG.Models.LieModel.toBlueprint (by decide) h⟩
  | twistedA r q =>
    have hc : TauCeti.ValidLieTypeIndex.characteristic
        ⟨TauCeti.LieTypeIndex.twistedA r q, hv⟩ = 2 := hchar
    have hf : TauCeti.ValidLieTypeIndex.fieldExponent
        ⟨TauCeti.LieTypeIndex.twistedA r q, hv⟩ = q.exponent :=
      TauCeti.LieTypeIndex.fieldExponent_twistedA r q
    have h := CFSG.Models.lieModel_twistedA r q hv e
    rw [hc, hf] at h
    exact ⟨.PSU, r + 1, q.exponent, by decide,
      CFSG.Models.LieModel.toBlueprint (by decide) h⟩
  | B r q =>
    have hq : q.p = 2 := by simpa using hchar
    rcases CFSG.Models.lieModel_B r q hv e with h | h
    · rw [hq] at h
      exact ⟨.PSp, r, q.exponent, by decide,
        CFSG.Models.LieModel.toBlueprint (by decide) h⟩
    · rw [hq] at h
      exact (h.1.2.2.2 rfl).elim
  | C r q =>
    have hq : q.p = 2 := by simpa using hchar
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    exact (hr.2 hq).elim
  | D r q =>
    have hq : q.p = 2 := by simpa using hchar
    have h := CFSG.Models.lieModel_D r q hv e
    rw [hq] at h
    exact ⟨.POmegaPlus, r, q.exponent, by decide,
      CFSG.Models.LieModel.toBlueprint (by decide) h⟩
  | twistedD r q =>
    have hq : q.p = 2 := by simpa using hchar
    have h := CFSG.Models.lieModel_twistedD r q hv e
    rw [hq] at h
    exact ⟨.POmegaMinus, r, q.exponent, by decide,
      CFSG.Models.LieModel.toBlueprint (by decide) h⟩
  | E6 q => exact hLie.elim
  | E7 q => exact hLie.elim
  | E8 q => exact hLie.elim
  | F4 q => exact hLie.elim
  | G2 q => exact hLie.elim
  | twistedE6 q => exact hLie.elim
  | trialityD4 q => exact hLie.elim
  | suzuki m => exact hLie.elim
  | reeG2 m => exact hLie.elim
  | reeF4 m => exact hLie.elim
  | tits => exact hLie.elim

private theorem eq_label_of_AParams {lab : GLALabel} {e : ℕ}
    (hP : CFSG.StandardType.markTag lab = .PSL ∧
      CFSG.StandardType.markRank lab = 3 ∧ CFSG.StandardType.markChar lab = 2 ∧
      CFSG.StandardType.markDeg lab = e) :
    lab = ⟨.A, 2, e⟩ := by
  obtain ⟨tg, r, nn⟩ := lab
  cases tg <;>
    simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markChar, CFSG.StandardType.markDeg] at hP ⊢ <;>
    (try split_ifs at hP ⊢) <;> simp_all <;> omega

private theorem eq_label_of_twAParams {lab : GLALabel} {e : ℕ}
    (hP : CFSG.StandardType.markTag lab = .PSU ∧
      CFSG.StandardType.markRank lab = 3 ∧ CFSG.StandardType.markChar lab = 2 ∧
      CFSG.StandardType.markDeg lab = e) :
    lab = ⟨.twA, 2, e⟩ := by
  obtain ⟨tg, r, nn⟩ := lab
  cases tg <;>
    simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markChar, CFSG.StandardType.markDeg] at hP ⊢ <;>
    (try split_ifs at hP ⊢) <;> simp_all <;> omega

section Label


theorem k1419ClsClassLabel_holds : K1419ClsClassLabelFact := by
  intro X _ hX hcat
  obtain ⟨d, hv, hP, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.K144I.exists_lieIndex_of_catalogIs_onLie hcat
  obtain ⟨t, n, f, ht, hm⟩ := exists_classical_lieModel ⟨d, hv⟩ hP.1 hP.2 e
  have hmark : HasLabel X (fun lab : GLALabel =>
      CFSG.StandardType.markTag lab = t ∧ CFSG.StandardType.markRank lab = n ∧
        CFSG.StandardType.markChar lab = 2 ∧ CFSG.StandardType.markDeg lab = f) :=
    CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hX.1 hm
  obtain ⟨lab, hP', hLab⟩ := exists_label_of_marking_aux hmark
  exact ⟨lab, hLab, not_famExc_of_markTag_classical ht hP'.1 hP'.2.2.1⟩

theorem k1419ClsL3U3Label_holds : K1419ClsL3U3LabelFact := by
  intro X _ hq hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic _ _ => simp [l3u3Index, onLie] at hi
  | alternating _ _ => simp [l3u3Index, onLie] at hi
  | sporadic _ => simp [l3u3Index, onLie] at hi
  | lie d =>
    obtain ⟨ld, hv⟩ := d
    cases ld with
    | A r q =>
      by_cases hr : r = 2
      · subst hr
        obtain ⟨hp2, hmod⟩ :
            q.p = 2 ∧ (q.exponent % 6 = 2 ∨ q.exponent % 6 = 4) := hi
        have hm := CFSG.Models.lieModel_A 2 q hv e
        rw [hp2] at hm
        have hmark : HasLabel X (fun lab : GLALabel =>
            CFSG.StandardType.markTag lab = .PSL ∧
              CFSG.StandardType.markRank lab = 3 ∧
              CFSG.StandardType.markChar lab = 2 ∧
              CFSG.StandardType.markDeg lab = q.exponent) :=
          CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hq.1
            (CFSG.Models.LieModel.toBlueprint (by decide) hm)
        obtain ⟨lab, hP, hLab⟩ := exists_label_of_marking_aux hmark
        have hlab : lab = ⟨.A, 2, q.exponent⟩ := eq_label_of_AParams hP
        exact ⟨q.exponent, Or.inl ⟨by rwa [hlab] at hLab, hmod⟩⟩
      · simp [l3u3Index, onLie, hr] at hi
    | twistedA r q =>
      by_cases hr : r = 2
      · subst hr
        obtain ⟨hp2, hmod⟩ :
            q.p = 2 ∧ (q.exponent % 6 = 1 ∨ q.exponent % 6 = 5) := hi
        have hm := lieModel_twistedA' 2 q hv e
        rw [hp2] at hm
        have hmark : HasLabel X (fun lab : GLALabel =>
            CFSG.StandardType.markTag lab = .PSU ∧
              CFSG.StandardType.markRank lab = 3 ∧
              CFSG.StandardType.markChar lab = 2 ∧
              CFSG.StandardType.markDeg lab = q.exponent) :=
          CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hq.1
            (CFSG.Models.LieModel.toBlueprint (by decide) hm)
        obtain ⟨lab, hP, hLab⟩ := exists_label_of_marking_aux hmark
        have hlab : lab = ⟨.twA, 2, q.exponent⟩ := eq_label_of_twAParams hP
        exact ⟨q.exponent, Or.inr ⟨by rwa [hlab] at hLab, hmod⟩⟩
      · simp [l3u3Index, onLie, hr] at hi
    | _ => simp [l3u3Index, onLie] at hi

end Label

end CFSG.LocalAnalysis.GLTheoremA.K1419
