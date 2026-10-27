module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1116
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltFacts4
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpOddChar

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.CrossCharOdd

open CFSG.Open CFSG.ComponentClassification.CatLeaf TauCeti
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple catalogIs onLie ambiguousChev)
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
  (lieModel_of_classical lieModel_lie lieModel_typeA)

theorem eq_of_pow_eq_eight {p k : ℕ} (hp : p.Prime) (h : p ^ k = 8) : p = 2 ∧ k = 3 := by
  have hk : k ≠ 0 := by
    rintro rfl
    simp at h
  have hp2 : p = 2 := by
    have h8 : p ∣ 2 ^ 3 := by
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← h]
      exact dvd_pow_self p hk
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h8)
  subst hp2
  exact ⟨rfl, Nat.pow_right_injective le_rfl (h.trans (by norm_num))⟩

theorem eq_of_pow_eq_two {p k : ℕ} (hp : p.Prime) (h : p ^ k = 2) : p = 2 ∧ k = 1 := by
  have hk : k ≠ 0 := by
    rintro rfl
    simp at h
  have hp2 : p = 2 := by
    have h2 : p ∣ 2 := by
      rw [← h]
      exact dvd_pow_self p hk
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
  subst hp2
  exact ⟨rfl, Nat.pow_right_injective le_rfl (h.trans (by norm_num))⟩

section Certified


theorem lie_cases {q : ℕ} {S : Type} [Group S] (h : catalogIs S (onLie fun d => d.characteristic = q)) :
    ∃ d : ValidLieTypeIndex, Nonempty (S ≃* (CFSGIndex.lie d).Group) ∧
      ∃ (t : StatedLieTag) (n f : ℕ), CFSG.Blueprint.LieModel S t n q f := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie d =>
    have hdq : d.1.characteristic = q := hi
    obtain ⟨t, n, p, f, hX, hp, -⟩ := AltFacts4.exists_blueprint_tagged d e
    obtain rfl : p = q := hp.trans hdq
    exact ⟨d, ⟨e⟩, t, n, f, hX⟩

theorem ambig_cases {r : ℕ} (hr2 : r ≠ 2) {S : Type} [Group S] (h : catalogIs S (ambiguousChev r)) :
    (Nonempty (S ≃* alternatingGroup (Fin 5)) ∧ r = 5) ∨
      (Nonempty (S ≃* alternatingGroup (Fin 6)) ∧ r = 3) ∨
      (r = 3 ∧ ∃ d : ValidLieTypeIndex, Nonempty (S ≃* (CFSGIndex.lie d).Group) ∧
        (CFSG.Blueprint.LieModel S .PSL 2 2 3 ∨ CFSG.Blueprint.LieModel S .PSU 4 2 1)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | alternating n hn =>
    rcases hi with ⟨rfl, h | h⟩ | ⟨rfl, h | h⟩ | ⟨-, h⟩
    · exact absurd h hr2
    · exact Or.inl ⟨⟨e⟩, h⟩
    · exact absurd h hr2
    · exact Or.inr (Or.inl ⟨⟨e⟩, h⟩)
    · exact absurd h hr2
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    cases d1 with
    | A k q' =>
      rcases k with _ | _ | k
      · simp [ambiguousChev] at hi
      ·
        have hi' : (q'.card = 7 ∧ r = 2) ∨ (q'.card = 8 ∧ r = 3) := by
          simpa [ambiguousChev] using hi
        rcases hi' with ⟨-, h⟩ | ⟨h8, h3⟩
        · exact absurd h hr2
        · obtain ⟨hp, hf⟩ := eq_of_pow_eq_eight q'.prime_p (by rw [← PrimePower.card_def, h8])
          have hY : CFSG.Blueprint.LieModel S .PSL (0 + 1 + 1) q'.p q'.exponent :=
            CFSG.Blueprint.LieModel.of_mulEquiv e.symm
              (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
                (lieModel_typeA (0 + 1) q' hv))
          rw [hp, hf] at hY
          exact Or.inr (Or.inr ⟨h3, _, ⟨e⟩, Or.inl hY⟩)
      · simp [ambiguousChev] at hi
    | twistedA k q' =>
      rcases k with _ | _ | _ | _ | k
      · simp [ambiguousChev] at hi
      · simp [ambiguousChev] at hi
      ·
        have hi' : q'.card = 3 ∧ r = 2 := by simpa [ambiguousChev] using hi
        exact absurd hi'.2 hr2
      ·
        have hi' : q'.card = 2 ∧ r = 3 := by simpa [ambiguousChev] using hi
        obtain ⟨hp, hf⟩ := eq_of_pow_eq_two q'.prime_p (by rw [← PrimePower.card_def, hi'.1])
        have hY : CFSG.Blueprint.LieModel S .PSU (0 + 1 + 1 + 1 + 1) q'.p q'.exponent :=
          CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
            (lieModel_of_classical
              (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA (0 + 1 + 1 + 1) q' hv e))
        rw [hp, hf] at hY
        exact Or.inr (Or.inr ⟨hi'.2, _, ⟨e⟩, Or.inr hY⟩)
      · simp [ambiguousChev] at hi
    | _ => simp [ambiguousChev] at hi

theorem false_of_lie_ambig {S : Type} [Group S] {q r : ℕ} (hqr : q ≠ r) (hq2 : q ≠ 2) (hr2 : r ≠ 2)
    (hq : catalogIs S (onLie fun d => d.characteristic = q)) (hr : catalogIs S (ambiguousChev r)) :
    False := by
  have hO : LieOrderFormulasInput := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  obtain ⟨d, ⟨e⟩, t, n, f, hX⟩ := lie_cases hq
  have hadm := CFSG.Blueprint.LieModel.admissible hX
  rcases ambig_cases hr2 hr with ⟨⟨a⟩, -⟩ | ⟨⟨a⟩, -⟩ | ⟨hr3, -, -, hY | hY⟩
  · exact (AltFacts4.inputAltNotLie_holds 5 d (by norm_num)).false (a.symm.trans e)
  · exact (AltFacts4.inputAltNotLie_holds 6 d (by norm_num)).false (a.symm.trans e)
  ·
    have hadmY := CFSG.Blueprint.LieModel.admissible hY
    rcases CFSG.SeitzReduction.CrossChar.crossChar_arith hadmY hadm hq2 (hO S _ _ _ _ hadmY hY).2.1
        (hO S _ _ _ _ hadm hX).2.1 with ⟨-, -, h, -⟩ | ⟨-, h, -⟩ | ⟨h, -⟩
    · exact absurd h (by norm_num)
    · exact absurd h (by norm_num)
    · exact absurd h (by decide)
  ·
    have hadmY := CFSG.Blueprint.LieModel.admissible hY
    rcases CFSG.SeitzReduction.CrossChar.crossChar_arith hadmY hadm hq2 (hO S _ _ _ _ hadmY hY).2.1
        (hO S _ _ _ _ hadm hX).2.1 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, -, -, -, h3⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · apply hqr
      rw [hr3]
      have hdvd : q ∣ 3 := h3 ▸ dvd_pow_self q (by have := hadm.2.1; omega)
      exact (Nat.prime_dvd_prime_iff_eq hadm.1 Nat.prime_three).1 hdvd

theorem false_of_ambig_ambig {S : Type} [Group S] {q r : ℕ} (hqr : q ≠ r) (hq2 : q ≠ 2) (hr2 : r ≠ 2)
    (hq : catalogIs S (ambiguousChev q)) (hr : catalogIs S (ambiguousChev r)) : False := by
  rcases ambig_cases hq2 hq with ⟨⟨a⟩, rfl⟩ | ⟨⟨a⟩, rfl⟩ | ⟨rfl, d, ⟨e⟩, -⟩ <;>
    rcases ambig_cases hr2 hr with ⟨⟨b⟩, rfl⟩ | ⟨⟨b⟩, rfl⟩ | ⟨rfl, d', ⟨e'⟩, -⟩
  · exact hqr rfl
  · exact absurd (Prop1116Design.alt_iso_degree (by norm_num) (by norm_num) (a.symm.trans b))
      (by norm_num)
  · exact (AltFacts4.inputAltNotLie_holds 5 d' (by norm_num)).false (a.symm.trans e')
  · exact absurd (Prop1116Design.alt_iso_degree (by norm_num) (by norm_num) (a.symm.trans b))
      (by norm_num)
  · exact hqr rfl
  · exact hqr rfl
  · exact (AltFacts4.inputAltNotLie_holds 5 d (by norm_num)).false (b.symm.trans e)
  · exact hqr rfl
  · exact hqr rfl

theorem input3_3_OddChar_holds : Claims1116.Input3_3_OddChar := by
  intro S _ q r hq hr hqr
  by_contra h2
  have hq2 : q ≠ 2 := fun h => h2 (Or.inl h)
  have hr2 : r ≠ 2 := fun h => h2 (Or.inr h)
  rcases hq with hq | hq <;> rcases hr with hr | hr
  · obtain ⟨-, -, t, n, f, hX⟩ := lie_cases hq
    obtain ⟨-, -, t', n', f', hX'⟩ := lie_cases hr
    exact hqr (CFSG.ComponentClassification.GS82PumpInputs.oddLieCharUnique_holds
      S t n q f t' n' r f' hq2 hr2 hX hX')
  · exact false_of_lie_ambig hqr hq2 hr2 hq hr
  · exact false_of_lie_ambig (Ne.symm hqr) hr2 hq2 hr hq
  · exact false_of_ambig_ambig hqr hq2 hr2 hq hr

theorem exc5_model {S : Type} [Group S] (h : Claims1116.Exc5 S) :
    ∃ (t : StatedLieTag) (f : ℕ), CFSG.Blueprint.LieModel S t 0 2 f ∧ t ≠ .PSL ∧ t ≠ .PSU ∧
      10 ≤ lieSylowExponent t 0 * f := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := h
  simp only at hd
  rcases hd with rfl | rfl | rfl
  · exact ⟨.Tits, 1, CFSG.Blueprint.LieModel.of_mulEquiv e.symm
      (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
        (lieModel_lie (t := .Tits) (p := 2) (f := 1) ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩
          ⟨.tits, hv⟩ ⟨rfl, rfl⟩)), by decide, by decide, by decide⟩
  · exact ⟨.twistedB2, 2 * 2 + 1, CFSG.Blueprint.LieModel.of_mulEquiv e.symm
      (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
        (lieModel_lie (t := .twistedB2) (p := 2) (f := 2 * 2 + 1)
          ⟨Nat.prime_two, by omega, rfl, rfl, ⟨2, rfl⟩, by omega⟩ ⟨.suzuki 2, hv⟩ ⟨rfl, rfl⟩)),
      by decide, by decide, by decide⟩
  · exact ⟨.twistedF4, 2 * 2 + 1, CFSG.Blueprint.LieModel.of_mulEquiv e.symm
      (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
        (lieModel_lie (t := .twistedF4) (p := 2) (f := 2 * 2 + 1)
          ⟨Nat.prime_two, by omega, rfl, rfl, ⟨2, rfl⟩, by omega⟩ ⟨.reeF4 2, hv⟩ ⟨rfl, rfl⟩)),
      by decide, by decide, by decide⟩

theorem input3_3_Exc5_holds : Claims1116.Input3_3_Exc5 := by
  intro S _ hexc q hq2 hch
  have hO : LieOrderFormulasInput := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  obtain ⟨t, f, hX, htL, htU, h10⟩ := exc5_model hexc
  have hadm := CFSG.Blueprint.LieModel.admissible hX
  rcases hch with hch | hch
  · obtain ⟨-, -, t', n', f', hY⟩ := lie_cases hch
    have hadm' := CFSG.Blueprint.LieModel.admissible hY
    rcases CFSG.SeitzReduction.CrossChar.crossChar_arith hadm hadm' hq2 (hO S _ _ _ _ hadm hX).2.1
        (hO S _ _ _ _ hadm' hY).2.1 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact htL h
    · exact htL h
    · exact htU h
  · obtain ⟨d, -, ⟨e⟩⟩ := hexc
    have h1 := (hO S _ _ _ _ hadm hX).2.2
    rcases ambig_cases hq2 hch with ⟨⟨a⟩, -⟩ | ⟨⟨a⟩, -⟩ | ⟨-, -, -, hY | hY⟩
    · exact (AltFacts4.inputAltNotLie_holds 5 d (by norm_num)).false (a.symm.trans e)
    · exact (AltFacts4.inputAltNotLie_holds 6 d (by norm_num)).false (a.symm.trans e)
    · have h2 := (hO S _ _ _ _ (CFSG.Blueprint.LieModel.admissible hY) hY).2.2
      have h3 : lieSylowExponent .PSL 2 * 3 = 3 := by decide
      omega
    · have h2 := (hO S _ _ _ _ (CFSG.Blueprint.LieModel.admissible hY) hY).2.2
      have h6 : lieSylowExponent .PSU 4 * 1 = 6 := by decide
      omega

end Certified

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.CrossCharOdd
