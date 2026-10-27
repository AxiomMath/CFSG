module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.CrossCharOdd
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupSevenLie

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.CrossCharOdd (input3_3_OddChar_holds)


private theorem alt5_le5 : (5 : ℕ) ≤ 5 := le_refl 5
private theorem alt5_le6 : (5 : ℕ) ≤ 6 := by norm_num
private theorem alt5_le8 : (5 : ℕ) ≤ 8 := by norm_num

theorem i1416_sq_dvd_of_elemAb {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime)
    (h : ∃ A : Subgroup (MulAut S), IsElemAbelian p A ∧ p ^ 2 ≤ Nat.card A) :
    p ^ 2 ∣ Nat.card (MulAut S) := by
  obtain ⟨A, hA, hle⟩ := h
  obtain ⟨m, hm⟩ := exists_card_eq_pow_of_isElemAbelian hp hA
  have hm2 : 2 ≤ m := by
    rw [hm] at hle
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hle
  have hdvd := Subgroup.card_subgroup_dvd_card A
  rw [hm] at hdvd
  exact (pow_dvd_pow p hm2).trans hdvd

theorem i1416_amb_chev2 {S : Type} [Group S] {q : ℕ} (hq2 : q ≠ 2)
    (h : catalogIs S (ambiguousChev q)) : IsChevSimple 2 S := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | alternating n' hn' =>
    rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inr ⟨.alternating 5 alt5_le5, Or.inl ⟨rfl, Or.inl rfl⟩, ⟨f⟩⟩
    · exact Or.inr ⟨.alternating 6 alt5_le6, Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩), ⟨f⟩⟩
    · exact Or.inr ⟨.alternating 8 alt5_le8, Or.inr (Or.inr ⟨rfl, rfl⟩), ⟨f⟩⟩
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    rcases small_amb_lie hq2 hv hi with ⟨q', rfl, hq8, -⟩ | ⟨q', rfl, hq2', -⟩
    · obtain ⟨hp2, -⟩ := primePower_eq_of_card_eq (r := 2) (s := 3) Nat.prime_two (by norm_num)
        (hq8.trans (by norm_num))
      exact Or.inl ⟨.lie ⟨.A 1 q', hv⟩, by simp [onLie, hp2], ⟨f⟩⟩
    · obtain ⟨hp2, -⟩ := primePower_eq_of_card_eq (r := 2) (s := 1) Nat.prime_two (by norm_num)
        (hq2'.trans (by norm_num))
      exact Or.inl ⟨.lie ⟨.twistedA 3 q', hv⟩, by simp [onLie, hp2], ⟨f⟩⟩

theorem i1416_chev3_of_u42 {S : Type} [Group S] (h : catalogIs S S9.isU4two) : IsChevSimple 3 S := by
  obtain ⟨q, hv, hq2, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.lieIndex_isU4two h
  exact Or.inr ⟨.lie ⟨.twistedA 3 q, hv⟩, ⟨hq2, rfl⟩, ⟨e⟩⟩

section ArithCerts


theorem i1416_chev3_of_psu33 {S : Type} [Group S] (hPSU : StatedClassicalModel S .PSU 3 3 1) :
    IsChevSimple 3 S := by
  have hL : CFSG.Blueprint.LieModel S .PSU 3 3 1 :=
    Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hPSU⟩
  have hp3 : small_pp3.p = 3 :=
    (primePower_eq_of_card_eq (r := 3) (s := 1) Nat.prime_three (by norm_num) (small_pp3_card.trans (by norm_num))).1
  obtain ⟨eS⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel hL
  have hT : StatedClassicalModel
      (TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 2 small_pp3, small_valid_tw23⟩) .PSU 3 3 1 :=
    CFSG.StandardType.ChevTwo.statedClassicalModel_psu_three_three_of_twistedA_two small_pp3
      small_valid_tw23 small_pp3_card (MulEquiv.refl _)
  obtain ⟨eT⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel
    (Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hT⟩)
  exact Or.inl ⟨.lie ⟨.twistedA 2 small_pp3, small_valid_tw23⟩,
    by simp [onLie, TauCeti.LieTypeIndex.characteristic_twistedA, hp3], ⟨eS.trans eT.symm⟩⟩

theorem i1416Amb2 {S : Type} [Group S] {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hq2 : q ≠ 2)
    (hqp : q ≠ p) (h2 : IsChevSimple 2 S) (hq' : IsChevSimple q S) (hAut : p ^ 2 ∣ Nat.card (MulAut S)) :
    False := by
  have hqS : IsChevSimple q S := hq'
  rcases CFSG.StandardType.ChevTwo.chevTwo_cases h2 with ⟨t, n, f, hX⟩ | ⟨e6⟩ | hPSU
  · rcases hq' with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
    ·
      cases i with
      | cyclic _ _ => exact hi.elim
      | alternating _ _ => exact hi.elim
      | sporadic _ => exact hi.elim
      | lie d =>
        rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType' hX
            (small_odd_lie hq hq2 (d := d) hi e) with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · rw [small_card_psl24 hX] at hAut
          exact small_not_sq_120 hp hp2 hAut
        · rw [small_card_psl32 hX] at hAut
          exact small_not_sq_336 hp hp2 hAut
        ·
          have hcat := small_u42_of_model hX
          rw [card_mulAut_u4two hcat] at hAut
          have h3 : p = 3 := eq_three_of_sq_dvd hp hp2 (Or.inl rfl) hAut
          subst h3
          rcases input3_3_OddChar_holds S q 3 hqS (i1416_chev3_of_u42 hcat) hqp with h | h
          · exact hq2 h
          · exact absurd h (by norm_num)
    ·
      cases i with
      | cyclic _ _ => exact hi.elim
      | sporadic _ => exact hi.elim
      | alternating n' hn' =>
        rcases hi with ⟨rfl, h5 | h5⟩ | ⟨rfl, h6 | h6⟩ | ⟨rfl, h8⟩
        · exact absurd h5 hq2
        ·
          rw [small_card_psl24 (CFSG.StandardType.ChevTwo.lieModel_psl_two_four_of_alternating_five e)] at hAut
          exact small_not_sq_120 hp hp2 hAut
        · exact absurd h6 hq2
        ·
          rw [card_mulAut_a6 ⟨TauCeti.CFSGIndex.alternating 6 alt5_le6, rfl, ⟨e⟩⟩] at hAut
          have h3 : p = 3 := eq_three_of_sq_dvd hp hp2 (Or.inr rfl) hAut
          subst h3
          exact hqp h6
        · exact absurd h8 hq2
      | lie d =>
        obtain ⟨d1, hv⟩ := d
        rcases small_amb_lie hq2 hv hi with ⟨q', rfl, hq8, rfl⟩ | ⟨q', rfl, hq2', rfl⟩
        ·
          have hM := CFSG.Models.lieModel_A 1 q' hv e
          obtain ⟨hq2'', hq3⟩ := primePower_eq_of_card_eq (r := 2) (s := 3) Nat.prime_two (by norm_num)
            (hq8.trans (by norm_num))
          have hBP := CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
            (t := .PSL) (by simp [CFSG.Blueprint.classicalTags]) hM
          rw [hq2'', hq3] at hBP
          rw [small_card_psl28 hBP] at hAut
          have h3 : p = 3 := small_eq3_1512 hp hp2 hAut
          subst h3
          exact hqp rfl
        ·
          have hcat : catalogIs S S9.isU4two := ⟨.lie ⟨.twistedA 3 q', hv⟩, hq2', ⟨e⟩⟩
          rw [card_mulAut_u4two hcat] at hAut
          have h3 : p = 3 := eq_three_of_sq_dvd hp hp2 (Or.inl rfl) hAut
          subst h3
          exact hqp rfl
  ·
    obtain ⟨e⟩ := e6
    have h56 : (5 : ℕ) ≤ 6 := by norm_num
    rw [card_mulAut_a6 ⟨TauCeti.CFSGIndex.alternating 6 h56, rfl, ⟨e⟩⟩] at hAut
    have h3 : p = 3 := eq_three_of_sq_dvd hp hp2 (Or.inr rfl) hAut
    subst h3
    have h3' : IsChevSimple 3 S :=
      Or.inr ⟨.alternating 6 h56, Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩), ⟨e⟩⟩
    rcases input3_3_OddChar_holds S q 3 hqS h3' hqp with h | h
    · exact hq2 h
    · exact absurd h (by norm_num)
  ·
    have h3' : IsChevSimple 3 S := i1416_chev3_of_psu33 hPSU
    obtain ⟨h3, -⟩ := small_u33 hp hp2 hAut hPSU
    subst h3
    rcases input3_3_OddChar_holds S q 3 hqS h3' hqp with h | h
    · exact hq2 h
    · exact absurd h (by norm_num)

theorem i1416AltArith {S : Type} [Group S] {m : ℕ} (hm : 5 ≤ m) (e : S ≃* alternatingGroup (Fin m))
    {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hC : IsChevSimple q S) (hAut : p ^ 2 ∣ Nat.card (MulAut S)) : False := by
  by_cases h8 : m = 5 ∨ m = 6 ∨ m = 8
  ·
    have h2 : IsChevSimple 2 S := by
      rcases h8 with rfl | rfl | rfl
      · exact Or.inr ⟨.alternating 5 alt5_le5, Or.inl ⟨rfl, Or.inl rfl⟩, ⟨e⟩⟩
      · exact Or.inr ⟨.alternating 6 alt5_le6, Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩), ⟨e⟩⟩
      · exact Or.inr ⟨.alternating 8 alt5_le8, Or.inr (Or.inr ⟨rfl, rfl⟩), ⟨e⟩⟩
    exact i1416Amb2 hp hp2 hq hq2 hqp h2 hC hAut
  · have hne : m ≠ 5 ∧ m ≠ 6 ∧ m ≠ 8 := by omega
    rcases hC with ⟨i, hi, ⟨f⟩⟩ | ⟨i, hi, ⟨f⟩⟩
    · cases i with
      | cyclic _ _ => exact hi.elim
      | alternating _ _ => exact hi.elim
      | sporadic _ => exact hi.elim
      | lie d =>
        obtain ⟨t, n, p', f', -, -, hadm, hY⟩ := small_odd_lie hq hq2 (d := d) hi f
        rcases (show m = 7 ∨ 9 ≤ m by omega) with rfl | h9
        · exact CFSG.OddStandard.AltStdSec.false_of_lieModel_alt7
            CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput e hadm hY
        · exact CFSG.OddStandard.AltStdSec.false_of_lieModel_alt
            CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput h9 e hadm hY
    · exact not_chev2_alt hm hne e (i1416_amb_chev2 hq2 ⟨i, hi, ⟨f⟩⟩)

theorem i1416LieArith {S : Type} [Group S] {p q r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hq2 : q ≠ 2)
    (hqp : q ≠ p) (hrq : r ≠ q) (hR : IsChevSimple r S) (hC : IsChevSimple q S)
    (hAut : p ^ 2 ∣ Nat.card (MulAut S)) : False := by
  by_cases hr2 : r = 2
  · subst hr2
    exact i1416Amb2 hp hp2 hq hq2 hqp hR hC hAut
  · rcases input3_3_OddChar_holds S r q hR hC hrq with h | h
    · exact hr2 h
    · exact hq2 h

end ArithCerts

end CFSG.LocalAnalysis.GLTheoremA
