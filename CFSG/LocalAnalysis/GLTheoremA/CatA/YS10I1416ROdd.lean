module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416Chev2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small
public import CFSG.GH74.KGroups.A5

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10

def odd_pp7 : TauCeti.PrimePower := ⟨7, 1, by norm_num, Nat.one_pos⟩

theorem odd_pp7_card : odd_pp7.card = 7 := by
  rw [TauCeti.PrimePower.card_def]
  rfl

theorem odd_valid_A17 : (TauCeti.LieTypeIndex.A 1 odd_pp7).Valid := by
  rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  simp [odd_pp7]

private theorem odd_chev2Small_of_isU4two (i : TauCeti.CFSGIndex) (hi : S9.isU4two i) : chev2Small i := by
  cases i with
  | cyclic _ _ => exact False.elim hi
  | alternating _ _ => exact False.elim hi
  | sporadic _ => exact False.elim hi
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    cases d1 <;> try (exact False.elim hi)
    rename_i r q
    by_cases h3 : r = 3
    · subst h3
      exact hi
    · exact absurd hi (by simp [S9.isU4two, onLie, h3])

section OddCerts


theorem chev2OddAmb_holds : Chev2OddAmb := by
  intro r T _ hr hr2 h2 hrC
  have h55 : (5 : ℕ) ≤ 5 := le_rfl
  have h56 : (5 : ℕ) ≤ 6 := by norm_num
  rcases CFSG.StandardType.ChevTwo.chevTwo_cases h2 with ⟨t, n, f, hX⟩ | ⟨e6⟩ | hPSU
  · rcases hrC with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
    ·
      cases i with
      | cyclic _ _ => exact hi.elim
      | alternating _ _ => exact hi.elim
      | sporadic _ => exact hi.elim
      | lie d =>
        rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType' hX
            (small_odd_lie (d := d) hr hr2 hi e) with
          ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        ·
          obtain ⟨eA⟩ := CFSG.GH74.KGroups.A5.equiv_of_lieModel22 hX
          exact ⟨TauCeti.CFSGIndex.alternating 5 h55, Or.inl rfl,
            ⟨eA.trans (MulEquiv.subgroupCongr CFSG.GH74.KGroups.A5.QP_eq_alt)⟩⟩
        ·
          obtain ⟨eT⟩ := CFSG.GH74.KGroups.L27.equiv_of_lieModel3 hX
          obtain ⟨eI⟩ := CFSG.GH74.KGroups.L27.equiv_of_lieModel
            (CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (t := .PSL)
              (by simp [CFSG.Blueprint.classicalTags])
              (CFSG.Models.lieModel_A 1 odd_pp7 odd_valid_A17 (MulEquiv.refl _)))
          exact ⟨TauCeti.CFSGIndex.lie ⟨.A 1 odd_pp7, odd_valid_A17⟩, Or.inl odd_pp7_card,
            ⟨eT.trans eI.symm⟩⟩
        ·
          obtain ⟨i', hi', e'⟩ := small_u42_of_model hX
          exact ⟨i', odd_chev2Small_of_isU4two i' hi', e'⟩
    ·
      cases i with
      | cyclic _ _ => exact hi.elim
      | sporadic _ => exact hi.elim
      | alternating n hn =>
        rcases hi with ⟨rfl, h5 | h5⟩ | ⟨rfl, h6 | h6⟩ | ⟨rfl, h8⟩
        · exact absurd h5 hr2
        · exact ⟨TauCeti.CFSGIndex.alternating 5 hn, Or.inl rfl, ⟨e⟩⟩
        · exact absurd h6 hr2
        · exact ⟨TauCeti.CFSGIndex.alternating 6 hn, Or.inr (Or.inl rfl), ⟨e⟩⟩
        · exact absurd h8 hr2
      | lie d =>
        obtain ⟨d1, hv⟩ := d
        rcases small_amb_lie hr2 hv hi with ⟨q, rfl, hq8, rfl⟩ | ⟨q, rfl, hq2, rfl⟩
        ·
          exact ⟨TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩, Or.inr hq8, ⟨e⟩⟩
        ·
          exact ⟨TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩, hq2, ⟨e⟩⟩
  ·
    obtain ⟨e6'⟩ := e6
    exact ⟨TauCeti.CFSGIndex.alternating 6 h56, Or.inr (Or.inl rfl), ⟨e6'⟩⟩
  ·
    have hL : CFSG.Blueprint.LieModel T .PSU 3 3 1 := Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hPSU⟩
    obtain ⟨eS⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel hL
    have hT := CFSG.StandardType.ChevTwo.statedClassicalModel_psu_three_three_of_twistedA_two small_pp3
      small_valid_tw23 small_pp3_card (MulEquiv.refl _)
    obtain ⟨eT⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel (Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hT⟩)
    exact ⟨TauCeti.CFSGIndex.lie ⟨.twistedA 2 small_pp3, small_valid_tw23⟩, small_pp3_card,
      ⟨eS.trans eT.symm⟩⟩

end OddCerts

end CFSG.LocalAnalysis.GLTheoremA

end
