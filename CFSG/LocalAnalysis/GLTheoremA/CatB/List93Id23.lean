module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS07I67
public import CFSG.GH74.KGroups.L28
public import CFSG.GH74.KGroups.A6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.List93

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem elemAb_of_isElemAbelian' {G : Type} [Group G] {p : ℕ} {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian p E) : CFSG.GH74.KGroups.ElemAb p E :=
  ⟨fun a ha b hb => congrArg Subtype.val (hE.1.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩),
    fun a ha => hE.2 a ha⟩

theorem lt27_of_le9 {S : Type} [Group S]
    (h : ∀ R : Subgroup (MulAut S), CFSG.GH74.KGroups.ElemAb 3 R → Nat.card R ≤ 9) :
    ∀ E : Subgroup (MulAut S), CFSG.Open.IsElemAbelian 3 E → Nat.card E < 3 ^ 3 :=
  fun E hE => by
    have := h E (elemAb_of_isElemAbelian' hE)
    norm_num
    omega

theorem lt27_of_not_dvd {S : Type} [Group S] [Finite S] (hn : ¬ 27 ∣ Nat.card (MulAut S)) :
    ∀ E : Subgroup (MulAut S), CFSG.Open.IsElemAbelian 3 E → Nat.card E < 3 ^ 3 := by
  intro E hE
  by_contra hlt
  push Not at hlt
  exact hn (by simpa using cube_dvd_mulAut Nat.prime_three hE hlt)

section Certs


theorem chev23_holds : ∀ (S : Type) [Group S] [Finite S], IsChevSimple 2 S → IsChevSimple 3 S →
    catalogIs S S9.isU4two ∨ ∀ E : Subgroup (MulAut S), CFSG.Open.IsElemAbelian 3 E →
      Nat.card E < 3 ^ 3 := by
  intro S _ _ h2 h3
  rcases CFSG.StandardType.ChevTwo.chevTwo_cases h2 with ⟨t, n, f, hX⟩ | ⟨e6⟩ | hPSU
  · rcases h3 with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
    · cases i with
      | cyclic _ _ => exact hi.elim
      | alternating _ _ => exact hi.elim
      | sporadic _ => exact hi.elim
      | lie d =>
        have hd : d.1.characteristic = 3 := hi
        rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType' hX
            (small_odd_lie (r := 3) (by norm_num) (by norm_num) hd e) with
          ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · exact Or.inr (lt27_of_not_dvd (by rw [small_card_psl24 hX]; norm_num))
        · exact Or.inr (lt27_of_not_dvd (by rw [small_card_psl32 hX]; norm_num))
        · exact Or.inl (small_u42_of_model hX)
    · cases i with
      | cyclic _ _ => exact hi.elim
      | sporadic _ => exact hi.elim
      | alternating n' hn' =>
        rcases hi with ⟨-, h⟩ | ⟨rfl, -⟩ | ⟨-, h⟩
        · norm_num at h
        · obtain ⟨eQ⟩ := CFSG.GH74.KGroups.A6.equiv_of_alt6 ⟨e⟩
          exact Or.inr (lt27_of_not_dvd (by rw [CFSG.GH74.KGroups.A6.card_mulAut eQ]; norm_num))
        · norm_num at h
      | lie d =>
        obtain ⟨d1, hv⟩ := d
        rcases small_amb_lie (r := 3) (by norm_num) hv hi with
          ⟨q, rfl, hq8, -⟩ | ⟨q, rfl, hq2, -⟩
        · have hM := CFSG.Models.lieModel_A 1 q hv e
          obtain ⟨hq2', hq3⟩ := primePower_eq_of_card_eq (r := 2) (s := 3) Nat.prime_two
            (by norm_num) (hq8.trans (by norm_num))
          have hBP := CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
            (t := .PSL) (by simp [CFSG.Blueprint.classicalTags]) hM
          rw [hq2', hq3] at hBP
          exact Or.inr (lt27_of_le9 fun R hR => CFSG.GH74.KGroups.L28.autRank3_le_two hBP R hR)
        · exact Or.inl ⟨.lie ⟨.twistedA 3 q, hv⟩, hq2, ⟨e⟩⟩
  · obtain ⟨eQ⟩ := CFSG.GH74.KGroups.A6.equiv_of_alt6 e6
    exact Or.inr (lt27_of_not_dvd (by rw [CFSG.GH74.KGroups.A6.card_mulAut eQ]; norm_num))
  · obtain ⟨eS⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel
      (Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hPSU⟩)
    exact Or.inr (lt27_of_le9 fun R hR => CFSG.GH74.KGroups.U33.autRank3_le_two eS R hR)

end Certs

end CFSG.LocalAnalysis.GLTheoremA.List93

end
