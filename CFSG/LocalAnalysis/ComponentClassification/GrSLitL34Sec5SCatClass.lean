module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsPFEven
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.LinearPilot

theorem isComponent_and_lieModel_of_simple {X : Type} [Group X]
    [Finite X] {P : Subgroup X} (hP : IsPComponent 2 P) [IsSimpleGroup P]
    (hL : LieModel P .PSL 3 2 2) : IsComponent P ∧ LieModel (P ⧸ center P) .PSL 3 2 2 := by
  have hna : ∃ a b : P, a * b ≠ b * a := L34PF.nonabelian_of_simple_of_four_dvd
    (by rw [card_of_isL34Type hL]; norm_num)
  have hZ : center P = ⊥ := center_eq_bot_of_simple hna
  exact ⟨⟨L34PF.isQuasisimple_of_simple hna, hP.choose_spec.2.1⟩,
    LieType.CurtisTits.lieModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm hL⟩

theorem lieModel_L316_of_classical_outer
    {S : Type} [Group S] [Finite S] {τ : StatedLieTag} {n f : ℕ}
    (hτ : τ ∈ Blueprint.classicalTags) (hadm : StatedLieAdmissible τ n 2 f)
    (hm : LieModel S τ n 2 f) {σ : MulAut S} (hσ2 : orderOf σ = 2)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {P : Subgroup (fixedSubgroup σ)}
    (hP : IsPComponent 2 P) [IsSimpleGroup P] (hL : LieModel P .PSL 3 2 2) :
    LieModel S .PSL 3 2 4 := by
  have hdet := slmEvenTypeDetAt (m := 3) le_rfl
  obtain ⟨hD, hDm⟩ := isComponent_and_lieModel_of_simple hP hL
  have hsp : ∀ {g : ℕ}, SpFixedOrNoPComponent (fixedSubgroup σ) g → False :=
    fun h => false_of_spFixedOrNoPComponent hdet h hD le_rfl hDm
  simp only [Blueprint.classicalTags, Finset.mem_insert, Finset.mem_singleton] at hτ
  rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl
  · rcases psl_outer_fixed_exact hadm hm σ hσ2 hout with h | h | h | h
    · obtain ⟨hadm', hm', h2⟩ := h P hP
      obtain ⟨-, rfl, h4⟩ := hdet _ 2 _ _ _ hL hadm' hm'
      obtain rfl : f = 4 := by omega
      exact hm
    · obtain ⟨hadm', hm'⟩ := h P hP
      exact absurd (hdet _ 2 _ _ _ hL hadm' hm').1 (by decide)
    · exact (hsp (Or.inl h)).elim
    · exact absurd hP (h P)
  · exact (hsp (psu_outer_fixed_exact hadm hm σ hσ2 hout)).elim
  · rcases psp_outer_fixed_exact hadm hm σ hσ2 hout with h | ⟨hs, hadmB, hmB⟩
    · exact (hsp h).elim
    · have htop := L34PF.eq_top_of_isPComponent_of_simple hP
      have hLF : LieModel (fixedSubgroup σ) .PSL 3 2 2 :=
        LieType.CurtisTits.lieModel_of_mulEquiv
          ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv) hL
      exact absurd (hdet _ 2 _ _ _ hLF hadmB hmB).1 (by decide)
  · exact absurd rfl hadm.2.2.2
  · rcases omega_family_fixed_exact (Or.inl rfl) hadm hm σ hσ2 hout with h | h
    · exact (hsp h).elim
    · obtain ⟨t, n', f', ht, hadm', hmP⟩ := h P hP
      have h1 := (hdet _ 2 _ _ _ hL hadm' hmP).1
      rcases ht with rfl | rfl <;> exact absurd h1 (by decide)
  · rcases omega_family_fixed_exact (Or.inr rfl) hadm hm σ hσ2 hout with h | h
    · exact (hsp h).elim
    · obtain ⟨t, n', f', ht, hadm', hmP⟩ := h P hP
      have h1 := (hdet _ 2 _ _ _ hL hadm' hmP).1
      rcases ht with rfl | rfl <;> exact absurd h1 (by decide)

theorem he_or_L316_of_evenLie
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (heven : EvenLieType S) {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P)
    (htype : IsL34Type (P ⧸ Open.fusionZStar P)) :
    Nonempty (S ≃* NativeSporadic.He) ∨ LieModel S .PSL 3 2 4 := by
  rcases exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout
  · obtain ⟨ht2, -, hPc, -⟩ := h.inner hna ht
    rcases oddCore_eq_bot_or_uList_of_evenLieType hna heven ht2 with hcore | hU
    · exfalso
      have hq := Sporadic.HeldB.pComponent_quasisimple_of_oddCore_eq_bot hcore _ hPc
      exact involutionCentralizersComponentFree_of_evenLieType heven t ht2 _
        ⟨hq, hPc.choose_spec.2.1⟩
    · rcases hU with ho | ⟨n, -, h7, hA⟩ | hL | hH
      · exact (L34PF.not_isL34Type_of_oddLie_or_alt hna h htype (Or.inl ho)).elim
      · exact (L34PF.not_isL34Type_of_oddLie_or_alt hna h htype (Or.inr ⟨n, h7, hA⟩)).elim
      · exact (L34PF.false_of_isL34Type_self h htype hL).elim
      · exact Or.inl hH
  · right
    have hσ2 : orderOf σ = 2 :=
      orderOf_eq_prime (by rw [sq]; exact MulEquiv.ext fun y => h.1 y) h.ne_one
    obtain ⟨τ, n, f, hadm, hm⟩ := heven
    by_cases hτ : τ ∈ Blueprint.classicalTags
    · have eP := subgroupOfEquivOfLe h.2.1
      have hd : 20160 ∣ Nat.card ↥(P.subgroupOf (fixedSubgroup σ)) := by
        rw [Nat.card_congr eP.toEquiv]
        exact L34PF.dvd_card_of_isL34Type htype
      have hs := L34PF.isSimpleGroup_of_classical_outer hτ hadm hm hσ2 hout h.2.2.1 hd
      have : IsSimpleGroup P := eP.symm.isSimpleGroup
      have hna' : ∃ a b : P, a * b ≠ b * a := L34PF.nonabelian_of_simple_of_four_dvd
        ((show 4 ∣ 20160 by norm_num).trans (L34PF.dvd_card_of_isL34Type htype))
      have hZ := L34PF.fusionZStar_eq_bot_of_simple hna'
        ((show 2 ∣ 20160 by norm_num).trans (L34PF.dvd_card_of_isL34Type htype))
      have e₁ : P ⧸ Open.fusionZStar P ≃* P :=
        (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
      exact lieModel_L316_of_classical_outer hτ hadm hm hσ2 hout h.2.2.1
        (LieType.CurtisTits.lieModel_of_mulEquiv (e₁.trans eP.symm) htype)
    · exfalso
      have hτ' : τ ≠ .PSL ∧ τ ≠ .PSU ∧ τ ≠ .PSp ∧ τ ≠ .POmegaOdd ∧ τ ≠ .POmegaPlus ∧
          τ ≠ .POmegaMinus := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> exact hτ (by decide)
      obtain ⟨eP⟩ :=
        GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe h.2.1).symm
      exact L34R.not_isL34Type_outer_nonclassical CatLeafProof.lieOrderFormulasInput hτ' hadm
        hm hσ2 hout h.2.2.1 (LieType.CurtisTits.lieModel_of_mulEquiv eP htype)

end CFSG.ComponentClassification.GrSLit.L34Sec5S
