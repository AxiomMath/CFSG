module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsPFClass
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34REven
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddLie
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGLS3
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.ComponentClassification.GrSLit.L34PF

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem not_isL34Type_of_oddLie_or_alt
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P)
    (htype : IsL34Type (P ⧸ Open.fusionZStar P))
    (hS : OddLieType S ∨ ∃ n : ℕ, 7 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n))) : False := by
  rcases hS with ho | ⟨n, h7, ⟨θ⟩⟩
  · exact (not_held_not_L34_of_properFixedComponent_oddLie
      GrSLit.gls3OddLieAutComponentsInput_holds CatLeafProof.lieOrderFormulasInput hna ho h).2 htype
  · exact not_isL34Type_of_properFixedComponent_alternating (by omega) θ h htype

theorem false_of_isL34Type_self {S : Type} [Group S] [Finite S]
    {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P)
    (htype : IsL34Type (P ⧸ Open.fusionZStar P)) (hL : IsL34Type S) : False := by
  have hS := card_of_isL34Type hL
  have hPd : 20160 ∣ Nat.card P := dvd_card_of_isL34Type htype
  exact h.2.2.2 ((Subgroup.card_eq_iff_eq_top P).mp
    (Nat.dvd_antisymm (Subgroup.card_subgroup_dvd_card P) (hS ▸ hPd)))

theorem he_or_rank_of_evenLie
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (heven : EvenLieType S) {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P)
    (htype : IsL34Type (P ⧸ Open.fusionZStar P)) :
    Nonempty (S ≃* NativeSporadic.He) ∨ pRank 2 ↥(Open.fusionZStar P) ≤ 1 := by
  rcases exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout
  · obtain ⟨ht2, -, hPc, -⟩ := h.inner hna ht
    rcases oddCore_eq_bot_or_uList_of_evenLieType hna heven ht2 with hcore | hU
    · exfalso
      have hq := Sporadic.HeldB.pComponent_quasisimple_of_oddCore_eq_bot hcore _ hPc
      exact involutionCentralizersComponentFree_of_evenLieType heven t ht2 _
        ⟨hq, hPc.choose_spec.2.1⟩
    · rcases hU with ho | ⟨n, -, h7, hA⟩ | hL | hH
      · exact (not_isL34Type_of_oddLie_or_alt hna h htype (Or.inl ho)).elim
      · exact (not_isL34Type_of_oddLie_or_alt hna h htype (Or.inr ⟨n, h7, hA⟩)).elim
      · exact (false_of_isL34Type_self h htype hL).elim
      · exact Or.inl hH
  · right
    have hσ2 : orderOf σ = 2 :=
      orderOf_eq_prime (by rw [sq]; exact MulEquiv.ext fun y => h.1 y) h.ne_one
    obtain ⟨τ, n, f, hadm, hm⟩ := heven
    by_cases hτ : τ ∈ Blueprint.classicalTags
    · have eP := subgroupOfEquivOfLe h.2.1
      have hd : 20160 ∣ Nat.card ↥(P.subgroupOf (fixedSubgroup σ)) := by
        rw [Nat.card_congr eP.toEquiv]
        exact dvd_card_of_isL34Type htype
      have hs := isSimpleGroup_of_classical_outer hτ hadm hm hσ2 hout h.2.2.1 hd
      have : IsSimpleGroup P := eP.symm.isSimpleGroup
      rw [pRank_fusionZStar_eq_zero_of_simple' htype]
      exact Nat.zero_le 1
    · exfalso
      have hτ' : τ ≠ .PSL ∧ τ ≠ .PSU ∧ τ ≠ .PSp ∧ τ ≠ .POmegaOdd ∧ τ ≠ .POmegaPlus ∧
          τ ≠ .POmegaMinus := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> exact hτ (by decide)
      obtain ⟨eP⟩ :=
        GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe h.2.1).symm
      exact L34R.not_isL34Type_outer_nonclassical CatLeafProof.lieOrderFormulasInput hτ' hadm
        hm hσ2 hout h.2.2.1 (LieType.CurtisTits.lieModel_of_mulEquiv eP htype)

end CFSG.ComponentClassification.GrSLit.L34PF
