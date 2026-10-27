module

import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpOrders
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEvenNoComponent
public import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupFix
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupNum
public import CFSG.LocalAnalysis.OddStandard.AltStdSecStdAlt
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.AltStdSec

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatLeaf
  CFSG.Assembly.LowTwoRank CFSG.Blueprint Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem lieModel_card_ne_alt7 (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible t n p f)
    (hX : Blueprint.LieModel X t n p f) : Nat.card X ≠ 2520 :=
  CFSG.ComponentClassification.SolMax.lieModel_card_ne_alt_seven hO hadm hX

theorem card_eq_of_equiv_alt7 {Y : Type} [Group Y] (e : Y ≃* alternatingGroup (Fin 7)) :
    Nat.card Y = 2520 := by
  rw [card_eq_of_equiv_alt (by norm_num) e]
  decide

theorem false_of_lieModel_alt7 (hO : LieOrderFormulasInput) {Y : Type} [Group Y]
    (e : Y ≃* alternatingGroup (Fin 7)) {t : StatedLieTag} {n p f : ℕ}
    (hadm : StatedLieAdmissible t n p f) (hY : Blueprint.LieModel Y t n p f) : False :=
  lieModel_card_ne_alt7 hO hadm hY (card_eq_of_equiv_alt7 e)

theorem not_alt7_of_oddLieType (hGLS : GLS3OddLieAutComponentsInput)
    (hO : LieOrderFormulasInput) {S : Type} [Group S] (hodd : OddLieType S) {σ : MulAut S}
    (hσ : orderOf σ = 2) {B : Subgroup (fixedSubgroup σ)} (hB : IsComponent B) :
    ¬ Nonempty (B ≃* alternatingGroup (Fin 7)) := by
  rintro ⟨e⟩
  obtain ⟨τ, n, p, f, hp, hp2, hadm, hmod⟩ := hodd
  have hz : center B = ⊥ := center_eq_bot_of_alt (by omega) e
  rcases hGLS S τ n p f hp hp2 hadm hmod σ hσ B hB with ⟨τ', n', f', hadm', hm'⟩ |
      ⟨-, -, -, h8⟩
  · let q : (B ⧸ center B) ≃* alternatingGroup (Fin 7) :=
      ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans e
    exact false_of_lieModel_alt7 hO (MulEquiv.refl _) hadm'
      (LieType.CurtisTits.lieModel_of_mulEquiv q hm')
  · have hadm8 : StatedLieAdmissible .PSL 2 2 3 := by
      refine ⟨Nat.prime_two, by norm_num, le_rfl, ?_, ?_⟩ <;> decide
    exact false_of_lieModel_alt7 hO e hadm8 h8

theorem false_of_evenLie_alt7 (hO : LieOrderFormulasInput) (hEO : EvenLieOuterTwoComponentsInput)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (heven : EvenLieType S) {σ : MulAut S} (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1)
    {B : Subgroup (fixedSubgroup σ)} (hB : IsComponent B)
    (e : B ≃* alternatingGroup (Fin 7)) : False := by
  have hσ2' : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσ2) hσ1
  rcases exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout
  · have ht2 := lookup_orderOf_eq_two_of_conj hna hσ2 hσ1 ht
    obtain ⟨B', hB', -⟩ := isComponent_map_fixedSubgroup_conj ht hB
    exact involutionCentralizersComponentFree_of_evenLieType heven t ht2 B' hB'
  · obtain ⟨τ, n, f, hadm, hmod⟩ := heven
    have hPc : IsPComponent 2 B :=
      LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hB
    have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple hPc e
    rcases hEO S τ n f hadm hmod σ hσ2' hout B hPc with ⟨τ', n', f', hadm', hmod'⟩ | hA | hU
    · exact false_of_lieModel_alt7 hO eZ hadm' hmod'
    · obtain ⟨eA⟩ := hA
      have h1 := card_eq_of_equiv_alt (Y := alternatingGroup (Fin 7)) (m := 6) (by norm_num)
        (eZ.symm.trans eA)
      rw [card_eq_of_equiv_alt7 (MulEquiv.refl _)] at h1
      exact absurd h1 (by decide)
    · have hadm3 : StatedLieAdmissible .PSU 3 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩
      exact false_of_lieModel_alt7 hO eZ hadm3 hU

end CFSG.OddStandard.AltStdSec
