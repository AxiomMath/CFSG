module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34REvenExcB
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34REvenCl
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEven

public noncomputable section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace L34R

theorem not_isL34Type_outer_nonclassical
    (hO : LieOrderFormulasInput) {K : Type} [Group K] {τ : StatedLieTag} {n f : ℕ}
    (hτ : τ ≠ .PSL ∧ τ ≠ .PSU ∧ τ ≠ .PSp ∧ τ ≠ .POmegaOdd ∧ τ ≠ .POmegaPlus ∧ τ ≠ .POmegaMinus)
    (hadm : StatedLieAdmissible τ n 2 f) (hm : LieModel K τ n 2 f) {α : MulAut K}
    (hα2 : orderOf α = 2) (hαo : α ∉ (MulAut.conj : K →* MulAut K).range)
    {P : Subgroup (fixedSubgroup α)} (hP : IsPComponent 2 P) :
    ¬ IsL34Type (P ⧸ Open.fusionZStar P) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hτ
  cases τ
  case PSL => exact absurd rfl h1
  case PSU => exact absurd rfl h2
  case PSp => exact absurd rfl h3
  case POmegaOdd => exact absurd rfl h4
  case POmegaPlus => exact absurd rfl h5
  case POmegaMinus => exact absurd rfl h6
  case G2 => exact not_isL34Type_outer_G2 hO hadm hm hα2 hαo hP
  case F4 => exact not_isL34Type_outer_F4 hO hadm hm hα2 hαo hP
  case E6 => exact not_isL34Type_outer_E6 hO hadm hm hα2 hαo hP
  case E7 => exact not_isL34Type_outer_E7_E8 hO (Or.inl rfl) hadm hm hα2 hαo hP
  case E8 => exact not_isL34Type_outer_E7_E8 hO (Or.inr rfl) hadm hm hα2 hαo hP
  case twistedE6 => exact not_isL34Type_outer_twistedE6 hO hadm hm hα2 hαo hP
  case trialityD4 => exact not_isL34Type_outer_trialityD4 hO hadm hm hα2 hαo hP
  case twistedB2 => exact (false_of_outer_suzukiRee (Or.inl rfl) hadm hm hα2 hαo).elim
  case twistedG2 => exact absurd hadm.2.2.2.1 (by norm_num)
  case twistedF4 => exact (false_of_outer_suzukiRee (Or.inr (Or.inl rfl)) hadm hm hα2 hαo).elim
  case Tits => exact (false_of_outer_suzukiRee (Or.inr (Or.inr rfl)) hadm hm hα2 hαo).elim


theorem uList_of_evenLie
    (hO : LieOrderFormulasInput) (hGA : TBLit.GriessMultipliersAllModels)
    (hR1 : EvenLieExcOuterL34Input) {Q : Type} [Group Q] [Finite Q] (hQ : IsQuasisimple Q)
    (hZ : IsPGroup 2 (center Q)) (hZ1 : center Q ≠ ⊥) (heven : EvenLieType (Q ⧸ center Q))
    {σ : MulAut (Q ⧸ center Q)} {P : Subgroup (Q ⧸ center Q)} (h : ProperFixedComponent σ P)
    (htype : IsL34Type (P ⧸ Open.fusionZStar P)) : TBLit.UList (Q ⧸ center Q) := by
  have : IsSimpleGroup (Q ⧸ center Q) := hQ.2.1
  have hna : ∃ a b : Q ⧸ center Q, a * b ≠ b * a := hQ.2.2
  rcases exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout
  · obtain ⟨ht2, -, hPc, -⟩ := h.inner hna ht
    rcases oddCore_eq_bot_or_uList_of_evenLieType hna heven ht2 with hcore | hU
    · exfalso
      have hq := Sporadic.HeldB.pComponent_quasisimple_of_oddCore_eq_bot hcore _ hPc
      exact involutionCentralizersComponentFree_of_evenLieType heven t ht2 _
        ⟨hq, hPc.choose_spec.2.1⟩
    · exact hU
  · exfalso
    have hσ2 : orderOf σ = 2 :=
      orderOf_eq_prime (by rw [sq]; exact MulEquiv.ext fun y => h.1 y) h.ne_one
    obtain ⟨τ, n, f, hadm, hm⟩ := heven
    by_cases hτ : τ ∈ Blueprint.classicalTags
    · have h2Z : 2 ∣ Nat.card (center Q) := RankThree.PartTwo.Sec4.Census.two_dvd_card_center hZ
        ((Subgroup.nontrivial_iff_ne_bot _).mpr hZ1)
      have hd := RankThree.PartTwo.Sec4.Census.card_center_dvd_tableOrder hGA hQ
        (MulEquiv.refl _) (models_lieModel_of_classical hτ hadm hm)
      exact false_of_classical_outer hO hR1 hτ hadm hm (h2Z.trans hd) hσ2 hout h htype
    · have hτ' : τ ≠ .PSL ∧ τ ≠ .PSU ∧ τ ≠ .PSp ∧ τ ≠ .POmegaOdd ∧ τ ≠ .POmegaPlus ∧
          τ ≠ .POmegaMinus := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> exact hτ (by decide)
      obtain ⟨eP⟩ :=
        GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe h.2.1).symm
      exact not_isL34Type_outer_nonclassical hO hτ' hadm hm hσ2 hout h.2.2.1
        (LieType.CurtisTits.lieModel_of_mulEquiv eP htype)

end L34R

end CFSG.ComponentClassification.GrSLit
