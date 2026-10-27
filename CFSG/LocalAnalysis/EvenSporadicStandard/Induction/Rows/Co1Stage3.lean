module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Stage3Parts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Stage3Glob
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Mult
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBCLocal

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
  CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block

@[expose] def Co1TMemOfNotMax : Prop := TMemOfNotMax [.Co1] (fun _ => Co1Pair)

theorem twoSylowStd_co1 (h25 : Finkelstein77.Asc76Lemma25)
    (hr : ∀ (X : Type) [Group X], IsLS [.Co1] X → 3 ≤ CFSG.pRank 2 X) : TwoSylowStd [.Co1] :=
  twoSylowStd_of_lemma25 h25 hr fun _ _ h =>
    TwoCo1.HypOne.hypothesisOne_of_isSporadic_co1 h TwoCo1.HypOne.hypothesisOne_native

@[expose] def IsKCo1 : GroupClass := IsOddCentralExt ↥twoBD

theorem co1_finite_even : ∀ s ∈ [TauCeti.SporadicName.Co1], ∀ (Y : Type) [Group Y],
    IsSporadic Y s → Finite Y ∧ Even (Nat.card Y) := by
  intro s hs Y _ h
  rcases List.mem_singleton.1 hs with rfl
  obtain ⟨e⟩ := h
  have hc : Nat.card (Carrier .Co1) = 4157776806543360000 := CFSG.Sporadic.Co1.card_Co1
  have : Finite (Carrier .Co1) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  refine ⟨Finite.of_equiv _ e.symm.toEquiv, ?_⟩
  rw [Nat.card_congr e.toEquiv, hc]
  decide

theorem co1_rowIsK (hmult : OddMultTrivial .Co1) : ∀ s ∈ [TauCeti.SporadicName.Co1],
    ∀ (H : Type) [Group H] (L K : Subgroup H) (u : H), OddCover s L → Co1Pair H L K u →
      IsKCo1 ↥K := by
  intro s hs H _ L K u hcov hQ
  rcases List.mem_singleton.1 hs with rfl
  have := hcov.finite (by decide : TauCeti.SporadicName.Co1 ≠ .M)
  have hL : IsSporadic ↥L .Co1 :=
    isSporadic_of_center_eq_bot (hmult ↥L hcov.1 hcov.2.1 hcov.2.2) hcov.2.2
  have hP : Co1Pair H L K u := hQ
  obtain ⟨huL, hu2, hKL, hKu, hperf, hcard⟩ := hQ
  obtain ⟨Ψ, hΨ, hΨL, hΨR, hΨu⟩ := co1_model hL hP
  obtain ⟨M⟩ := co1_outModel
  obtain ⟨eK⟩ := M.equiv_D huL hKL hKu Ψ hΨ hΨL hΨu hperf (hcard.trans card_twoBD.symm)
  have hqK : CFSG.Open.IsQuasisimple ↥K :=
    isQuasisimple_of_mulEquiv' eK.symm
      (isQuasisimple_of_simple isSimpleGroup_twoBD ⟨xD, yD, xD_yD_ne⟩)
  have hker : eK.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 eK.injective
  exact ⟨((CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1).2 hqK, eK.toMonoidHom,
    eK.surjective, by rw [hker]; exact bot_le, by rw [hker, Subgroup.card_bot]; exact odd_one⟩

end CFSG.EvenSporadicStandard.Induction
