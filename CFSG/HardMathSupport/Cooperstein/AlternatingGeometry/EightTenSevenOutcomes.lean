module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenOutcomeFiveFinal
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenGivenNatural
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenSeven
public import CFSG.HardMathSupport.RichardWeiss.Coordinator.AltSevenCentre
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.EightTenI.AltTypeOdd
public import CFSG.HardMathSupport.Cooperstein.Proving.SolvableSylowNormalizerAll

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin
open CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure CFSG CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec19 CFSG.HardMathSupport.Cooperstein.StructureLie
open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

theorem outcomeOne_of_caseA_seven
    (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L)
    (hN : NaturalSectionLSL S L 7) (hY : HasSym3LiftS S L (L ⊔ S)) : InClassXBlock L := by
  have hSL : S ≤ Subgroup.normalizer (L : Set G) :=
    Coordinator.le_normalizer_of_isWeakSBlock hX hA hL
  have hcenM : Subgroup.center ↥(barM (L ⊔ S) L) = ⊥ :=
    CFSG.HardMathSupport.RichardWeiss.Coordinator.center_barM_eq_bot_of_natural_seven hX hA hL hN
  have hcore : L ⊓ pCoreOf 2 X = L ⊓ pCoreOf 2 (L ⊔ S) :=
    Coordinator.inf_pCoreOf_eq_inf_pCoreOf_sup hA hL hSL
  have hcenX : Subgroup.center ↥(barM X L) = ⊥ := by
    let E := CFSG.HardMathSupport.Cooperstein.Proving.barMEquiv hL.le (le_sup_left : L ≤ L ⊔ S) hcore
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have hEz : E z ∈ Subgroup.center ↥(barM (L ⊔ S) L) := by
      rw [Subgroup.mem_center_iff]
      intro c
      have := Subgroup.mem_center_iff.1 hz (E.symm c)
      have h2 := congrArg E this
      simpa [map_mul] using h2
    rw [hcenM] at hEz
    exact E.injective (by simpa using Subgroup.mem_bot.1 hEz)
  obtain ⟨Y, hSY, hYM, hSyl, hS3, -, y, hyL, hyY, hy, hyQ⟩ := hY
  have hQV := commutator_pCore_le_blockV_of_sym3_lift
    (CFSG.AGLEmbedding.asc81bEightFour_of_factorization
      CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved)
    hX hA hL hcenX hYM hSY hSyl hS3 hyL hyY hy hyQ
  have hirr := hasIrr_of_naturalSectionL (by omega) hN.naturalSectionL
  have hshort := isShort2_of_hQV_of_center_eq_bot hX hA hL hirr hQV hcenX
  exact inClassXBlock_of_natural_section_odd_of_center_bot hX hA hL (N := 7) (by norm_num)
    ⟨3, rfl⟩ hcenM hN hQV hshort

theorem eightTen_outcomes_of_natural_seven
    (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L)
    (hN : NaturalSectionLSL S L 7) : EightTenOutcomes X S L := by
  have hSL : S ≤ Subgroup.normalizer (L : Set G) :=
    Coordinator.le_normalizer_of_isWeakSBlock hX hA hL
  obtain ⟨θ, r, s, hr1, hs1, hrs, hD, hDX, hY3, hYS⟩ :=
    eightTen_cases_of_natural_seven hX hA hL
        (CFSG.HardMathSupport.RichardWeiss.Coordinator.center_barM_eq_bot_of_natural_seven hX hA hL
            hN) hN
  by_cases hr2 : r = 2
  · exfalso
    subst hr2
    exact eightTwo_false hA hL.toIsTwoPrimeComponent hSL
      (Proving.solvableSylowNormalizerAll G X S hX hA) (hDX X hA hL hSL symAutInner)
  · have hrg : r = 1 ∨ r = 3 ∨ 5 ≤ r := by omega
    have hsg : s = 1 ∨ s = 3 ∨ 5 ≤ s := by omega
    exact Or.inl (outcomeOne_of_caseA_seven hX hA hL hN (hYS hrg hsg))

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
