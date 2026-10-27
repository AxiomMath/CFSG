module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5SecLookup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5SecRed
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterStructCases
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35HTransfer
public import CFSG.LocalAnalysis.SeitzReduction.GLS3OddHolds

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.OddStandard
  CFSG.OddStandard.AltStdSec CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Induction
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.HSStd.Zassenhaus
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

@[expose] def HSOuterSwapFree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S : Subgroup G) (z n v s : G),
    CFSG.EvenSporadicStandard.Induction.Balance.UHered G →
    ∀ (h : HSOuterSetup G L t S z n v s) (K : Subgroup (OuterSection v)),
    OuterSwap (OuterSection v) (sectionImage v (derivedCentralizerIn L v)) h.tBar K → False

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {S : Subgroup G}
  {z n v s : G}

theorem outerSwap_or_five_of_lookup
    (hGLS : CFSG.ComponentClassification.CatLeaf.GLS3OddLieAutComponentsInput)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (h : HSOuterSetup G L t S z n v s) (hF : F v t)
    (hL44 : ∀ W : Subgroup (OuterSection v), W.Normal → LieModel W .PSL 4 2 2 → False) :
    (∃ K : Subgroup (OuterSection v),
        OuterSwap (OuterSection v) (sectionImage v (derivedCentralizerIn L v)) h.tBar K) ∨
      HSOuterOutcomeFive (OuterSection v) := by
  have hsh := exactShape_outerSection h hF
  rcases section_dichotomy (oddCore_outerSection h) hsh (by norm_num) with
    hc | ⟨K, hKc, hne, hlay, ⟨eK⟩, hdiag⟩ | hAS
  · exfalso
    apply h.not_normal_sectionImage
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
    intro y _
    exact hsh.cent_le_norm (mem_centralizer_singleton_iff.2 (mem_center_iff.1 hc y))
  · left
    have hK'c : CFSG.IsComponent (PartA.cj h.tBar K) :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj h.tBar) hKc
    refine ⟨K, hKc, hK'c, hne, hlay, ?_, ⟨eK⟩, ?_⟩
    · intro a ha b hb
      exact mem_centralizer_iff.1 (PartA.le_centralizer_of_ne hK'c hKc hne hb) a ha
    · intro x
      have hx := Set.ext_iff.1 hdiag x
      simpa using hx
  · right
    rcases exactShape_almostSimple_eight hGLS hO (isKGroupCat_outerSection h)
        (oddCore_outerSection h) hsh hAS with ⟨e, -⟩ | hHS | ⟨W, hWN, -, -, hLie⟩
    · exact Or.inl ⟨e.symm⟩
    · exact Or.inr (equiv_mulAut_hs_of_hsOutcome hHS)
    · exact (hL44 W hWN hLie).elim

theorem hsOuterOutcomeFive_of_lookup
    (hgood : HSOuterGoodCase) (hL44 : HSOuterL44Free) (hsw : HSOuterSwapFree)
    (hG : CFSG.EvenSporadicStandard.Induction.Balance.UHered G)
    (h : HSOuterSetup G L t S z n v s) : HSOuterOutcomeFive (OuterSection v) := by
  rcases outerSwap_or_five_of_lookup CFSG.SeitzReduction.gls3OddLieAutComponentsInput
      CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput h
      (hgood G L t S z n v s hG h) (hL44 G L t S z n v s hG h) with ⟨K, hK⟩ | h5
  · exact (hsw G L t S z n v s hG h K hK).elim
  · exact h5

end CFSG.EvenSporadicStandard.HSStd
