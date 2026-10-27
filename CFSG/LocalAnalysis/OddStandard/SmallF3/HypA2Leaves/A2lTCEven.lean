module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCEvenPSL
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCEvenPSU
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCEvenPSp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCEvenOmega
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCEvenExc
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCEvenE6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCEvenSuz
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatEvenInner

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification
  CFSG.ComponentClassification.CatLeaf CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.SolMax.FiveCat.Even (evenFiveInner)

section


theorem a2l_evenTCOuter_all (hO : LieOrderFormulasInput) (τ : Open.StatedLieTag) :
    EvenTCOuter τ := by
  cases τ
  · exact a2l_evenTCOuter_PSL hO
  · exact a2l_evenTCOuter_PSU hO
  · exact a2l_evenTCOuter_PSp hO
  · exact fun _ _ n f hadm => absurd rfl hadm.2.2.2
  · exact a2l_evenTCOuter_POmegaPlus hO
  · exact a2l_evenTCOuter_POmegaMinus hO
  · exact a2l_evenTCOuter_G2 hO
  · exact a2l_evenTCOuter_F4 hO
  · exact a2l_evenTCOuter_E6 hO
  · exact a2l_evenTCOuter_E7 hO
  · exact a2l_evenTCOuter_E8 hO
  · exact a2l_evenTCOuter_twistedE6 hO
  · exact a2l_evenTCOuter_trialityD4 hO
  · exact a2l_evenTCOuter_twistedB2 hO
  · exact fun _ _ n f hadm => absurd hadm.2.2.2.1 (by norm_num)
  · exact a2l_evenTCOuter_twistedF4 hO
  · exact a2l_evenTCOuter_Tits hO

theorem a2l_even_arm (hO : LieOrderFormulasInput) {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hna : ∃ x y : S, x * y ≠ y * x) {τ : Open.StatedLieTag} {n f : ℕ}
    (hL : Blueprint.LieModel S τ n 2 f) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) (hS : TCSmall (↥P ⧸ Open.fusionZStar ↥P)) :
    EvenTCList τ n f :=
  a2l_evenTCList_of_inner_outer (evenFiveInner τ) (a2l_evenTCOuter_all hO τ) hs hna hL h hS

end

end CFSG.OddStandard.SmallF3.HypA2Leaves
