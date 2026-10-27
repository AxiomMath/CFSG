module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.BRoots
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.BClassA
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.BClassB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.BOddCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.BRowFinal
public import CFSG.Monster.B.Final.PinnedBOrder
public import CFSG.Monster.B.Pinned.Primes.SeedGL
public import CFSG.RankThree.PartOne.SPOR.OuterB

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HypOne.BabyHyp

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS CFSG.Monster.Existence
  CFSG.ComponentClassification.M12Cover CFSG.EvenSporadicStandard.Solomon78
  CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 CFSG.RankThree.PartOne.SPOR
  CFSG.EvenSporadicStandard.HypOne

@[expose] def BabyRootClassLarge (k : Fin 4) : Prop :=
  ∀ a : NativeSporadic.B, BabyInv k a → ∀ n : centralizer ({a} : Set NativeSporadic.B),
    (n : NativeSporadic.B) * n = a →
      5 ≤ Nat.card {y : centralizer ({a} : Set NativeSporadic.B) // IsConj n y}



theorem noNormalFour_centralizer_of_rootClassLarge {k : Fin 4}
    (hcen : ∀ a : NativeSporadic.B, BabyInv k a → CenterInvAt a) (h : BabyRootClassLarge k)
    {a : NativeSporadic.B} (ha : BabyInv k a) :
    NoNormalFour (centralizer ({a} : Set NativeSporadic.B)) :=
  @noNormalFour_centralizer_of_roots NativeSporadic.B Units.instGroup a (hcen a ha) (h a ha)

theorem noNormalFour_centralizer_B (h2 : BabyRootClassLarge 2) (h3 : BabyRootClassLarge 3)
    {X : NativeSporadic.B} (hX : orderOf X = 2) :
    NoNormalFour (centralizer ({X} : Set NativeSporadic.B)) := by
  have hfin := CFSG.Monster.B.Pinned.finite_B
  obtain ⟨k, hk⟩ := babyTableIII.1 X hX
  fin_cases k
  · exact noNormalFour_centralizer_babyInv_zero hk
  · exact noNormalFour_centralizer_babyInv_one hk
  · exact noNormalFour_centralizer_of_rootClassLarge (fun a ha => babyCenterW3_B a ha) h2 hk
  · exact noNormalFour_centralizer_of_rootClassLarge (fun a ha => babyCenterW4_B a ha) h3 hk

theorem hypothesisOne_B_of_roots (h2 : BabyRootClassLarge 2) (h3 : BabyRootClassLarge 3) :
    HypothesisOne (Carrier .B) := by
  have hfin := CFSG.Monster.B.Pinned.finite_B
  obtain ⟨-, -, -, hs, hcard⟩ := CFSG.Monster.B.pinned_B_explicit_native_isomorphism_simplicity_and_order
  have hcenter : center NativeSporadic.B = ⊥ :=
    center_eq_bot_of_isSimpleGroup (by rw [hcard]; norm_num)
  refine hypothesisOne_of_inner (conj_injective_of_center_eq_bot hcenter) allInner_B
    (fun y hy => ?_)
  exact SmallNormalFree.of_noNormalFour (oddCore_centralizer_B hy)
    (noNormalFour_centralizer_B h2 h3 hy)

end CFSG.EvenSporadicStandard.HypOne.BabyHyp
