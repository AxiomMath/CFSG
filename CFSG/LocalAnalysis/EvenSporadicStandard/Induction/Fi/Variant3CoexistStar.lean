module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3CoexistTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3CoexistTail
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.RowBC
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.RowFacts

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction.Fi.V3

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

@[expose] def Fi23Claim612EStarAt (H : Type) [Group H] [Finite H] : Prop :=
  ∀ (N L K : Subgroup H) (t u : H), FStarSimple N → N.index ≤ 2 →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → OddCover .Fi23 L →
      SolomonGlobalQ H L K t u → fiLoc (2 * 64561751654400) H L K u → Fi23Transposition L u →
        Maximal L → (∀ S : Sylow 2 (centralizer (L : Set H)), Nat.card S = 2) →
          ∀ a : H, a ∈ L → orderOf a = 2 → (¬ ∃ l ∈ L, a = l * u * l⁻¹) → ¬ IsConj t (t * a)

@[expose] def Fi23Claim612EStarHered : Prop :=
  ∀ (H : Type) [Group H] [Finite H], Balance.UHered H → Fi23Claim612EStarAt H

theorem fi23Claim612E_of_star (h : Fi23Claim612EStarHered) : Fi23Claim612EHered :=
  fun H _ _ hH N L K t u hN hidx hkp hcov hglob hfi hT _ hS =>
    h H hH N L K t u hN hidx hkp hcov hglob (fiInBase_iff.1 hfi).1 hT
      (maximal_of_stdBare (Hyp.inL_of_solStd hglob.standardL) hglob.standardL.stdBare) hS

theorem fi23ClaimMax_of_star (h : Fi23Claim612EStarHered) : Fi23ClaimMaxHered :=
  fun H _ _ hH N L K t u hN hidx hkp hcov hglob hfi hT _ _ hS =>
    h H hH N L K t u hN hidx hkp hcov hglob hfi hT
      (maximal_of_stdBare (Hyp.inL_of_solStd hglob.standardL) hglob.standardL.stdBare) hS

section Certificates

theorem fiCoexistMax_of_star (ho : FiOrders) (hmult : OddMultTrivial .Fi23)
    (hfix23 : Fi23FixesElem) (hfix24 : Fi24InFixesElem)
    (h31 : FiHyp31Max (IsOddCentralExt Fi23D)) (h63 : Fi23Lemma63)
    (h65 : Balance.Sol78Lemma65KP) (h25 : Finkelstein77.Asc76Lemma25)
    (hI : HypothesisOne (Carrier .Fi23)) (hyp12 : Hyp12Fi) (hBal : Fi23BalanceHered)
    (hE : Fi23Claim612EStarHered) : FiCoexistMax :=
  fiCoexistMax_of_atlas ho (stage3Row_fi2324 hmult hfix23 hfix24) h31 hmult h63 h65
      (fi23TwoSylowMax_of h25 ((fi23_atlasFacts hmult hfix23).pRank_L) hI) hBal
      (fi23ClaimMax_of_star hE) (fi23TailMax_of_hyp12 hyp12 hmult)

end Certificates

end CFSG.EvenSporadicStandard.Induction.Fi.V3
