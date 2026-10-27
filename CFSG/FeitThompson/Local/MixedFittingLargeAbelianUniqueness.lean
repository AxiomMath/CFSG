module

public import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
public import CFSG.FeitThompson.Definitions.UniqueMaximalOvergroup
import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
import CFSG.FeitThompson.Definitions.AlphaPrimesOfAFiniteGroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {M A : Subgroup G}

theorem isMixedFittingSetup_of_three_le_elementaryAbelianPRank (hM : IsCoatom M)
    (hMsolv : Group.IsSolvable ↥M) (hp : p.Prime) (hA : IsElementaryAbelian p A)
    (hAF : A ≤ mixedFitting M) (hrank : 3 ≤ elementaryAbelianPRank p ↥A)
    (hnp : ¬ IsPGroup p ↥(mixedFitting M)) :
    IsMixedFittingSetup p M A where
  isCoatom := hM
  isSolvable := hMsolv
  prime := hp
  isElementaryAbelian := hA
  le := hAF
  three_mem_ranks := mem_elementaryAbelianRanks_of_le hrank
    (elementaryAbelianPRank_mem_elementaryAbelianRanks hp.one_lt)
  not_isPGroup := hnp

theorem isUniqueMaximalOvergroup_mixedFittingCentralizer [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hM : IsCoatom M) (hp : p.Prime) (hA : IsElementaryAbelian p A) (hAF : A ≤ mixedFitting M)
    (hrank : 3 ≤ elementaryAbelianPRank p ↥A) (hnp : ¬ IsPGroup p ↥(mixedFitting M)) :
    IsUniqueMaximalOvergroup (mixedFittingCentralizer M A) M where
  isCoatom := hM
  le := (mixedFittingCentralizer_le M A).trans (mixedFitting_le M)
  eq_of_isCoatom _ hH hTH :=
    (isMixedFittingSetup_of_three_le_elementaryAbelianPRank hM (hsolv M hM.1) hp hA hAF hrank
      hnp).eq_of_le_mixedFittingCentralizer hna hodd hsolv hH hTH

theorem isUniqueMaximalOvergroup_mixedFittingCentralizer_of_maximal [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hM : IsCoatom M) (hp : p.Prime)
    (hA : Maximal (fun B : Subgroup G => IsElementaryAbelian p B ∧ B ≤ mixedFitting M) A)
    (hrank : 3 ≤ elementaryAbelianPRank p ↥A) (hnp : ¬ IsPGroup p ↥(mixedFitting M)) :
    IsUniqueMaximalOvergroup (mixedFittingCentralizer M A) M :=
  isUniqueMaximalOvergroup_mixedFittingCentralizer hna hodd hsolv hM hp hA.prop.1 hA.prop.2 hrank
    hnp

theorem le_of_mixedFittingCentralizer_le [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hM : IsCoatom M) (hp : p.Prime) (hA : IsElementaryAbelian p A) (hAF : A ≤ mixedFitting M)
    (hrank : 3 ≤ elementaryAbelianPRank p ↥A) (hnp : ¬ IsPGroup p ↥(mixedFitting M))
    {N : Subgroup G} (hTN : mixedFittingCentralizer M A ≤ N) (hN : N ≠ ⊤) : N ≤ M :=
  (isUniqueMaximalOvergroup_mixedFittingCentralizer hna hodd hsolv hM hp hA hAF hrank
    hnp).le_of_ne_top hTN hN

end

end CFSG.FeitThompson
