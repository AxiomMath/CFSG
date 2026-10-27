module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.BGeneric
public import CFSG.Monster.B.Cbar.LocalStructure
public import CFSG.Monster.B.GSide.TwoBNative
public import CFSG.Monster.Existence.BabyW2
public import CFSG.Monster.Existence.DLevelRank
public import CFSG.Monster.Existence.MilestoneInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Walter.JRFacts

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HypOne.BabyHyp

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS CFSG.Monster.Existence
  CFSG.Monster.B CFSG.Monster.B.GSide CFSG.ComponentClassification.M12Cover



theorem noNormalFour_Jbar : NoNormalFour Jbar := by
  obtain ⟨-, hx2, -, hEJ, -, -, hJcard, hExtra, hEcard, -⟩ :=
    short_centralizer_quotient_local_structure
  have hJ2 : ¬ IsPGroup 2 Jbar := by
    intro h
    obtain ⟨k, hk⟩ := h.exists_card_eq
    rw [hJcard] at hk
    have h3 : (3 : ℕ) ∣ 2 ^ k := by
      rw [← hk]
      norm_num
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hx : Nat.card (zpowers xbar) ≤ 2 := by
    rw [Nat.card_zpowers, hx2]
  refine noNormalFour_of_invariant_subgroups Jbar Ebar hEJ xbar (by rw [hEcard]; norm_num) hJ2 hx
    (IsPGroup.of_card (n := 23) hEcard) (fun h hh q hq => ?_)
    (fun R hRE hR => eq_of_invariant_Ebar R hR hRE)
    (fun R hER hRJ hR => eq_of_normal_Ebar R hER hRJ hR)
  have := conj_mem_Ebar (Jbar.inv_mem hh) hq
  simpa using this

theorem noNormalFour_centralizer_phiB_xBar :
    NoNormalFour (centralizer ({phiB xBar} : Set NativeSporadic.B)) := by
  have h1 : NoNormalFour (centralizer ({xbar} : Set Cbar)) :=
    noNormalFour_of_mulEquiv (MulEquiv.subgroupCongr centralizer_xbar.symm) noNormalFour_Jbar
  exact @noNormalFour_centralizer_of_mulEquiv Cbar NativeSporadic.B _ Units.instGroup phiB xbar _
    rfl h1

theorem noNormalFour_centralizer_babyInv_one {X : NativeSporadic.B} (hX : BabyInv 1 X) :
    NoNormalFour (centralizer ({X} : Set NativeSporadic.B)) :=
  @noNormalFour_centralizer_of_isConj NativeSporadic.B Units.instGroup _ _
    (babyTableIII.2 1 (phiB xBar) X babyInv_one_phiB_xBar hX)
    noNormalFour_centralizer_phiB_xBar

end CFSG.EvenSporadicStandard.HypOne.BabyHyp
