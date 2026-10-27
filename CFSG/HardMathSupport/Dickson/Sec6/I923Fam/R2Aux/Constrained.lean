module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.Transport
public import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDownComp
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.Basic

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Dickson.Sec6.I923 CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux

theorem noL2Sub_of_constrained {G : Type} [Group G] [Finite G] (D Q : Subgroup G) (hQD : Q ≤ D)
    (hQn : ∀ g ∈ D, ∀ n ∈ Q, g * n * g⁻¹ ∈ Q) (hQp : IsPGroup 3 Q)
    (hsol : Group.IsSolvable ↥(D ⊓ Subgroup.centralizer (Q : Set G))) : NoL2Sub D := by
  intro A hA r hr hT
  exfalso
  have hcomm := CFSG.LocalAnalysis.GLTheoremA.AltDown.glaPComponent_commute_of_normal_isPGroup
    Nat.prime_three hA hQD hQn hQp
  have hAD : A ≤ D := hA.1
  have hAC : A ≤ D ⊓ Subgroup.centralizer (Q : Set G) := by
    refine le_inf hAD fun j hj => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact (hcomm j hj n hn).symm
  haveI : Group.IsSolvable ↥A :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hAC)
  have hne : A ≠ ⊥ := glaPComponent_ne_bot hA
  haveI : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).2 hne
  have hperf : ⁅A, A⁆ = A := glaPComponent_perfect hA
  haveI : Group.IsPerfect ↥A := Subgroup.isPerfect_iff.mpr hperf
  exact Group.IsPerfect.not_isSolvable ↥A inferInstance

end CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux
