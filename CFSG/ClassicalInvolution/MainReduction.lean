module

public import CFSG.ClassicalInvolution.QuaternionStructure.Witness
public import CFSG.ClassicalInvolution.SubnormalClosure
public import CFSG.ClassicalInvolution.PerfectCase
public import CFSG.ClassicalInvolution.LBalance.Main

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open

theorem witnessOfNotTwoGroup : WitnessOfNotTwoGroup :=
  fun J S hS hnot => exists_witness_of_not_isPGroup J S hS hnot

theorem models_of_partOne_of_normalOddByQuaternion' (h1 : PartOne)
    (h2 : NormalOddByQuaternion)
    (G : Type) [Group G] [Finite G]
    [IsSimpleGroup (genFittingFStar G)]
    (hFnonab : ∃ a b : genFittingFStar G, a * b ≠ b * a)
    (z : G) (hz : orderOf z = 2)
    (J : Subgroup G) (hzJ : z ∈ J) (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    (classicalInvolutionWitness J → Blueprint.OddLieType (genFittingFStar G) ∨
      Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11) ∧
    (classicalInvolutionTightlyEmbedded J → Blueprint.OddLieType (genFittingFStar G) ∨
      Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11 ∨
      Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M12) :=
  models_of_partOne_of_normalOddByQuaternion h1 h2 witnessOfNotTwoGroup G hFnonab z hz J hzJ hJ
    S hS

theorem models_of_aschbacherCIT_of_normalOddByQuaternion (h1 : AschbacherCIT)
    (h2 : NormalOddByQuaternion)
    (G : Type) [Group G] [Finite G]
    [IsSimpleGroup (genFittingFStar G)]
    (hFnonab : ∃ a b : genFittingFStar G, a * b ≠ b * a)
    (z : G) (hz : orderOf z = 2)
    (J : Subgroup G) (hzJ : z ∈ J) (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    (classicalInvolutionWitness J → Blueprint.OddLieType (genFittingFStar G) ∨
      Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11) ∧
    (classicalInvolutionTightlyEmbedded J → Blueprint.OddLieType (genFittingFStar G) ∨
      Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11 ∨
      Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M12) :=
  models_of_partOne_of_normalOddByQuaternion' (partOne_of_aschbacherCIT h1) h2 G hFnonab z hz J
    hzJ hJ S hS

theorem models_of_l2PrimeBalance (hL : L2PrimeBalance) (hC : CITSimplePerfect)
    (hs : PartOneSolvable) (h2 : NormalOddByQuaternion)
    (G : Type) [Group G] [Finite G]
    [IsSimpleGroup (genFittingFStar G)]
    (hFnonab : ∃ a b : genFittingFStar G, a * b ≠ b * a)
    (z : G) (hz : orderOf z = 2)
    (J : Subgroup G) (hzJ : z ∈ J) (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    (classicalInvolutionWitness J → Blueprint.OddLieType (genFittingFStar G) ∨
      Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11) ∧
    (classicalInvolutionTightlyEmbedded J → Blueprint.OddLieType (genFittingFStar G) ∨
      Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11 ∨
      Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M12) :=
  models_of_partOne_of_normalOddByQuaternion' (partOne_of_l2PrimeBalance hL hC hs) h2 G hFnonab z
    hz J hzJ hJ S hS

theorem models_of_citSimplePerfect (hC : CITSimplePerfect) (hs : PartOneSolvable)
    (h2 : NormalOddByQuaternion)
    (G : Type) [Group G] [Finite G]
    [IsSimpleGroup (genFittingFStar G)]
    (hFnonab : ∃ a b : genFittingFStar G, a * b ≠ b * a)
    (z : G) (hz : orderOf z = 2)
    (J : Subgroup G) (hzJ : z ∈ J) (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    (classicalInvolutionWitness J → Blueprint.OddLieType (genFittingFStar G) ∨
      Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11) ∧
    (classicalInvolutionTightlyEmbedded J → Blueprint.OddLieType (genFittingFStar G) ∨
      Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11 ∨
      Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M12) :=
  models_of_l2PrimeBalance l2PrimeBalance hC hs h2 G hFnonab z hz J hzJ hJ S hS

end CFSG.ClassicalInvolution
