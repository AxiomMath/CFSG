module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FinalTheorem
public import CFSG.Dihedral.BrauerSuzuki
public import CFSG.ClassicalInvolution.QuaternionStructure.WitnessCore

public section

namespace CFSG.ClassicalInvolution

theorem exists_witness_of_not_isPGroup {G : Type*} [Group G] [Finite G] (J : Subgroup G)
    (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2))))
    (hnot : ¬ IsPGroup 2 (J ⧸ CFSG.Open.classicalInvolutionOddCore J)) :
    ∃ J' : Subgroup G, J' ≤ J ∧ (J'.subgroupOf J).Normal ∧
      CFSG.Open.classicalInvolutionWitness J' ∧
      ∃ S' : Sylow 2 J', ∃ r : ℕ, 3 ≤ r ∧
        Nonempty ((S' : Subgroup J') ≃* QuaternionGroup (2 ^ (r - 2))) := by
  obtain ⟨r, hr, hq⟩ := hS
  exact QuaternionStructure.exists_witness_of_not_isPGroup_of_hyps
    CFSG.GorensteinWalter.gorensteinWalter J S ⟨r, hr, hq⟩
    (fun t ht ho => CFSG.BrauerSuzuki.brauer_suzuki r hr S hq t ht ho) hnot

end CFSG.ClassicalInvolution
