module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.KReduction
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBBlocks
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBLattice

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Fi22TwoB (Qbar Qbar_le_Cbar card_Cbar card_Qbar t1_mem_Qbar sq_mem_zpowers_t1
  commutator_mem_zpowers_t1 central_iff_mem_zpowers_t1 card_le_of_abelian cent_Qbar O2In_Cbar
  exists_quot_Cbar exists_perfect_Cbar)

theorem fi22TwoBFacts_holds :
    Fi22TwoBFacts :=
  ⟨Qbar,
    { card_C := by rw [card_Cbar]; norm_num
      Q_le := Qbar_le_Cbar
      card_Q := card_Qbar
      t1_mem := t1_mem_Qbar
      sq := fun _ hx => sq_mem_zpowers_t1 hx
      comm := fun _ hx _ hy => commutator_mem_zpowers_t1 hx hy
      center := fun _ hx => central_iff_mem_zpowers_t1 hx
      abelian := fun _ hB hab => card_le_of_abelian hB hab
      cent := cent_Qbar
      O2 := O2In_Cbar
      quot := exists_quot_Cbar
      perfect := exists_perfect_Cbar }⟩

theorem kFacts_holds :
    KFacts :=
  kFacts_of_fi22TwoBFacts fi22TwoBFacts_holds

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
