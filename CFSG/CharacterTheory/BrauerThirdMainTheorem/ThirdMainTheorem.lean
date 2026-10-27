module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.LargerCounterexample

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem principal_of_brauerCorr
    (prime : ℕ) (hprime : prime.Prime) (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (hprimeMem : (prime : BlocksAlgInt) ∈ m) (G : Type) [Group G] [Finite G]
    (subgroup overgroup : Subgroup G) (hpGroup : IsPGroup prime subgroup)
    (hsubgroup : subgroup ≤ overgroup)
    (hcentralizer : Subgroup.centralizer (subgroup : Set G) ≤ overgroup)
    (hnormalizer : overgroup ≤ Subgroup.normalizer (subgroup : Set G))
    {block : Set (overgroup → ℂ)} (hblock : BlocksIsBlock m overgroup block)
    (hcorrespondence : BlocksBrauerCorr m subgroup overgroup block (BlocksPrincipalBlock m G)) :
    block = BlocksPrincipalBlock m overgroup := by
  classical
  by_contra hnotPrincipal
  let candidates : ℕ → Prop := fun size =>
    ∃ candidate overgroup : Subgroup G, IsPGroup prime candidate ∧
      Nat.card candidate = size ∧ candidate ≤ overgroup ∧
      Subgroup.centralizer (candidate : Set G) ≤ overgroup ∧
      overgroup ≤ Subgroup.normalizer (candidate : Set G) ∧
      ∃ candidateBlock : Set (overgroup → ℂ), BlocksIsBlock m overgroup candidateBlock ∧
        candidateBlock ≠ BlocksPrincipalBlock m overgroup ∧
        BlocksBrauerCorr m candidate overgroup candidateBlock (BlocksPrincipalBlock m G)
  have hcandidate : candidates (Nat.card subgroup) :=
    ⟨subgroup, overgroup, hpGroup, rfl, hsubgroup, hcentralizer, hnormalizer,
      block, hblock, hnotPrincipal, hcorrespondence⟩
  have hmaximal : candidates (Nat.findGreatest candidates (Nat.card G)) :=
    Nat.findGreatest_spec (Subgroup.card_le_card_group subgroup) hcandidate
  obtain ⟨maximalSubgroup, maximalOvergroup, hpMaximal, hsize, hmaximalInclusion,
    hmaximalCentralizer, hmaximalNormalizer, maximalBlock, hmaximalBlock,
    hmaximalNotPrincipal, hmaximalCorr⟩ := hmaximal
  obtain ⟨normalizerBlock, hnormalizerBlock, hnormalizerNotPrincipal, hnormalizerCorr⟩ :=
    normalizer_counterexample_exists prime hprime m hm hprimeMem G maximalSubgroup maximalOvergroup
      hpMaximal hmaximalInclusion hmaximalCentralizer hmaximalNormalizer
      hmaximalBlock hmaximalNotPrincipal hmaximalCorr
  obtain ⟨larger, largerOvergroup, hpLarger, hcardLarger, hlargerInclusion,
    hlargerCentralizer, hlargerNormalizer, largerBlock, hlargerBlock,
    hlargerNotPrincipal, hlargerCorr⟩ := normalizer_counterexample_larger prime hprime m hm hprimeMem
      G maximalSubgroup hpMaximal hnormalizerBlock hnormalizerNotPrincipal hnormalizerCorr
  have hlargerCandidate : candidates (Nat.card larger) :=
    ⟨larger, largerOvergroup, hpLarger, rfl, hlargerInclusion, hlargerCentralizer,
      hlargerNormalizer, largerBlock, hlargerBlock, hlargerNotPrincipal, hlargerCorr⟩
  have hbound := Nat.le_findGreatest (Subgroup.card_le_card_group larger) hlargerCandidate
  rw [← hsize] at hbound
  exact (Nat.not_le_of_lt hcardLarger) hbound

end CFSG.BrauerThirdMainTheorem.Helpers
