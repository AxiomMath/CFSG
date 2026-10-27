module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeAbstract
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic

open scoped commutatorElement
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect le_perfectJoin)

theorem exists_mem_ker_of_mem_perfectJoin {G A : Type*} [Group G] [CommGroup A] (J : Subgroup G)
    (φ : ↥J →* A) {x : G} (hx : x ∈ perfectJoin J) : ∃ hxJ : x ∈ J, φ ⟨x, hxJ⟩ = 1 := by
  set N : Subgroup G := φ.ker.map J.subtype with hN
  have hmem : ∀ y : G, y ∈ N ↔ ∃ hyJ : y ∈ J, φ ⟨y, hyJ⟩ = 1 := by
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, hz⟩
    · rintro ⟨hyJ, hy⟩
      exact ⟨⟨y, hyJ⟩, hy, rfl⟩
  have hle : perfectJoin J ≤ N := by
    have hUJ := perfectJoin_le J
    have hUp := perfectJoin_perfect J
    conv_lhs => rw [← hUp]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [hmem]
    refine ⟨?_, ?_⟩
    · exact J.mul_mem (J.mul_mem (J.mul_mem (hUJ ha) (hUJ hb)) (J.inv_mem (hUJ ha)))
        (J.inv_mem (hUJ hb))
    · have : (⟨⁅a, b⁆, _⟩ : ↥J) = ⁅(⟨a, hUJ ha⟩ : ↥J), (⟨b, hUJ hb⟩ : ↥J)⁆ := rfl
      rw [this, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)]
  exact (hmem x).1 (hle hx)

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic
