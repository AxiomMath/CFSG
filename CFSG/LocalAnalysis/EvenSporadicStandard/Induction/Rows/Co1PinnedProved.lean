module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1PairK
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1RowAtlas

public noncomputable section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Co1Block
  CFSG.Sporadic.Co1Schreier
open scoped commutatorElement

theorem transport_pair {G H : Type*} [Group G] [Group H] (e : G ≃* H) (K₁ : Subgroup H) (a : H)
    (ha : orderOf a = 2) (hK : K₁ ≤ Subgroup.centralizer {a}) (hperf : ⁅K₁, K₁⁆ = K₁) (n : ℕ)
    (hcard : Nat.card K₁ = n) :
    ∃ (u : G) (K : Subgroup G), u * u = 1 ∧ u ≠ 1 ∧ (∀ k ∈ K, k * u = u * k) ∧
      ⁅K, K⁆ = K ∧ Nat.card K = n := by
  have hu : orderOf (e.symm a) = 2 :=
    (orderOf_injective e.symm.toMonoidHom e.symm.injective a).trans ha
  refine ⟨e.symm a, K₁.map e.symm.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← sq, ← hu]
    exact pow_orderOf_eq_one _
  · intro h
    rw [h, orderOf_one] at hu
    exact absurd hu (by norm_num)
  · rintro _ ⟨c, hc, rfl⟩
    show e.symm c * e.symm a = e.symm a * e.symm c
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 (hK hc)]
  · rw [← Subgroup.map_commutator, hperf]
  · rw [Subgroup.card_map_of_injective e.symm.injective, hcard]

section


theorem co1PinnedPair_native : ∃ (u : NativeSporadic.Co1) (K : Subgroup NativeSporadic.Co1),
    u * u = 1 ∧ u ≠ 1 ∧ (∀ k ∈ K, k * u = u * k) ∧ ⁅K, K⁆ = K ∧ Nat.card K = 251596800 := by
  obtain ⟨K₁, hperf, hcard⟩ := CFSG.EvenSporadicStandard.Co1Pair.exists_perfect_K₁
  exact @transport_pair NativeSporadic.Co1 GA Units.instGroup GA.toGroup co1MatEquiv
    (K₁.map C₁.subtype) a₁ orderOf_a₁ (Subgroup.map_subtype_le K₁)
    (by rw [← Subgroup.map_commutator, hperf]) _
    (by rw [Subgroup.card_map_of_injective C₁.subtype_injective, hcard])

theorem co1PinnedPair_proved : Co1PinnedPair := co1PinnedPair_native

end

end CFSG.EvenSporadicStandard.Induction
