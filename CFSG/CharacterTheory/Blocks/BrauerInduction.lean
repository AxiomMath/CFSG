module

public import CFSG.CharacterTheory.Blocks.VirtualCharacterRing
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerInduction

public section

namespace CFSG

open TwoRankLowerBound.Helpers
open scoped BigOperators

@[expose] def BlocksElementaryInductionLattice (G : Type) [Group G] [Fintype G] :
    AddSubgroup (G → ℂ) :=
  AddSubgroup.closure {f | ∃ E : Subgroup G, BlocksBrauerElementary E ∧
    ∃ φ : E → ℂ, φ ∈ BlocksVChar E ∧ inducedFunction E φ = f}

theorem blocksElementaryInductionLattice_eq_native (G : Type) [Group G] [Fintype G] :
    BlocksElementaryInductionLattice G = (elementaryInductionLattice G).toAddSubgroup := by
  simp only [BlocksElementaryInductionLattice, elementaryInductionLattice,
    blocksBrauerElementary_iff, blocksVChar_eq_virtualCharacters,
    Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure]

theorem inducedFunction_mem_blocksVChar {G : Type} [Group G] [Fintype G]
    (E : Subgroup G) {φ : E → ℂ} (hφ : φ ∈ BlocksVChar E) :
    inducedFunction E φ ∈ BlocksVChar G := by
  rw [blocksVChar_eq_virtualCharacters, Submodule.mem_toAddSubgroup] at hφ ⊢
  exact inducedFunction_mem_virtualCharacters E hφ

theorem blocksElementaryInductionLattice_le_virtual (G : Type) [Group G] [Fintype G] :
    BlocksElementaryInductionLattice G ≤ BlocksVChar G := by
  rw [blocksElementaryInductionLattice_eq_native, blocksVChar_eq_virtualCharacters]
  exact elementaryInductionLattice_le_virtual

theorem blocksVChar_mul_elementaryInductionLattice {G : Type} [Group G] [Fintype G]
    {β y : G → ℂ} (hβ : β ∈ BlocksVChar G)
    (hy : y ∈ BlocksElementaryInductionLattice G) :
    β * y ∈ BlocksElementaryInductionLattice G := by
  rw [blocksVChar_eq_virtualCharacters, Submodule.mem_toAddSubgroup] at hβ
  rw [blocksElementaryInductionLattice_eq_native, Submodule.mem_toAddSubgroup] at hy ⊢
  exact virtual_mul_elementaryInductionLattice β y hβ hy

@[expose] def blocksElementaryInductionIdeal (G : Type) [Group G] [Fintype G] :
    Ideal (blocksVCharSubring G) where
  carrier := {y | (y : G → ℂ) ∈ BlocksElementaryInductionLattice G}
  zero_mem' := (BlocksElementaryInductionLattice G).zero_mem
  add_mem' := (BlocksElementaryInductionLattice G).add_mem
  smul_mem' := by
    intro β y hy
    exact blocksVChar_mul_elementaryInductionLattice β.property hy

theorem blocksElementaryInductionLattice_eq_virtual (G : Type) [Group G] [Fintype G] :
    BlocksElementaryInductionLattice G = BlocksVChar G := by
  rw [blocksElementaryInductionLattice_eq_native, elementaryInductionLattice_eq_virtual,
    blocksVChar_eq_virtualCharacters]

theorem blocksElementaryInductionLattice_exists_list {G : Type} [Group G] [Fintype G]
    {f : G → ℂ} (hf : f ∈ BlocksElementaryInductionLattice G) :
    ∃ l : List (G → ℂ),
      (∀ g ∈ l, ∃ E : Subgroup G, BlocksBrauerElementary E ∧
        ∃ φ : E → ℂ, φ ∈ BlocksVChar E ∧ inducedFunction E φ = g) ∧ l.sum = f := by
  let generators : Set (G → ℂ) := {g | ∃ E : Subgroup G, BlocksBrauerElementary E ∧
    ∃ φ : E → ℂ, φ ∈ BlocksVChar E ∧ inducedFunction E φ = g}
  have hneg : -generators ⊆ generators := by
    intro g hg
    obtain ⟨E, hE, φ, hφ, hφg⟩ := Set.mem_neg.mp hg
    refine ⟨E, hE, -φ, (BlocksVChar E).neg_mem hφ, ?_⟩
    change (inducedFunctionLinearMap E) (-φ) = g
    rw [map_neg]
    change -inducedFunction E φ = g
    rw [hφg, neg_neg]
  have hf' : f ∈ (AddSubgroup.closure generators).toAddSubmonoid := hf
  rw [AddSubgroup.closure_toAddSubmonoid, Set.union_eq_self_of_subset_right hneg] at hf'
  exact AddSubmonoid.exists_list_of_mem_closure hf'

theorem blocksVChar_exists_elementary_induction_sum {G : Type} [Group G] [Fintype G]
    {f : G → ℂ} (hf : f ∈ BlocksVChar G) :
    ∃ (r : ℕ) (E : Fin r → Subgroup G) (φ : (i : Fin r) → E i → ℂ),
      (∀ i, BlocksBrauerElementary (E i)) ∧ (∀ i, φ i ∈ BlocksVChar (E i)) ∧
      f = ∑ i, inducedFunction (E i) (φ i) := by
  classical
  rw [← blocksElementaryInductionLattice_eq_virtual] at hf
  obtain ⟨l, hl, hsum⟩ := blocksElementaryInductionLattice_exists_list hf
  choose E hE φ hφ hφg using fun i : Fin l.length => hl (l.get i) (l.get_mem i)
  refine ⟨l.length, E, φ, hE, hφ, ?_⟩
  simp only [hφg]
  rw [← List.sum_ofFn, List.ofFn_get]
  exact hsum.symm

end CFSG
