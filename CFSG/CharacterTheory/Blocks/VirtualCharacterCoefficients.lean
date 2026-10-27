module

public import CFSG.CharacterTheory.Blocks.InnerProduct

public section

namespace CFSG

open TwoRankLowerBound.Helpers
open scoped BigOperators Classical

@[expose] noncomputable def blocksCharacterExpansion (G : Type) [Group G] :
    (BlocksIrr G →₀ ℤ) →ₗ[ℤ] (G → ℂ) :=
  Finsupp.linearCombination ℤ Subtype.val

theorem blocksCharacterExpansion_apply {G : Type} [Group G]
    (n : BlocksIrr G →₀ ℤ) (x : G) :
    blocksCharacterExpansion G n x = ∑ χ ∈ n.support, (n χ : ℂ) * (χ : G → ℂ) x := by
  simp only [blocksCharacterExpansion, Finsupp.linearCombination_apply, Finsupp.sum,
    Finset.sum_apply, zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply]

theorem blocksInnerProduct_irreducible {G : Type} [Group G] [Fintype G]
    (χ ψ : BlocksIrr G) :
    BlocksInnerProduct (χ : G → ℂ) (ψ : G → ℂ) = if χ = ψ then 1 else 0 := by
  have hχ := (Set.ext_iff.mp (blocksIrr_eq_irreducible_characters G) (χ : G → ℂ)).mp χ.property
  have hψ := (Set.ext_iff.mp (blocksIrr_eq_irreducible_characters G) (ψ : G → ℂ)).mp ψ.property
  obtain ⟨ρ, hρ, hρχ⟩ := hχ
  obtain ⟨σ, hσ, hσψ⟩ := hψ
  rw [blocksInnerProduct_eq_characterPairing _ (AddSubgroup.subset_closure ψ.property)]
  simpa only [hρχ, hσψ, Subtype.ext_iff] using characterPairing_irreducible ρ σ hρ hσ

theorem blocksCharacterExpansion_mem_virtual {G : Type} [Group G]
    (n : BlocksIrr G →₀ ℤ) : blocksCharacterExpansion G n ∈ BlocksVChar G := by
  rw [blocksCharacterExpansion, Finsupp.linearCombination_apply]
  exact (BlocksVChar G).sum_mem fun χ _ =>
    (BlocksVChar G).zsmul_mem (AddSubgroup.subset_closure χ.property) (n χ)

theorem blocksInnerProduct_expansion_coefficient {G : Type} [Group G] [Fintype G]
    (n : BlocksIrr G →₀ ℤ) (ψ : BlocksIrr G) :
    BlocksInnerProduct (blocksCharacterExpansion G n) (ψ : G → ℂ) = (n ψ : ℂ) := by
  rw [blocksInnerProduct_eq_characterPairing _ (AddSubgroup.subset_closure ψ.property)]
  have hexpansion : blocksCharacterExpansion G n = fun x =>
      ∑ χ : n.support, (n χ.val : ℂ) * (χ.val : G → ℂ) x := by
    funext x
    rw [blocksCharacterExpansion_apply, Finset.sum_subtype n.support (by intros; rfl)]
  rw [hexpansion, characterPairing_expansion_left]
  have hpair : ∀ χ : n.support,
      characterPairing (χ.val : G → ℂ) (ψ : G → ℂ) = if χ.val = ψ then 1 else 0 := by
    intro χ
    rw [← blocksInnerProduct_eq_characterPairing _ (AddSubgroup.subset_closure ψ.property)]
    exact blocksInnerProduct_irreducible χ.val ψ
  simp only [hpair, mul_ite, mul_one, mul_zero]
  change (∑ χ : n.support, if χ.val = ψ then (n χ.val : ℂ) else 0) = (n ψ : ℂ)
  have hconvert := Finset.sum_subtype (p := fun χ : BlocksIrr G => χ ∈ n.support)
    (F := (inferInstance : Fintype n.support))
    n.support (by intros; rfl)
    (fun χ => if χ = ψ then (n χ : ℂ) else 0)
  rw [← hconvert]
  by_cases hψ : ψ ∈ n.support
  · simp [hψ]
  · simp [hψ, Finsupp.notMem_support_iff.mp hψ]

theorem blocksCharacterExpansion_injective (G : Type) [Group G] [Fintype G] :
    Function.Injective (blocksCharacterExpansion G) := by
  intro n m hequal
  ext χ
  have hcoeff := congrArg (fun f => BlocksInnerProduct f (χ : G → ℂ)) hequal
  simpa only [blocksInnerProduct_expansion_coefficient, Int.cast_inj] using hcoeff

theorem blocksVChar_exists_unique_expansion {G : Type} [Group G] [Fintype G]
    {f : G → ℂ} (hf : f ∈ BlocksVChar G) :
    ∃! n : BlocksIrr G →₀ ℤ, blocksCharacterExpansion G n = f := by
  have hf' : f ∈ (blocksCharacterExpansion G).range := by
    rw [blocksCharacterExpansion, Finsupp.range_linearCombination, Subtype.range_val]
    have hequal := Submodule.span_int_eq_addSubgroupClosure (BlocksIrr G)
    change f ∈ AddSubgroup.closure (BlocksIrr G) at hf
    rw [← hequal] at hf
    exact hf
  obtain ⟨n, hn⟩ := hf'
  exact ⟨n, hn, fun m hm => blocksCharacterExpansion_injective G (hm.trans hn.symm)⟩

theorem characterPairing_blocks_expansion_right {G : Type} [Group G] [Fintype G]
    (f : G → ℂ) (n : BlocksIrr G →₀ ℤ) :
    characterPairing f (blocksCharacterExpansion G n) =
      ∑ χ ∈ n.support, (n χ : ℂ) * characterPairing f (χ : G → ℂ) := by
  have hexpansion : blocksCharacterExpansion G n = fun x =>
      ∑ χ : n.support, (n χ.val : ℂ) * (χ.val : G → ℂ) x := by
    funext x
    rw [blocksCharacterExpansion_apply, Finset.sum_subtype n.support (by intros; rfl)]
  rw [hexpansion, characterPairing_expansion_right]
  exact (Finset.sum_subtype (p := fun χ : BlocksIrr G => χ ∈ n.support)
    (F := (inferInstance : Fintype n.support)) n.support (by intros; rfl)
      (fun χ => (n χ : ℂ) * characterPairing f (χ : G → ℂ))).symm

theorem blocksInnerProduct_expansions {G : Type} [Group G] [Fintype G]
    (n m : BlocksIrr G →₀ ℤ) :
    BlocksInnerProduct (blocksCharacterExpansion G n) (blocksCharacterExpansion G m) =
      ((∑ χ ∈ m.support, n χ * m χ : ℤ) : ℂ) := by
  rw [blocksInnerProduct_eq_characterPairing _ (blocksCharacterExpansion_mem_virtual m),
    characterPairing_blocks_expansion_right]
  have hcoefficient : ∀ χ : BlocksIrr G,
      characterPairing (blocksCharacterExpansion G n) (χ : G → ℂ) = (n χ : ℂ) := by
    intro χ
    rw [← blocksInnerProduct_eq_characterPairing _ (AddSubgroup.subset_closure χ.property)]
    exact blocksInnerProduct_expansion_coefficient n χ
  simp only [hcoefficient, Int.cast_sum, Int.cast_mul]
  exact Finset.sum_congr rfl fun χ _ => mul_comm _ _

theorem blocksInnerProduct_expansion_norm {G : Type} [Group G] [Fintype G]
    (n : BlocksIrr G →₀ ℤ) :
    BlocksInnerProduct (blocksCharacterExpansion G n) (blocksCharacterExpansion G n) =
      ((∑ χ ∈ n.support, n χ ^ 2 : ℤ) : ℂ) := by
  simpa only [pow_two] using blocksInnerProduct_expansions n n

end CFSG
