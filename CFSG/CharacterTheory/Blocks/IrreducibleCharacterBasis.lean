module

public import CFSG.CharacterTheory.BlockSectionOrthogonality.Characters
public import CFSG.CharacterTheory.Blocks.VirtualCharacterCoefficients

public section

open scoped BigOperators Classical

namespace CFSG

open TwoRankLowerBound.Helpers BlockSectionOrthogonality.Helpers

theorem blocksInnerProduct_sub_sum_smul {G : Type} [Group G] [Fintype G] {ι : Type*}
    (s : Finset ι) (f : G → ℂ) (c : ι → ℂ) (χ : ι → G → ℂ) (ψ : G → ℂ) :
    BlocksInnerProduct (f - ∑ i ∈ s, c i • χ i) ψ =
      BlocksInnerProduct f ψ - ∑ i ∈ s, c i * BlocksInnerProduct (χ i) ψ := by
  unfold BlocksInnerProduct
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul,
    Finset.sum_sub_distrib, Finset.sum_mul, mul_sub, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => ?_
  ring

theorem irreducible_character_basis (G : Type) [Group G] [Fintype G] :
    (∀ χ ∈ BlocksIrr G, ∀ ψ ∈ BlocksIrr G,
      BlocksInnerProduct χ ψ = if χ = ψ then 1 else 0) ∧
    LinearIndependent ℂ (fun χ : BlocksIrr G => (χ : G → ℂ)) ∧
    (∀ f : G → ℂ, BlocksIsClassFunction f ↔ f ∈ Submodule.span ℂ (BlocksIrr G)) ∧
    ∀ f : G → ℂ, BlocksIsClassFunction f →
      f = ∑ χ ∈ (irreducibles_finite G).toFinset, BlocksInnerProduct f χ • χ := by
  have horth : ∀ χ ∈ BlocksIrr G, ∀ ψ ∈ BlocksIrr G,
      BlocksInnerProduct χ ψ = if χ = ψ then 1 else 0 := by
    intro χ hχ ψ hψ
    have h := blocksInnerProduct_irreducible ⟨χ, hχ⟩ ⟨ψ, hψ⟩
    simpa only [Subtype.mk.injEq] using h
  have hexp : ∀ f : G → ℂ, BlocksIsClassFunction f →
      f = ∑ χ ∈ (irreducibles_finite G).toFinset, BlocksInnerProduct f χ • χ := by
    intro f hf
    obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
    set g := f - ∑ χ ∈ (irreducibles_finite G).toFinset, BlocksInnerProduct f χ • χ with hg
    have hgclass : ∀ x y : G, g (y * x * y⁻¹) = g x := by
      intro x y
      simp only [hg, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [hf x y]
      congr 1
      refine Finset.sum_congr rfl fun χ hχ => ?_
      rw [irreducible_isClassFunction ((irreducibles_finite G).mem_toFinset.mp hχ) x y]
    have hgzero : g = 0 := by
      apply basis.separates g hgclass
      intro label
      have hmem : (basis.representation label).character ∈ BlocksIrr G := by
        rw [blocksIrr_eq_irreducible_characters]
        exact ⟨basis.representation label, basis.irreducible label, rfl⟩
      rw [← blocksInnerProduct_eq_characterPairing _ (AddSubgroup.subset_closure hmem), hg,
        blocksInnerProduct_sub_sum_smul]
      rw [Finset.sum_eq_single_of_mem ((basis.representation label).character)
        ((irreducibles_finite G).mem_toFinset.mpr hmem)]
      · rw [horth _ hmem _ hmem]
        simp
      · intro χ hχ hne
        rw [horth _ ((irreducibles_finite G).mem_toFinset.mp hχ) _ hmem]
        simp [hne]
    exact sub_eq_zero.mp hgzero
  refine ⟨horth, irreducibles_linearIndependent G, fun f => ⟨fun hf => ?_, fun hf => ?_⟩, hexp⟩
  · rw [hexp f hf]
    exact Submodule.sum_mem _ fun χ hχ => Submodule.smul_mem _ _
      (Submodule.subset_span ((irreducibles_finite G).mem_toFinset.mp hχ))
  · induction hf using Submodule.span_induction with
    | mem x hx => exact irreducible_isClassFunction hx
    | zero => intro x y; rfl
    | add x y _ _ hx hy =>
      intro a b
      simp only [Pi.add_apply, hx a b, hy a b]
    | smul c x _ hx =>
      intro a b
      simp only [Pi.smul_apply, hx a b]

end CFSG
