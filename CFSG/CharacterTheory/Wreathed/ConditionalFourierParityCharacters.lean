module

public import CFSG.CharacterTheory.Blocks.InnerProduct
public import CFSG.CharacterTheory.Wreathed.ConditionalFourierParityCore

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.ConditionalFourier

open CFSG.TwoRankLowerBound.Helpers

variable {G : Type} [Group G] [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)

theorem blocksInnerProduct_basis_character (l m : basis.index) :
    BlocksInnerProduct (basis.representation l).character (basis.representation m).character =
      if l = m then 1 else 0 := by
  have hm : (basis.representation m).character ∈ BlocksVChar G := by
    rw [blocksVChar_eq_virtualCharacters, Submodule.mem_toAddSubgroup]
    exact character_mem_virtualCharacters _
  rw [blocksInnerProduct_eq_characterPairing _ hm,
    characterPairing_irreducible _ _ (basis.irreducible l) (basis.irreducible m)]
  by_cases h : l = m
  · subst h
    simp
  · rw [ite_eq_right fun h' => h (basis.distinct h'), ite_eq_right h]

@[expose] noncomputable def basisDegree (ψ : basis.index) : ℤ :=
  Module.finrank ℂ (basis.representation ψ).vector

theorem basisDegree_cast (ψ : basis.index) :
    ((basisDegree basis ψ : ℤ) : ℂ) = (basis.representation ψ).character 1 := by
  rw [basisDegree, FiniteComplexRepresentation.character, Representation.char_one]
  push_cast
  rfl

theorem basisDegree_pos (ψ : basis.index) : 0 < basisDegree basis ψ := by
  have h := irreducible_character_degree_ne_zero _ (basis.irreducible ψ)
  rw [← basisDegree_cast] at h
  have h' : basisDegree basis ψ ≠ 0 := by exact_mod_cast h
  have hnn : 0 ≤ basisDegree basis ψ := by
    rw [basisDegree]
    positivity
  omega

theorem basisDegree_principal {principal : basis.index}
    (hprincipal : (basis.representation principal).character = 1) :
    basisDegree basis principal = 1 := by
  have h := basisDegree_cast basis principal
  rw [hprincipal, Pi.one_apply] at h
  exact_mod_cast h

@[expose] noncomputable def basisCombination (B : Finset basis.index) :
    (basis.index → ℤ) →+ (G → ℂ) where
  toFun e := ∑ ψ ∈ B, (e ψ : ℂ) • (basis.representation ψ).character
  map_zero' := by simp
  map_add' e e' := by
    simp only [Pi.add_apply, Int.cast_add, add_smul, Finset.sum_add_distrib]

variable {basis}

theorem basisCombination_apply (B : Finset basis.index) (e : basis.index → ℤ) :
    basisCombination basis B e = ∑ ψ ∈ B, (e ψ : ℂ) • (basis.representation ψ).character :=
  rfl

theorem basisCombination_congr (B : Finset basis.index) {e e' : basis.index → ℤ}
    (h : ∀ ψ ∈ B, e ψ = e' ψ) : basisCombination basis B e = basisCombination basis B e' :=
  Finset.sum_congr rfl fun ψ hψ => by rw [h ψ hψ]

theorem basisCombination_unitVector (B : Finset basis.index) {α : basis.index} (hα : α ∈ B) :
    basisCombination basis B (unitVector α) = (basis.representation α).character := by
  rw [basisCombination_apply]
  simp only [unitVector, Int.cast_ite, Int.cast_one, Int.cast_zero, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq' B α, ite_eq_left hα]

theorem basisCombination_one (B : Finset basis.index) (e : basis.index → ℤ) :
    basisCombination basis B e 1 = ((∑ ψ ∈ B, basisDegree basis ψ * e ψ : ℤ) : ℂ) := by
  rw [basisCombination_apply, Finset.sum_apply]
  push_cast
  exact Finset.sum_congr rfl fun ψ _ => by
    rw [Pi.smul_apply, smul_eq_mul, basisDegree_cast, mul_comm]

theorem blocksInnerProduct_basisCombination (B : Finset basis.index) (e e' : basis.index → ℤ) :
    BlocksInnerProduct (basisCombination basis B e) (basisCombination basis B e') =
      ((∑ ψ ∈ B, e ψ * e' ψ : ℤ) : ℂ) := by
  have hleft : ∀ g : G → ℂ, BlocksInnerProduct (basisCombination basis B e) g =
      ∑ l ∈ B, (e l : ℂ) * BlocksInnerProduct (basis.representation l).character g := by
    intro g
    simp only [basisCombination_apply, BlocksInnerProduct, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun x _ => by ring
  have hright : ∀ l : basis.index, BlocksInnerProduct (basis.representation l).character
      (basisCombination basis B e') = if l ∈ B then (e' l : ℂ) else 0 := by
    intro l
    have hexp : BlocksInnerProduct (basis.representation l).character
        (basisCombination basis B e') = ∑ m ∈ B, (e' m : ℂ) *
          BlocksInnerProduct (basis.representation l).character
            (basis.representation m).character := by
      simp only [basisCombination_apply, BlocksInnerProduct, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, map_sum, map_mul, map_intCast, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun x _ => by ring
    rw [hexp]
    simp only [blocksInnerProduct_basis_character, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
  rw [hleft]
  push_cast
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [hright l, ite_eq_left hl]

end CFSG.Wreathed.ConditionalFourier
