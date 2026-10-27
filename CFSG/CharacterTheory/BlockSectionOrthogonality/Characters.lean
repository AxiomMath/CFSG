module

public import CFSG.CharacterTheory.Blocks.Defs
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

open CFSG
namespace CFSG.BlockSectionOrthogonality.Helpers

theorem irreducible_isClassFunction {G : Type*} [Group G] {character : G → ℂ}
    (hcharacter : character ∈ BlocksIrr G) : BlocksIsClassFunction character := by
  rcases hcharacter with ⟨space, hAdd, hModule, hFinite, representation, hIrr, rfl⟩
  exact representation.char_conj

theorem block_subset_irreducibles (m : Ideal BlocksAlgInt) (G : Type*) [Group G]
    {block : Set (G → ℂ)} (hblock : BlocksIsBlock m G block) : block ⊆ BlocksIrr G := by
  rcases hblock with ⟨character, hcharacter, rfl⟩
  exact fun _ hmember => hmember.1

theorem block_nonempty (m : Ideal BlocksAlgInt) (G : Type*) [Group G]
    {block : Set (G → ℂ)} (hblock : BlocksIsBlock m G block) : block.Nonempty := by
  rcases hblock with ⟨character, hcharacter, rfl⟩
  exact ⟨character, hcharacter, fun _ _ => Iff.rfl⟩

@[expose] noncomputable def characterPairingFunctional {G : Type*} [Group G] [Fintype G]
    (character : G → ℂ) : Module.Dual ℂ (G → ℂ) where
  toFun function := (Nat.card G : ℂ)⁻¹ * ∑ element, function element * character element⁻¹
  map_add' left right := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' scalar function := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    ring

theorem irreducible_characterPairing {G : Type*} [Group G] [Fintype G]
    {left right : G → ℂ} (hleft : left ∈ BlocksIrr G) (hright : right ∈ BlocksIrr G) :
    characterPairingFunctional right left = if left = right then 1 else 0 := by
  classical
  rcases hleft with ⟨leftSpace, hLeftAdd, hLeftModule, hLeftFinite,
    leftRepresentation, hLeftIrr, rfl⟩
  rcases hright with ⟨rightSpace, hRightAdd, hRightModule, hRightFinite,
    rightRepresentation, hRightIrr, rfl⟩
  let := hLeftIrr
  let := hRightIrr
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  change (Nat.card G : ℂ)⁻¹ * ∑ element,
    leftRepresentation.character element * rightRepresentation.character element⁻¹ = _
  rw [Representation.char_orthonormal]
  by_cases hEquiv : Nonempty (rightRepresentation.Equiv leftRepresentation)
  · have hEqual : leftRepresentation.character = rightRepresentation.character :=
      (Representation.char_iso hEquiv.some).symm
    simp [hEquiv, hEqual]
  · have hDifferent : leftRepresentation.character ≠ rightRepresentation.character := by
      intro hEqual
      have hSelf := Representation.char_orthonormal leftRepresentation leftRepresentation
      have hCross := Representation.char_orthonormal leftRepresentation rightRepresentation
      have hRefl : Nonempty (leftRepresentation.Equiv leftRepresentation) :=
        ⟨Representation.Equiv.refl leftRepresentation⟩
      rw [ite_eq_left hRefl] at hSelf
      rw [ite_eq_right hEquiv, ← hEqual] at hCross
      exact one_ne_zero (hSelf.symm.trans hCross)
    simp [hEquiv, hDifferent]

theorem irreducibles_linearIndependent (G : Type*) [Group G] [Finite G] :
    LinearIndependent ℂ (fun character : BlocksIrr G => (character : G → ℂ)) := by
  classical
  let := Fintype.ofFinite G
  apply LinearIndependent.of_pairwise_dual_eq_zero_one _
    (fun character : BlocksIrr G => characterPairingFunctional (character : G → ℂ))
  · intro left right hDifferent
    rw [irreducible_characterPairing right.property left.property, ite_eq_right]
    intro hEqual
    exact hDifferent (Subtype.ext hEqual.symm)
  · intro character
    rw [irreducible_characterPairing character.property character.property, ite_eq_left rfl]

theorem irreducibles_finite (G : Type*) [Group G] [Finite G] : (BlocksIrr G).Finite := by
  have hFinite := (irreducibles_linearIndependent G).finite_of_isNoetherian
  exact Set.toFinite (BlocksIrr G)

theorem block_finite (m : Ideal BlocksAlgInt) (G : Type*) [Group G] [Finite G]
    {block : Set (G → ℂ)} (hblock : BlocksIsBlock m G block) : block.Finite :=
  (irreducibles_finite G).subset (block_subset_irreducibles m G hblock)

end CFSG.BlockSectionOrthogonality.Helpers
