module

public import CFSG.CharacterTheory.PSL2Table

public section

namespace CFSG.PSL2Table

open CFSG.DirectProduct CFSG.BlockSectionOrthogonality.Helpers
open scoped MatrixGroups

theorem blocksIrr_eq_of_sum_degree_sq {G : Type} [Group G] [Fintype G] {X : Finset (G → ℂ)}
    (hX : ∀ χ ∈ X, χ ∈ BlocksIrr G) (hsum : ∑ χ ∈ X, χ 1 ^ 2 = (Nat.card G : ℂ)) :
    BlocksIrr G = X := by
  classical
  have hsub : X ⊆ (irreducibles_finite G).toFinset := fun χ hχ => by
    rw [Set.Finite.mem_toFinset]
    exact hX χ hχ
  have hrest : ∑ θ ∈ (irreducibles_finite G).toFinset \ X, θ 1 ^ 2 = 0 := by
    have h := Finset.sum_sdiff hsub (f := fun θ => θ 1 ^ 2)
    rw [sum_degree_sq_irr, hsum] at h
    linear_combination h
  have hempty := eq_empty_of_sum_degree_sq (fun θ hθ => by
    have := (Finset.mem_sdiff.mp hθ).1
    rwa [Set.Finite.mem_toFinset] at this) hrest
  ext θ
  constructor
  · intro hθ
    by_contra hθX
    have : θ ∈ (irreducibles_finite G).toFinset \ X := by
      rw [Finset.mem_sdiff, Set.Finite.mem_toFinset]
      exact ⟨hθ, hθX⟩
    rw [hempty] at this
    exact Finset.notMem_empty _ this
  · intro hθ
    exact hX θ hθ

section OrderTwo

variable {Z : Type} [Group Z] [Fintype Z] [DecidableEq Z]

@[expose] def signChar (Z : Type) [Group Z] [DecidableEq Z] : Z → ℂ :=
  fun z => if z = 1 then 1 else -1

omit [Fintype Z] [DecidableEq Z] in
theorem mul_self_of_card_two (hZ : Nat.card Z = 2) (a : Z) : a * a = 1 := by
  have : Finite Z := Nat.finite_of_card_ne_zero (by omega)
  rw [← sq, ← hZ]
  exact pow_card_eq_one'

omit [Fintype Z] [DecidableEq Z] in
theorem eq_of_ne_one_of_card_two (hZ : Nat.card Z = 2) {a b : Z} (ha : a ≠ 1) (hb : b ≠ 1) :
    a = b := by
  obtain ⟨x, y, hxy, hxy'⟩ := Nat.card_eq_two_iff.mp hZ
  have hmem : ∀ z : Z, z = x ∨ z = y := by
    intro z
    have : z ∈ ({x, y} : Set Z) := by rw [hxy']; trivial
    simpa using this
  have h1 : (1 : Z) = x ∨ (1 : Z) = y := hmem 1
  rcases hmem a with rfl | rfl <;> rcases hmem b with rfl | rfl <;> rcases h1 with h | h
  all_goals first | rfl | exact (ha h.symm).elim | exact (hb h.symm).elim

omit [Fintype Z] in
theorem signChar_mul (hZ : Nat.card Z = 2) (a b : Z) :
    signChar Z (a * b) = signChar Z a * signChar Z b := by
  simp only [signChar]
  by_cases ha : a = 1 <;> by_cases hb : b = 1
  · simp [ha, hb]
  · simp [ha, hb]
  · simp [ha, hb]
  · have hab : a * b = 1 := by
      rw [eq_of_ne_one_of_card_two hZ hb ha] at *
      exact mul_self_of_card_two hZ a
    simp [ha, hb, hab]

omit [Fintype Z] in
theorem signChar_mem_blocksIrr (hZ : Nat.card Z = 2) : signChar Z ∈ BlocksIrr Z :=
  CFSG.Wreathed.CentralSL2.monoidHom_mem_blocksIrr
    { toFun := signChar Z
      map_one' := by simp [signChar]
      map_mul' := signChar_mul hZ }

omit [Fintype Z] in
theorem one_ne_signChar (hZ : Nat.card Z = 2) : (1 : Z → ℂ) ≠ signChar Z := by
  intro h
  obtain ⟨x, y, hxy, -⟩ := Nat.card_eq_two_iff.mp hZ
  have ht : ∃ t : Z, t ≠ 1 := by
    by_cases hx : x = 1
    · exact ⟨y, fun hy => hxy (hx.trans hy.symm)⟩
    · exact ⟨x, hx⟩
  obtain ⟨t, ht⟩ := ht
  have := congrFun h t
  simp only [Pi.one_apply, signChar, ht, ↓reduceIte] at this
  norm_num at this

theorem blocksIrr_of_card_two (hZ : Nat.card Z = 2) : BlocksIrr Z = {1, signChar Z} := by
  classical
  have h := blocksIrr_eq_of_sum_degree_sq (X := {1, signChar Z}) (fun χ hχ => by
      rcases Finset.mem_insert.mp hχ with rfl | hχ
      · exact one_mem_blocksIrr Z
      · rw [Finset.mem_singleton.mp hχ]
        exact signChar_mem_blocksIrr hZ)
    (by
      rw [Finset.sum_pair (one_ne_signChar hZ), hZ]
      simp [signChar]
      norm_num)
  rw [h]
  simp

end OrderTwo

theorem blocksIrr_prod_card_two {Z : Type} [Group Z] [Fintype Z] [DecidableEq Z]
    (hZ : Nat.card Z = 2) (L : Type) [Group L] [Fintype L] :
    BlocksIrr (Z × L) = {χ | ∃ θ ∈ BlocksIrr L,
      χ = outerProductCharacter 1 θ ∨ χ = outerProductCharacter (signChar Z) θ} ∧
    (∀ ε ∈ ({1, signChar Z} : Set (Z → ℂ)), ∀ ε' ∈ ({1, signChar Z} : Set (Z → ℂ)),
      ∀ θ ∈ BlocksIrr L, ∀ θ' ∈ BlocksIrr L,
        outerProductCharacter ε θ = outerProductCharacter ε' θ' → ε = ε' ∧ θ = θ') := by
  obtain ⟨hbij, -⟩ := direct_product_irreducible_character_families Z L
  rw [blocksIrr_of_card_two hZ] at hbij
  refine ⟨?_, ?_⟩
  · ext χ
    constructor
    · intro hχ
      obtain ⟨⟨ε, θ⟩, ⟨hε, hθ⟩, rfl⟩ := hbij.surjOn hχ
      rcases hε with rfl | rfl
      · exact ⟨θ, hθ, Or.inl rfl⟩
      · exact ⟨θ, hθ, Or.inr rfl⟩
    · rintro ⟨θ, hθ, rfl | rfl⟩
      · exact hbij.mapsTo (show ((1 : Z → ℂ), θ) ∈ _ from ⟨Or.inl rfl, hθ⟩)
      · exact hbij.mapsTo (show (signChar Z, θ) ∈ _ from ⟨Or.inr rfl, hθ⟩)
  · intro ε hε ε' hε' θ hθ θ' hθ' h
    have := hbij.injOn (x₁ := (ε, θ)) (x₂ := (ε', θ')) ⟨hε, hθ⟩ ⟨hε', hθ'⟩ h
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

theorem outerProductCharacter_apply {Z L : Type} (ε : Z → ℂ) (θ : L → ℂ) (z : Z) (x : L) :
    outerProductCharacter ε θ (z, x) = ε z * θ x := rfl

theorem prod_psl2_character_table {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F} (hν : ¬ IsSquare ν)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {Z : Type} [Group Z] [Fintype Z] [DecidableEq Z]
    (hZ : Nat.card Z = 2) :
    BlocksIrr (Z × PSL(2, F)) = {χ | ∃ ε ∈ ({1, signChar Z} : Set (Z → ℂ)),
      ∃ θ : PSL(2, F) → ℂ,
      (θ = 1 ∨ θ = steinberg F ∨
        (∃ α : splitTorus F →* ℂˣ, α ^ 2 ≠ 1 ∧ θ = principal α) ∨
        (∃ β : nonsplitTorus ν →* ℂˣ, β ^ 2 ≠ 1 ∧ θ = discrete β) ∨
        θ = halfPlus hF ψ ν ∨ θ = halfMinus hF ψ ν) ∧ χ = outerProductCharacter ε θ} ∧
    (∀ ε ∈ ({1, signChar Z} : Set (Z → ℂ)), ∀ ε' ∈ ({1, signChar Z} : Set (Z → ℂ)),
      ∀ θ ∈ BlocksIrr PSL(2, F), ∀ θ' ∈ BlocksIrr PSL(2, F),
        outerProductCharacter ε θ = outerProductCharacter ε' θ' → ε = ε' ∧ θ = θ') := by
  obtain ⟨hIrr, hinj⟩ := blocksIrr_prod_card_two hZ PSL(2, F)
  have hL := (psl2_character_table hF hq hν hψ).1
  refine ⟨?_, hinj⟩
  rw [hIrr]
  ext χ
  constructor
  · rintro ⟨θ, hθ, h | h⟩
    · rw [hL] at hθ
      exact ⟨1, Or.inl rfl, θ, hθ, h⟩
    · rw [hL] at hθ
      exact ⟨signChar Z, Or.inr rfl, θ, hθ, h⟩
  · rintro ⟨ε, hε, θ, hθ, rfl⟩
    have hθ' : θ ∈ BlocksIrr PSL(2, F) := by
      rw [hL]
      exact hθ
    rcases hε with rfl | rfl
    · exact ⟨θ, hθ', Or.inl rfl⟩
    · exact ⟨θ, hθ', Or.inr rfl⟩

end CFSG.PSL2Table
