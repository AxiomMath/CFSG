module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.SylowColumns.Restriction

public section

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical

section Sets

variable (A : Type) [Group A] [Finite A]

@[expose] noncomputable def irreducibleCharacters : Finset (A → ℂ) :=
  (blocksIrr_finite A).toFinset

@[expose] noncomputable def nonprincipalLinearCharacters : Finset (A → ℂ) :=
  (irreducibleCharacters A).filter (fun θ => θ 1 = 1 ∧ θ ≠ 1)

@[expose] noncomputable def degreeFourCharacters : Finset (A → ℂ) :=
  (irreducibleCharacters A).filter (fun θ => θ 1 = 4)

variable {A}

theorem mem_irreducibleCharacters {θ : A → ℂ} :
    θ ∈ irreducibleCharacters A ↔ θ ∈ CFSG.BlocksIrr A :=
  Set.Finite.mem_toFinset _

theorem mem_nonprincipalLinearCharacters {θ : A → ℂ} :
    θ ∈ nonprincipalLinearCharacters A ↔ θ ∈ CFSG.BlocksIrr A ∧ θ 1 = 1 ∧ θ ≠ 1 := by
  rw [nonprincipalLinearCharacters, Finset.mem_filter, mem_irreducibleCharacters]

theorem mem_degreeFourCharacters {θ : A → ℂ} :
    θ ∈ degreeFourCharacters A ↔ θ ∈ CFSG.BlocksIrr A ∧ θ 1 = 4 := by
  rw [degreeFourCharacters, Finset.mem_filter, mem_irreducibleCharacters]

end Sets

section Shape

variable {A : Type} [Group A] [Finite A]

theorem UnitaryFourSylowShape.exists_sign_of_linear (h : UnitaryFourSylowShape A) {θ : A → ℂ}
    (hθ : θ ∈ CFSG.BlocksIrr A) (h1 : θ 1 = 1) :
    ∃ l : A ⧸ Subgroup.center A →* ℤˣ,
      θ = fun s : A => (((l (s : A ⧸ Subgroup.center A) : ℤˣ) : ℤ) : ℂ) := by
  let := Fintype.ofFinite A
  obtain ⟨hlin, -⟩ := h.character_table
  have hmem : θ ∈ {χ | χ ∈ CFSG.BlocksIrr A ∧ χ 1 = 1} := ⟨hθ, h1⟩
  rw [hlin] at hmem
  obtain ⟨l, hl⟩ := hmem
  exact ⟨l, hl.symm⟩

theorem UnitaryFourSylowShape.linear_apply_center (h : UnitaryFourSylowShape A) {θ : A → ℂ}
    (hθ : θ ∈ CFSG.BlocksIrr A) (h1 : θ 1 = 1) {z : A} (hz : z ∈ Subgroup.center A) :
    θ z = 1 := by
  obtain ⟨l, rfl⟩ := h.exists_sign_of_linear hθ h1
  simp only
  rw [(QuotientGroup.eq_one_iff z).mpr hz]
  simp

theorem UnitaryFourSylowShape.linear_mul (h : UnitaryFourSylowShape A) {θ : A → ℂ}
    (hθ : θ ∈ CFSG.BlocksIrr A) (h1 : θ 1 = 1) (a b : A) : θ (a * b) = θ a * θ b := by
  obtain ⟨l, rfl⟩ := h.exists_sign_of_linear hθ h1
  simp only [QuotientGroup.mk_mul, map_mul, Units.val_mul, Int.cast_mul]

theorem UnitaryFourSylowShape.linear_apply_eq_one_or (h : UnitaryFourSylowShape A)
    {θ : A → ℂ} (hθ : θ ∈ CFSG.BlocksIrr A) (h1 : θ 1 = 1) (a : A) :
    θ a = 1 ∨ θ a = -1 := by
  obtain ⟨l, rfl⟩ := h.exists_sign_of_linear hθ h1
  rcases Int.units_eq_one_or (l (a : A ⧸ Subgroup.center A)) with h' | h' <;> simp [h']

theorem UnitaryFourSylowShape.degree_eq_one_or_four (h : UnitaryFourSylowShape A)
    {θ : A → ℂ} (hθ : θ ∈ CFSG.BlocksIrr A) : θ 1 = 1 ∨ θ 1 = 4 := by
  let := Fintype.ofFinite A
  obtain ⟨-, -, -, -, -, hover, hcases, -⟩ := h.character_table
  rcases hcases θ hθ with h1 | ⟨l, hl1, hl⟩
  · exact Or.inl h1
  · exact Or.inr (hover l hl1 θ hθ hl).1

theorem UnitaryFourSylowShape.degreeFour_apply_eq_zero (h : UnitaryFourSylowShape A)
    {θ : A → ℂ} (hθ : θ ∈ CFSG.BlocksIrr A) (h4 : θ 1 = 4) {x : A}
    (hx : x ∉ Subgroup.center A) : θ x = 0 := by
  let := Fintype.ofFinite A
  obtain ⟨-, -, -, -, -, hover, hcases, -⟩ := h.character_table
  rcases hcases θ hθ with h1 | ⟨l, hl1, hl⟩
  · rw [h4] at h1
    norm_num at h1
  · exact (hover l hl1 θ hθ hl).2.2 x hx

theorem UnitaryFourSylowShape.irreducibleCharacters_eq (h : UnitaryFourSylowShape A) :
    irreducibleCharacters A =
      insert 1 (nonprincipalLinearCharacters A ∪ degreeFourCharacters A) := by
  ext θ
  rw [Finset.mem_insert, Finset.mem_union, mem_irreducibleCharacters,
    mem_nonprincipalLinearCharacters, mem_degreeFourCharacters]
  constructor
  · intro hθ
    by_cases h1 : θ = 1
    · exact Or.inl h1
    · rcases h.degree_eq_one_or_four hθ with hd | hd
      · exact Or.inr (Or.inl ⟨hθ, hd, h1⟩)
      · exact Or.inr (Or.inr ⟨hθ, hd⟩)
  · rintro (rfl | ⟨hθ, -⟩ | ⟨hθ, -⟩)
    · exact one_mem_blocksIrr A
    · exact hθ
    · exact hθ

theorem one_not_mem_linear_union_degreeFour :
    (1 : A → ℂ) ∉ nonprincipalLinearCharacters A ∪ degreeFourCharacters A := by
  rw [Finset.mem_union, mem_nonprincipalLinearCharacters, mem_degreeFourCharacters]
  rintro (⟨-, -, h⟩ | ⟨-, h⟩)
  · exact h rfl
  · norm_num at h

theorem disjoint_linear_degreeFour :
    Disjoint (nonprincipalLinearCharacters A) (degreeFourCharacters A) := by
  rw [Finset.disjoint_left]
  intro θ h1 h4
  rw [mem_nonprincipalLinearCharacters] at h1
  rw [mem_degreeFourCharacters] at h4
  have h4' := h4.2
  rw [h1.2.1] at h4'
  norm_num at h4'

theorem sum_irreducibleCharacters_degree_mul (x : A) :
    ∑ θ ∈ irreducibleCharacters A, θ 1 * θ x = if x = 1 then (Nat.card A : ℂ) else 0 := by
  let := Fintype.ofFinite A
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := A)
  rw [← regular_character_sum basis x]
  symm
  refine Finset.sum_bij (fun label _ => (basis.representation label).character)
    (fun label _ => ?_) (fun a _ b _ hab => basis.distinct hab) (fun θ hθ => ?_)
    (fun label _ => rfl)
  · rw [mem_irreducibleCharacters]
    exact basis_character_mem_blocksIrr basis label
  · rw [mem_irreducibleCharacters, blocksIrr_eq_range_basis basis] at hθ
    obtain ⟨label, rfl⟩ := hθ
    exact ⟨label, Finset.mem_univ _, rfl⟩

theorem UnitaryFourSylowShape.card_nonprincipalLinearCharacters (h : UnitaryFourSylowShape A) :
    (nonprincipalLinearCharacters A).card = 15 := by
  let := Fintype.ofFinite A
  obtain ⟨-, -, hlin16, -⟩ := h.character_table
  have hset : {χ | χ ∈ CFSG.BlocksIrr A ∧ χ 1 = 1} =
      ((insert 1 (nonprincipalLinearCharacters A) : Finset (A → ℂ)) : Set (A → ℂ)) := by
    ext θ
    simp only [Set.mem_ofPred_eq, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe,
      mem_nonprincipalLinearCharacters]
    constructor
    · rintro ⟨hθ, h1⟩
      by_cases hθ1 : θ = 1
      · exact Or.inl hθ1
      · exact Or.inr ⟨hθ, h1, hθ1⟩
    · rintro (rfl | ⟨hθ, h1, -⟩)
      · exact ⟨one_mem_blocksIrr A, rfl⟩
      · exact ⟨hθ, h1⟩
  rw [hset, Set.ncard_coe_finset, Finset.card_insert_of_notMem] at hlin16
  · omega
  · rw [mem_nonprincipalLinearCharacters]
    exact fun h' => h'.2.2 rfl

theorem UnitaryFourSylowShape.ncard_blocksIrr (h : UnitaryFourSylowShape A) :
    (CFSG.BlocksIrr A).ncard = 19 := by
  let := Fintype.ofFinite A
  obtain ⟨-, -, -, -, -, -, -, hirr19, -⟩ := h.character_table
  exact hirr19

theorem UnitaryFourSylowShape.card_degreeFourCharacters (h : UnitaryFourSylowShape A) :
    (degreeFourCharacters A).card = 3 := by
  have hirr19 := h.ncard_blocksIrr
  have hcard : (irreducibleCharacters A).card = 19 := by
    rw [← hirr19, irreducibleCharacters, Set.ncard_eq_toFinset_card _ (blocksIrr_finite A)]
  rw [h.irreducibleCharacters_eq, Finset.card_insert_of_notMem one_not_mem_linear_union_degreeFour,
    Finset.card_union_of_disjoint disjoint_linear_degreeFour,
    h.card_nonprincipalLinearCharacters] at hcard
  omega

theorem UnitaryFourSylowShape.regular_split (h : UnitaryFourSylowShape A) (x : A) :
    1 + ∑ θ ∈ nonprincipalLinearCharacters A, θ x + 4 * ∑ θ ∈ degreeFourCharacters A, θ x =
      if x = 1 then 64 else 0 := by
  have hreg := sum_irreducibleCharacters_degree_mul x
  rw [h.irreducibleCharacters_eq, Finset.sum_insert one_not_mem_linear_union_degreeFour,
    Finset.sum_union disjoint_linear_degreeFour, h.card] at hreg
  have hL : ∑ θ ∈ nonprincipalLinearCharacters A, θ 1 * θ x =
      ∑ θ ∈ nonprincipalLinearCharacters A, θ x :=
    Finset.sum_congr rfl fun θ hθ => by rw [(mem_nonprincipalLinearCharacters.mp hθ).2.1, one_mul]
  have hD : ∑ θ ∈ degreeFourCharacters A, θ 1 * θ x =
      4 * ∑ θ ∈ degreeFourCharacters A, θ x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun θ hθ => by rw [(mem_degreeFourCharacters.mp hθ).2]
  rw [hL, hD] at hreg
  simp only [Pi.one_apply, one_mul] at hreg
  push_cast at hreg
  linear_combination hreg

theorem UnitaryFourSylowShape.sum_linear (h : UnitaryFourSylowShape A) (x : A) :
    ∑ θ ∈ nonprincipalLinearCharacters A, θ x =
      if x ∈ Subgroup.center A then 15 else -1 := by
  by_cases hx : x ∈ Subgroup.center A
  · rw [ite_eq_left hx, Finset.sum_congr rfl (fun θ hθ => h.linear_apply_center
      (mem_nonprincipalLinearCharacters.mp hθ).1 (mem_nonprincipalLinearCharacters.mp hθ).2.1 hx),
      Finset.sum_const, h.card_nonprincipalLinearCharacters]
    norm_num
  · rw [ite_eq_right hx]
    have hreg := h.regular_split x
    have hx1 : x ≠ 1 := fun h' => hx (h' ▸ Subgroup.one_mem _)
    rw [ite_eq_right hx1, Finset.sum_eq_zero (fun θ hθ => h.degreeFour_apply_eq_zero
      (mem_degreeFourCharacters.mp hθ).1 (mem_degreeFourCharacters.mp hθ).2 hx)] at hreg
    linear_combination hreg

theorem UnitaryFourSylowShape.sum_degreeFour (h : UnitaryFourSylowShape A) (x : A) :
    ∑ θ ∈ degreeFourCharacters A, θ x =
      if x = 1 then 12 else if x ∈ Subgroup.center A then -4 else 0 := by
  by_cases hx1 : x = 1
  · rw [ite_eq_left hx1, hx1, Finset.sum_congr rfl (fun θ hθ => (mem_degreeFourCharacters.mp hθ).2),
      Finset.sum_const, h.card_degreeFourCharacters]
    norm_num
  · rw [ite_eq_right hx1]
    by_cases hx : x ∈ Subgroup.center A
    · rw [ite_eq_left hx]
      have hreg := h.regular_split x
      rw [ite_eq_right hx1, h.sum_linear x, ite_eq_left hx] at hreg
      linear_combination hreg / 4
    · rw [ite_eq_right hx]
      exact Finset.sum_eq_zero (fun θ hθ => h.degreeFour_apply_eq_zero
        (mem_degreeFourCharacters.mp hθ).1 (mem_degreeFourCharacters.mp hθ).2 hx)

end Shape

section Multiplicities

variable {G : Type} [Group G]

theorem restriction_multiplicities [Finite G] (S : Subgroup G) {V : Type} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    ∃ m : (S → ℂ) → ℕ,
      (∀ x : S, ρ.character x = ∑ θ ∈ irreducibleCharacters S, (m θ : ℂ) * θ x) ∧
      ∀ θ ∈ CFSG.BlocksIrr S, ∀ n ∈ Subgroup.normalizer (S : Set G),
        m (conjugateCharacter S n θ) = m θ := by
  classical
  obtain ⟨size, θs, hθs, hsum⟩ := character_restrict_sum_irreducible S ρ
  let := Fintype.ofFinite S
  obtain ⟨m₀, hm₀, hexp⟩ := sum_irreducible_expansion
    (fun t : (irreducibleCharacters S : Set (S → ℂ)) => (t : S → ℂ)) Subtype.val_injective
    (fun t => mem_irreducibleCharacters.mp t.property)
    (fun χ hχ => ⟨⟨χ, mem_irreducibleCharacters.mpr hχ⟩, rfl⟩) θs hθs
  let m : (S → ℂ) → ℕ := fun θ =>
    if hθ : θ ∈ irreducibleCharacters S then m₀ ⟨θ, hθ⟩ else 0
  have hm : ∀ θ (hθ : θ ∈ irreducibleCharacters S), m θ = m₀ ⟨θ, hθ⟩ := by
    intro θ hθ
    simp only [m, dite_eq_left hθ]
  have hres : (fun x : S => ∑ k, θs k x) = fun x : S => ρ.character x := by
    funext x
    rw [hsum x]
  refine ⟨m, fun x => ?_, fun θ hθ n hn => ?_⟩
  · rw [hsum x, hexp x]
    rw [← Finset.sum_coe_sort (irreducibleCharacters S)]
    apply Finset.sum_congr rfl
    intro t _
    rw [hm t t.property]
  · have hθ' : θ ∈ irreducibleCharacters S := mem_irreducibleCharacters.mpr hθ
    have hnθ : conjugateCharacter S n θ ∈ irreducibleCharacters S :=
      mem_irreducibleCharacters.mpr (conjugateCharacter_mem_blocksIrr hn hθ)
    rw [hm _ hθ', hm _ hnθ]
    have h1 := hm₀ ⟨_, hnθ⟩
    have h2 := hm₀ ⟨_, hθ'⟩
    rw [hres] at h1 h2
    simp only at h1 h2
    have hinv : CFSG.Section1.scalarProduct S (fun x : S => ρ.character x)
        (conjugateCharacter S n θ) =
        CFSG.Section1.scalarProduct S (fun x : S => ρ.character x) θ := by
      rw [conjugateCharacter_eq_comp hn, scalarProduct_comp_mulEquiv]
      intro x
      change ρ.character (n⁻¹ * x * n) = ρ.character x
      have := Representation.char_conj ρ (x : G) n⁻¹
      rwa [inv_inv] at this
    rw [hinv] at h1
    exact_mod_cast h1.trans h2.symm

end Multiplicities

end CFSG.LyonsUnitaryFour
