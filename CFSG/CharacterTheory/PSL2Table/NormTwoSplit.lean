module

public import CFSG.CharacterTheory.DirectProductCharacters
public import CFSG.CharacterTheory.Blocks.VirtualCharacterRing

public section

namespace CFSG.PSL2Table

open scoped BigOperators
open CFSG.TwoRankLowerBound.Helpers CFSG.BlockSectionOrthogonality.Helpers

variable {G : Type} [Group G] [Fintype G]

theorem bip_add_left (f f' g : G → ℂ) :
    BlocksInnerProduct (f + f') g = BlocksInnerProduct f g + BlocksInnerProduct f' g := by
  unfold BlocksInnerProduct
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem bip_smul_left (c : ℂ) (f g : G → ℂ) :
    BlocksInnerProduct (c • f) g = c * BlocksInnerProduct f g := by
  unfold BlocksInnerProduct
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  ring

theorem bip_neg_left (f g : G → ℂ) :
    BlocksInnerProduct (-f) g = -BlocksInnerProduct f g := by
  have := bip_smul_left (-1) f g
  simpa using this

theorem bip_sub_left (f f' g : G → ℂ) :
    BlocksInnerProduct (f - f') g = BlocksInnerProduct f g - BlocksInnerProduct f' g := by
  rw [sub_eq_add_neg, bip_add_left, bip_neg_left, ← sub_eq_add_neg]

theorem bip_conj_symm (f g : G → ℂ) :
    BlocksInnerProduct g f = starRingEnd ℂ (BlocksInnerProduct f g) := by
  unfold BlocksInnerProduct
  simp only [map_mul, map_sum, map_inv₀, map_natCast, Complex.conj_conj]
  congr 1
  exact Finset.sum_congr rfl (fun x _ => mul_comm _ _)

theorem bip_add_right (f g g' : G → ℂ) :
    BlocksInnerProduct f (g + g') = BlocksInnerProduct f g + BlocksInnerProduct f g' := by
  rw [bip_conj_symm, bip_add_left, map_add, ← bip_conj_symm, ← bip_conj_symm]

theorem bip_smul_right (c : ℂ) (f g : G → ℂ) :
    BlocksInnerProduct f (c • g) = starRingEnd ℂ c * BlocksInnerProduct f g := by
  rw [bip_conj_symm, bip_smul_left, map_mul, ← bip_conj_symm]

theorem bip_sub_right (f g g' : G → ℂ) :
    BlocksInnerProduct f (g - g') = BlocksInnerProduct f g - BlocksInnerProduct f g' := by
  rw [bip_conj_symm, bip_sub_left, map_sub, ← bip_conj_symm, ← bip_conj_symm]

omit [Fintype G] in
theorem exists_degree_of_mem_blocksIrr {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) :
    ∃ n : ℕ, 1 ≤ n ∧ χ 1 = n := by
  have hre : 0 < (χ 1).re := blocksIrr_identity_re_pos ⟨χ, hχ⟩
  obtain ⟨V, _, _, _, ρ, -, hρ⟩ := hχ
  refine ⟨Module.finrank ℂ V, ?_, by rw [← hρ, Representation.char_one]⟩
  have : (0 : ℝ) < Module.finrank ℂ V := by
    simpa [← hρ, Representation.char_one] using hre
  exact_mod_cast this

theorem sum_degree_sq_irr :
    ∑ χ ∈ (irreducibles_finite G).toFinset, χ 1 ^ 2 = (Nat.card G : ℂ) :=
  (CFSG.OddOrderBasics.regular_character_degree_square_sum G).2

theorem eq_empty_of_sum_degree_sq {s : Finset (G → ℂ)} (hs : ∀ χ ∈ s, χ ∈ BlocksIrr G)
    (hsum : ∑ χ ∈ s, χ 1 ^ 2 = 0) : s = ∅ := by
  by_contra hne
  obtain ⟨χ₀, hχ₀⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hre : ∀ χ ∈ s, (χ 1 ^ 2).re = ((χ 1).re) ^ 2 := by
    intro χ hχ
    obtain ⟨n, -, hn⟩ := exists_degree_of_mem_blocksIrr (hs χ hχ)
    rw [hn]
    norm_cast
  have hpos : 0 < ∑ χ ∈ s, (χ 1 ^ 2).re := by
    rw [Finset.sum_congr rfl hre]
    apply Finset.sum_pos'
    · intro χ _
      exact sq_nonneg _
    · exact ⟨χ₀, hχ₀, pow_pos (blocksIrr_identity_re_pos ⟨χ₀, hs χ₀ hχ₀⟩) 2⟩
  have h0 := congrArg Complex.re hsum
  rw [Complex.re_sum, Complex.zero_re] at h0
  linarith

theorem norm_two_split {X : Finset (G → ℂ)} (hX : ∀ χ ∈ X, χ ∈ BlocksIrr G) {d : ℕ} (hd : 0 < d)
    (hXsum : ∑ χ ∈ X, χ 1 ^ 2 = (Nat.card G : ℂ) - (d : ℂ) ^ 2 / 2)
    {Φ : G → ℂ} (hΦ : Φ ∈ BlocksVChar G) (hΦΦ : BlocksInnerProduct Φ Φ = 2)
    (hΦ1 : Φ 1 = d) (hΦX : ∀ χ ∈ X, BlocksInnerProduct Φ χ = 0) :
    ∃ χ ψ : G → ℂ, χ ∈ BlocksIrr G ∧ ψ ∈ BlocksIrr G ∧ χ ≠ ψ ∧ χ ∉ X ∧ ψ ∉ X ∧
      Φ = χ + ψ ∧ 2 * χ 1 = d ∧ 2 * ψ 1 = d ∧
      BlocksIrr G = (X : Set (G → ℂ)) ∪ {χ, ψ} := by
  classical
  obtain ⟨⟨χ, hχ⟩, ⟨ψ, hψ⟩, ε, η, hne, hε, hη, hΦeq⟩ :=
    blocksVChar_norm_two_signed_irreducibles hΦ hΦΦ
  have hne' : χ ≠ ψ := fun h => hne (Subtype.ext h)
  replace hΦeq : Φ = (ε : ℂ) • χ + (η : ℂ) • ψ := hΦeq
  have hχχ := CFSG.DirectProduct.blocksInnerProduct_of_mem hχ hχ
  have hψψ := CFSG.DirectProduct.blocksInnerProduct_of_mem hψ hψ
  have hχψ := CFSG.DirectProduct.blocksInnerProduct_of_mem hχ hψ
  have hψχ := CFSG.DirectProduct.blocksInnerProduct_of_mem hψ hχ
  rw [ite_eq_left rfl] at hχχ hψψ
  rw [ite_eq_right hne'] at hχψ
  rw [ite_eq_right (Ne.symm hne')] at hψχ
  have hεne : (ε : ℂ) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hηne : (η : ℂ) ≠ 0 := by rcases hη with rfl | rfl <;> norm_num
  have hχX : χ ∉ X := by
    intro h
    have := hΦX χ h
    rw [hΦeq, bip_add_left, bip_smul_left, bip_smul_left, hχχ, hψχ] at this
    simp only [mul_one, mul_zero, add_zero] at this
    exact hεne this
  have hψX : ψ ∉ X := by
    intro h
    have := hΦX ψ h
    rw [hΦeq, bip_add_left, bip_smul_left, bip_smul_left, hχψ, hψψ] at this
    simp only [mul_one, mul_zero, zero_add] at this
    exact hηne this
  obtain ⟨a, ha1, ha⟩ := exists_degree_of_mem_blocksIrr hχ
  obtain ⟨b, hb1, hb⟩ := exists_degree_of_mem_blocksIrr hψ
  have hdeg : (ε : ℂ) * a + η * b = d := by
    have := congrFun hΦeq 1
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ha, hb] at this
    rw [← this, hΦ1]
  set Y := insert χ (insert ψ X) with hY
  have hYsub : Y ⊆ (irreducibles_finite G).toFinset := by
    intro θ hθ
    rw [Set.Finite.mem_toFinset]
    rcases Finset.mem_insert.mp hθ with rfl | hθ
    · exact hχ
    rcases Finset.mem_insert.mp hθ with rfl | hθ
    · exact hψ
    · exact hX θ hθ
  have hYsum : ∑ θ ∈ Y, θ 1 ^ 2 =
      (a : ℂ) ^ 2 + (b : ℂ) ^ 2 + ((Nat.card G : ℂ) - (d : ℂ) ^ 2 / 2) := by
    rw [hY, Finset.sum_insert (by
        rw [Finset.mem_insert, not_or]
        exact ⟨hne', hχX⟩),
      Finset.sum_insert hψX, hXsum, ha, hb]
    ring
  have hrest : ∑ θ ∈ (irreducibles_finite G).toFinset \ Y, θ 1 ^ 2 =
      (d : ℂ) ^ 2 / 2 - (a : ℂ) ^ 2 - (b : ℂ) ^ 2 := by
    have h := Finset.sum_sdiff hYsub (f := fun θ => θ 1 ^ 2)
    rw [sum_degree_sq_irr, hYsum] at h
    linear_combination h
  have hrest_re : 0 ≤ ((d : ℝ) ^ 2 / 2 - (a : ℝ) ^ 2 - (b : ℝ) ^ 2) := by
    have h := congrArg Complex.re hrest
    rw [Complex.re_sum] at h
    have hnn : 0 ≤ ∑ θ ∈ (irreducibles_finite G).toFinset \ Y, (θ 1 ^ 2).re := by
      apply Finset.sum_nonneg
      intro θ hθ
      have hθirr : θ ∈ BlocksIrr G := by
        have := (Finset.mem_sdiff.mp hθ).1
        rwa [Set.Finite.mem_toFinset] at this
      obtain ⟨n, -, hn⟩ := exists_degree_of_mem_blocksIrr hθirr
      rw [hn]
      norm_cast
      positivity
    rw [h] at hnn
    have hcast : ((d : ℂ) ^ 2 / 2 - (a : ℂ) ^ 2 - (b : ℂ) ^ 2) =
        (((d : ℝ) ^ 2 / 2 - (a : ℝ) ^ 2 - (b : ℝ) ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rwa [hcast, Complex.ofReal_re] at hnn
  have hdeg_re : (ε : ℝ) * a + η * b = d := by
    have := congrArg Complex.re hdeg
    simpa using this
  have hεη : ε = 1 ∧ η = 1 := by
    have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    rcases hε with rfl | rfl <;> rcases hη with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · exfalso
      push_cast at hdeg_re
      nlinarith
    · exfalso
      push_cast at hdeg_re
      nlinarith
    · exfalso
      push_cast at hdeg_re
      nlinarith
  obtain ⟨rfl, rfl⟩ := hεη
  push_cast at hdeg_re
  have hab : (a : ℝ) = b := by nlinarith
  have hab' : 2 * (a : ℝ) = d := by linarith
  have hab'' : 2 * a = d := by exact_mod_cast hab'
  have habn : a = b := by exact_mod_cast hab
  have hempty : (irreducibles_finite G).toFinset \ Y = ∅ := by
    apply eq_empty_of_sum_degree_sq
    · intro θ hθ
      have := (Finset.mem_sdiff.mp hθ).1
      rwa [Set.Finite.mem_toFinset] at this
    · rw [hrest, ← habn]
      have : ((d : ℂ)) = 2 * a := by exact_mod_cast hab''.symm
      rw [this]
      ring
  refine ⟨χ, ψ, hχ, hψ, hne', hχX, hψX, ?_, ?_, ?_, ?_⟩
  · rw [hΦeq]
    simp
  · rw [ha]
    exact_mod_cast hab''
  · rw [hb, ← habn]
    exact_mod_cast hab''
  · ext θ
    constructor
    · intro hθ
      by_contra hθY
      have hθ' : θ ∈ (irreducibles_finite G).toFinset \ Y := by
        rw [Finset.mem_sdiff, Set.Finite.mem_toFinset]
        refine ⟨hθ, fun h => hθY ?_⟩
        rcases Finset.mem_insert.mp h with rfl | h
        · exact Or.inr (Or.inl rfl)
        rcases Finset.mem_insert.mp h with rfl | h
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl h
      rw [hempty] at hθ'
      exact Finset.notMem_empty _ hθ'
    · rintro (h | h | h)
      · exact hX θ h
      · rw [h]; exact hχ
      · rw [h]; exact hψ

theorem norm_two_difference {X : Finset (G → ℂ)} {χ ψ : G → ℂ} (hχ : χ ∈ BlocksIrr G)
    (hψ : ψ ∈ BlocksIrr G) (hne : χ ≠ ψ) (hχX : χ ∉ X) (hψX : ψ ∉ X)
    (hIrr : BlocksIrr G = (X : Set (G → ℂ)) ∪ {χ, ψ})
    {Ψ : G → ℂ} (hΨ : Ψ ∈ BlocksVChar G) (hΨΨ : BlocksInnerProduct Ψ Ψ = 2)
    (hΨX : ∀ θ ∈ X, BlocksInnerProduct Ψ θ = 0)
    (hΨΦ : BlocksInnerProduct Ψ (χ + ψ) = 0) :
    Ψ = χ - ψ ∨ Ψ = ψ - χ := by
  classical
  have hclass := blocksVChar_isClassFunction hΨ
  have hexp := (CFSG.irreducible_character_basis G).2.2.2 Ψ hclass
  have hfin : (irreducibles_finite G).toFinset = insert χ (insert ψ X) := by
    ext θ
    rw [Set.Finite.mem_toFinset, hIrr]
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff,
      Finset.mem_insert]
    tauto
  rw [hfin, Finset.sum_insert (by
      rw [Finset.mem_insert, not_or]
      exact ⟨hne, hχX⟩),
    Finset.sum_insert hψX, Finset.sum_eq_zero (fun θ hθ => by rw [hΨX θ hθ, zero_smul]),
    add_zero] at hexp
  obtain ⟨m, hm⟩ := blocksInnerProduct_virtual_integer hΨ (AddSubgroup.subset_closure hχ)
  obtain ⟨n, hn⟩ := blocksInnerProduct_virtual_integer hΨ (AddSubgroup.subset_closure hψ)
  rw [hm, hn] at hexp
  have hχχ := CFSG.DirectProduct.blocksInnerProduct_of_mem hχ hχ
  have hψψ := CFSG.DirectProduct.blocksInnerProduct_of_mem hψ hψ
  have hχψ := CFSG.DirectProduct.blocksInnerProduct_of_mem hχ hψ
  have hψχ := CFSG.DirectProduct.blocksInnerProduct_of_mem hψ hχ
  rw [ite_eq_left rfl] at hχχ hψψ
  rw [ite_eq_right hne] at hχψ
  rw [ite_eq_right (Ne.symm hne)] at hψχ
  have hsum : (m : ℂ) + n = 0 := by
    rw [bip_add_right, hm, hn] at hΨΦ
    exact hΨΦ
  have hsq : (m : ℂ) * m + n * n = 2 := by
    have h := hΨΨ
    nth_rewrite 2 [hexp] at h
    rw [bip_add_right, bip_smul_right, bip_smul_right, hm, hn] at h
    simp only [map_intCast] at h
    linear_combination h
  have hmn : m + n = 0 := by exact_mod_cast hsum
  have hmn2 : m * m + n * n = 2 := by exact_mod_cast hsq
  have hn' : n = -m := by linarith
  rw [hn'] at hmn2
  have hm2 : m * m = 1 := by nlinarith
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hm2 with h | h
  · left
    rw [hexp, hn', h]
    funext x
    simp
    ring
  · right
    rw [hexp, hn', h]
    funext x
    simp
    ring

end CFSG.PSL2Table
