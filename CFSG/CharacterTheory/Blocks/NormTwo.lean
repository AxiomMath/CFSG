module

public import CFSG.CharacterTheory.Blocks.VirtualCharacterCoefficients
public import CFSG.CharacterTheory.TwoRankLowerBound.VirtualNormOne

public noncomputable section

namespace CFSG

open TwoRankLowerBound.Helpers
open scoped BigOperators Classical

theorem integer_norm_two_two_coefficients {index : Type*} [Fintype index]
    (coefficient : index → ℤ) (hnorm : ∑ label, coefficient label ^ 2 = 2) :
    ∃ first second, first ≠ second ∧
      (coefficient first = 1 ∨ coefficient first = -1) ∧
      (coefficient second = 1 ∨ coefficient second = -1) ∧
      ∀ other, other ≠ first → other ≠ second → coefficient other = 0 := by
  have hexists : ∃ first, coefficient first ≠ 0 := by
    by_contra! hzero
    simp only [hzero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero] at hnorm
    norm_num at hnorm
  obtain ⟨first, hfirst⟩ := hexists
  have hbound : coefficient first ^ 2 ≤ 2 := by
    rw [← hnorm]
    exact Finset.single_le_sum (fun member _ => sq_nonneg (coefficient member))
      (Finset.mem_univ _)
  have hsquare : coefficient first ^ 2 = 1 :=
    Int.sq_eq_one_of_sq_le_three (by omega) hfirst
  have herase : (∑ member ∈ Finset.univ.erase first, coefficient member ^ 2) = 1 := by
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset index)
      (fun member => coefficient member ^ 2) (Finset.mem_univ first)
    rw [hnorm, hsquare] at hsplit
    omega
  have herase' : (∑ member : Finset.univ.erase first, coefficient member.val ^ 2) = 1 := by
    rwa [Finset.sum_subtype (Finset.univ.erase first) (by intros; rfl)] at herase
  obtain ⟨second, hsecond, houtside⟩ := integer_norm_one_single_coefficient
    (fun member : Finset.univ.erase first => coefficient member.val) herase'
  refine ⟨first, second.val, (Finset.mem_erase.mp second.property).1.symm,
    sq_eq_one_iff.mp hsquare, hsecond, ?_⟩
  intro other hnefirst hnesecond
  exact houtside ⟨other, Finset.mem_erase.mpr ⟨hnefirst, Finset.mem_univ _⟩⟩ (by
    intro hequal
    exact hnesecond (congrArg Subtype.val hequal))

theorem blocksVChar_norm_two_signed_irreducibles {G : Type} [Group G] [Fintype G]
    {f : G → ℂ} (hf : f ∈ BlocksVChar G) (hnorm : BlocksInnerProduct f f = 2) :
    ∃ (χ ψ : BlocksIrr G) (ε η : ℤ), χ ≠ ψ ∧ (ε = 1 ∨ ε = -1) ∧
      (η = 1 ∨ η = -1) ∧ f = (ε : ℂ) • (χ : G → ℂ) + (η : ℂ) • (ψ : G → ℂ) := by
  obtain ⟨n, hn, _⟩ := blocksVChar_exists_unique_expansion hf
  have hsum : (∑ χ ∈ n.support, n χ ^ 2 : ℤ) = 2 := by
    apply Int.cast_injective (α := ℂ)
    rw [Int.cast_ofNat, ← blocksInnerProduct_expansion_norm, hn]
    exact hnorm
  have hsum' : (∑ χ : n.support, n χ.val ^ 2 : ℤ) = 2 := by
    rwa [Finset.sum_subtype n.support (by intros; rfl)] at hsum
  obtain ⟨χ, ψ, hne, hχ, hψ, houtside⟩ := integer_norm_two_two_coefficients
    (fun χ : n.support => n χ.val) hsum'
  refine ⟨χ.val, ψ.val, n χ.val, n ψ.val,
    (fun hequal => hne (Subtype.ext hequal)), hχ, hψ, ?_⟩
  rw [← hn]
  funext x
  rw [blocksCharacterExpansion_apply]
  change (∑ ρ ∈ n.support, (n ρ : ℂ) * (ρ : G → ℂ) x) =
    (n χ.val : ℂ) * (χ.val : G → ℂ) x + (n ψ.val : ℂ) * (ψ.val : G → ℂ) x
  rw [← Finset.add_sum_erase n.support
    (fun ρ => (n ρ : ℂ) * (ρ : G → ℂ) x) χ.property]
  congr 1
  apply Finset.sum_eq_single ψ.val
  · intro ρ hρ hneψ
    have hneχ : (⟨ρ, (Finset.mem_erase.mp hρ).2⟩ : n.support) ≠ χ := by
      intro hequal
      exact (Finset.mem_erase.mp hρ).1 (congrArg Subtype.val hequal)
    have hneψ' : (⟨ρ, (Finset.mem_erase.mp hρ).2⟩ : n.support) ≠ ψ := by
      intro hequal
      exact hneψ (congrArg Subtype.val hequal)
    rw [houtside _ hneχ hneψ', Int.cast_zero, zero_mul]
  · intro hnot
    exact (hnot (Finset.mem_erase.mpr
      ⟨(fun hequal => hne (Subtype.ext hequal.symm)), ψ.property⟩)).elim

theorem blocksIrr_identity_re_pos {G : Type} [Group G] (χ : BlocksIrr G) :
    0 < ((χ : G → ℂ) 1).re := by
  have hχ := (Set.ext_iff.mp (blocksIrr_eq_irreducible_characters G) (χ : G → ℂ)).mp
    χ.property
  obtain ⟨ρ, hρ, hρχ⟩ := hχ
  have hdim : 0 < Module.finrank ℂ ρ.vector := by
    apply Nat.pos_of_ne_zero
    intro hzero
    apply irreducible_character_degree_ne_zero ρ hρ
    rw [FiniteComplexRepresentation.character, Representation.char_one, hzero, Nat.cast_zero]
  rw [← hρχ, FiniteComplexRepresentation.character, Representation.char_one,
    Complex.natCast_re]
  exact Nat.cast_pos.mpr hdim

theorem blocksVChar_degree_zero_norm_two_signed_difference
    {G : Type} [Group G] [Fintype G] {f : G → ℂ}
    (hf : f ∈ BlocksVChar G) (hnorm : BlocksInnerProduct f f = 2) (hdegree : f 1 = 0) :
    ∃ (χ ψ : BlocksIrr G) (ε : ℤ), χ ≠ ψ ∧ (ε = 1 ∨ ε = -1) ∧
      (χ : G → ℂ) 1 = (ψ : G → ℂ) 1 ∧
      f = (ε : ℂ) • (χ : G → ℂ) - (ε : ℂ) • (ψ : G → ℂ) := by
  obtain ⟨χ, ψ, ε, η, hne, hε, hη, hexpansion⟩ :=
    blocksVChar_norm_two_signed_irreducibles hf hnorm
  have hid : (ε : ℂ) * (χ : G → ℂ) 1 + (η : ℂ) * (ψ : G → ℂ) 1 = 0 := by
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hdegree] using
      (congrFun hexpansion 1).symm
  have hreal : (ε : ℝ) * ((χ : G → ℂ) 1).re +
      (η : ℝ) * ((ψ : G → ℂ) 1).re = 0 := by
    simpa only [Complex.add_re, Complex.mul_re, Complex.intCast_re,
      Complex.intCast_im, zero_mul, sub_zero, Complex.zero_re] using congrArg Complex.re hid
  have hχpos := blocksIrr_identity_re_pos χ
  have hψpos := blocksIrr_identity_re_pos ψ
  have hsigns : η = -ε := by
    rcases hε with hε | hε <;> rcases hη with hη | hη <;>
      norm_num [hε, hη] at hreal ⊢ <;> linarith
  have hεne : (ε : ℂ) ≠ 0 := by
    rcases hε with rfl | rfl <;> norm_num
  have hequal : (χ : G → ℂ) 1 = (ψ : G → ℂ) 1 := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp ?_).resolve_left hεne
    calc
      (ε : ℂ) * ((χ : G → ℂ) 1 - (ψ : G → ℂ) 1) =
          (ε : ℂ) * (χ : G → ℂ) 1 + (η : ℂ) * (ψ : G → ℂ) 1 := by
        rw [hsigns, Int.cast_neg]
        ring
      _ = 0 := hid
  refine ⟨χ, ψ, ε, hne, hε, hequal, ?_⟩
  simpa only [hsigns, Int.cast_neg, neg_smul, sub_eq_add_neg] using hexpansion

theorem blocksVChar_degree_zero_norm_two_orthonormal_difference
    {G : Type} [Group G] [Fintype G] {f : G → ℂ}
    (hf : f ∈ BlocksVChar G) (hnorm : BlocksInnerProduct f f = 2) (hdegree : f 1 = 0) :
    ∃ (χ ψ : BlocksIrr G) (ε : ℤ) (a b : G → ℂ),
      χ ≠ ψ ∧ (ε = 1 ∨ ε = -1) ∧ (χ : G → ℂ) 1 = (ψ : G → ℂ) 1 ∧
      a = (ε : ℂ) • (χ : G → ℂ) ∧ b = (ε : ℂ) • (ψ : G → ℂ) ∧
      a ∈ BlocksVChar G ∧ b ∈ BlocksVChar G ∧
      BlocksInnerProduct a a = 1 ∧ BlocksInnerProduct b b = 1 ∧
      BlocksInnerProduct a b = 0 ∧ BlocksInnerProduct b a = 0 ∧
      a 1 = b 1 ∧ f = a - b := by
  obtain ⟨χ, ψ, ε, hne, hε, hequal, hexpansion⟩ :=
    blocksVChar_degree_zero_norm_two_signed_difference hf hnorm hdegree
  have hχ : (χ : G → ℂ) ∈ BlocksVChar G := AddSubgroup.subset_closure χ.property
  have hψ : (ψ : G → ℂ) ∈ BlocksVChar G := AddSubgroup.subset_closure ψ.property
  have hχnorm : BlocksInnerProduct (χ : G → ℂ) (χ : G → ℂ) = 1 := by
    simp [blocksInnerProduct_irreducible]
  have hψnorm : BlocksInnerProduct (ψ : G → ℂ) (ψ : G → ℂ) = 1 := by
    simp [blocksInnerProduct_irreducible]
  have horth : BlocksInnerProduct (χ : G → ℂ) (ψ : G → ℂ) = 0 := by
    simp [blocksInnerProduct_irreducible, hne]
  have horth' : BlocksInnerProduct (ψ : G → ℂ) (χ : G → ℂ) = 0 := by
    simp [blocksInnerProduct_irreducible, hne.symm]
  have hneg (a b : G → ℂ) : BlocksInnerProduct (-a) (-b) = BlocksInnerProduct a b := by
    simp only [BlocksInnerProduct, Pi.neg_apply, map_neg, neg_mul_neg]
  rcases hε with rfl | rfl
  · refine ⟨χ, ψ, 1, (χ : G → ℂ), (ψ : G → ℂ), hne, Or.inl rfl, hequal,
      ?_, ?_, hχ, hψ, hχnorm, hψnorm, horth, horth', hequal, ?_⟩
    · simp only [Int.cast_one, one_smul]
    · simp only [Int.cast_one, one_smul]
    · simpa only [Int.cast_one, one_smul] using hexpansion
  · refine ⟨χ, ψ, -1, -(χ : G → ℂ), -(ψ : G → ℂ), hne, Or.inr rfl, hequal,
      ?_, ?_, (BlocksVChar G).neg_mem hχ, (BlocksVChar G).neg_mem hψ,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Int.cast_neg, Int.cast_one, neg_one_smul]
    · simp only [Int.cast_neg, Int.cast_one, neg_one_smul]
    · rwa [hneg]
    · rwa [hneg]
    · rwa [hneg]
    · rwa [hneg]
    · simpa only [Pi.neg_apply] using congrArg Neg.neg hequal
    · simpa only [Int.cast_neg, Int.cast_one, neg_one_smul] using hexpansion

end CFSG
