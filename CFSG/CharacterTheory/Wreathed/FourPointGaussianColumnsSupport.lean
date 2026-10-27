module

public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicInversionColumns
public import CFSG.Dihedral.DisconnectedInvolutionGraph.IrreducibleDegree
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs

public noncomputable section

namespace CFSG.Wreathed.FourPointGaussianColumns

open CFSG.TwoRankLowerBound.Helpers

open scoped BigOperators Classical

@[expose] def imCoeff (i t : ℂ) : ℝ := t.im / i.im

theorem re_eq_zero_and_im_sq_eq_one {i : ℂ} (hi : i ^ 2 = -1) : i.re = 0 ∧ i.im ^ 2 = 1 := by
  have hre := congrArg Complex.re hi
  have him := congrArg Complex.im hi
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.one_re,
    Complex.neg_im, Complex.one_im, neg_zero] at hre him
  have h0 : i.re = 0 := by
    by_contra h
    have him0 : i.im = 0 := by
      have : 2 * i.re * i.im = 0 := by linarith
      rcases mul_eq_zero.mp this with h2 | h2
      · exact absurd (by linarith : i.re = 0) h
      · exact h2
    rw [him0] at hre
    nlinarith [sq_nonneg i.re]
  refine ⟨h0, ?_⟩
  rw [h0] at hre
  nlinarith

theorem im_ne_zero {i : ℂ} (hi : i ^ 2 = -1) : i.im ≠ 0 := by
  intro h
  have := (re_eq_zero_and_im_sq_eq_one hi).2
  rw [h] at this
  norm_num at this

theorem imCoeff_add_mul {i : ℂ} (hi : i ^ 2 = -1) (s k : ℝ) :
    imCoeff i ((s : ℂ) + k * i) = k := by
  have h0 := (re_eq_zero_and_im_sq_eq_one hi).1
  unfold imCoeff
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, h0,
    mul_zero, zero_add, add_zero]
  field_simp [im_ne_zero hi]

theorem imCoeff_conj (i t : ℂ) : imCoeff i (starRingEnd ℂ t) = -imCoeff i t := by
  unfold imCoeff
  rw [Complex.conj_im, neg_div]

theorem imCoeff_sub (i t t' : ℂ) : imCoeff i (t - t') = imCoeff i t - imCoeff i t' := by
  unfold imCoeff
  rw [Complex.sub_im, sub_div]

theorem imCoeff_one (i : ℂ) : imCoeff i 1 = 0 := by
  unfold imCoeff
  rw [Complex.one_im, zero_div]

theorem normSq_sub_sq_re {i : ℂ} (hi : i ^ 2 = -1) (t : ℂ) :
    Complex.normSq t - (t ^ 2).re = 2 * imCoeff i t ^ 2 := by
  have h1 := (re_eq_zero_and_im_sq_eq_one hi).2
  have hne := im_ne_zero hi
  unfold imCoeff
  rw [Complex.normSq_apply, sq t, Complex.mul_re, div_pow, h1, div_one]
  ring

theorem mul_conj_re_sub_mul_re {i : ℂ} (hi : i ^ 2 = -1) (t t' : ℂ) :
    (t * starRingEnd ℂ t').re - (t * t').re = 2 * imCoeff i t * imCoeff i t' := by
  have h1 := (re_eq_zero_and_im_sq_eq_one hi).2
  have hne := im_ne_zero hi
  unfold imCoeff
  rw [Complex.mul_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  field_simp
  rw [h1]
  ring

theorem isPrimitiveRoot_of_sq_eq_neg_one {i : ℂ} (hi : i ^ 2 = -1) : IsPrimitiveRoot i (2 ^ 2) := by
  have h4 : i ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hi]
    norm_num
  refine IsPrimitiveRoot.mk_of_lt i (by norm_num) (by simpa using h4) ?_
  intro l hl0 hl4
  have hl : l < 4 := by simpa using hl4
  interval_cases l
  · intro h
    rw [pow_one] at h
    rw [h] at hi
    norm_num at hi
  · rw [hi]
    norm_num
  · intro h
    have h' : i ^ 3 = i ^ 2 * i := by ring
    rw [h', hi] at h
    have hi1 : i = -1 := by linear_combination -h
    rw [hi1] at hi
    norm_num at hi

theorem isPrimitiveRoot_neg_one_two : IsPrimitiveRoot (-1 : ℂ) (2 ^ 1) := by
  rw [pow_one]
  exact IsPrimitiveRoot.neg_one 0 (by norm_num)

theorem exists_int_of_mem_adjoin_neg_one {t : ℂ}
    (ht : t ∈ Algebra.adjoin ℤ ({-1} : Set ℂ)) : ∃ k : ℤ, t = k := by
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨-1, by rw [hx]; push_cast; ring⟩
  | algebraMap r => exact ⟨r, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, rfl⟩ := hx
    obtain ⟨s', rfl⟩ := hy
    exact ⟨s + s', by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨s, rfl⟩ := hx
    obtain ⟨s', rfl⟩ := hy
    exact ⟨s * s', by push_cast; ring⟩

theorem exists_gaussian_of_mem_adjoin {i : ℂ} (hi : i ^ 2 = -1) {t : ℂ}
    (ht : t ∈ Algebra.adjoin ℤ ({i} : Set ℂ)) : ∃ s k : ℤ, t = s + k * i := by
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by rw [hx]; push_cast; ring⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, k, rfl⟩ := hx
    obtain ⟨s', k', rfl⟩ := hy
    exact ⟨s + s', k + k', by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨s, k, rfl⟩ := hx
    obtain ⟨s', k', rfl⟩ := hy
    exact ⟨s * s' - k * k', s * k' + k * s', by push_cast; linear_combination (k * k' : ℂ) * hi⟩

section Conjugation

variable {G : Type} [Group G] [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)

theorem characterSubsetIdempotent_coeff_sum (S : Finset basis.index) (g : G) :
    (characterSubsetIdempotent basis S).coeff g =
      ∑ l ∈ S, (basis.representation l).character 1 / (Nat.card G : ℂ) *
        (basis.representation l).character g⁻¹ := by
  simp only [characterSubsetIdempotent, characterIdempotentExpansion, MonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, MonoidAlgebra.coeff_smul, Finsupp.smul_apply,
    complexCharacterIdempotent_coeff, smul_eq_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

@[expose] def conjLabel (l : basis.index) : basis.index :=
  Classical.choose (CFSG.Semidihedral.Principal.CyclicInversion.exists_conj_label basis l)

theorem conjLabel_spec (l : basis.index) (g : G) :
    (basis.representation (conjLabel basis l)).character g =
      starRingEnd ℂ ((basis.representation l).character g) :=
  Classical.choose_spec (CFSG.Semidihedral.Principal.CyclicInversion.exists_conj_label basis l) g

theorem conjLabel_conjLabel (l : basis.index) : conjLabel basis (conjLabel basis l) = l :=
  basis.distinct (funext fun g => by
    change (basis.representation (conjLabel basis (conjLabel basis l))).character g =
      (basis.representation l).character g
    rw [conjLabel_spec, conjLabel_spec, Complex.conj_conj])

theorem conjLabel_eq_of_spec (l l' : basis.index)
    (h : ∀ g, (basis.representation l').character g =
      starRingEnd ℂ ((basis.representation l).character g)) : conjLabel basis l = l' :=
  basis.distinct (funext fun g => by
    change (basis.representation (conjLabel basis l)).character g =
      (basis.representation l').character g
    rw [conjLabel_spec, h])

theorem conjLabel_injective : Function.Injective (conjLabel basis) := fun l l' h => by
  rw [← conjLabel_conjLabel basis l, h, conjLabel_conjLabel]

theorem conj_character_one (l : basis.index) :
    starRingEnd ℂ ((basis.representation l).character 1) =
      (basis.representation l).character 1 := by
  rw [finite_character_conjugate_inverse, inv_one]

theorem characterSubsetAdmissible_image_conjLabel (ring : Subring ℂ) (S : Finset basis.index)
    (hS : characterSubsetAdmissible basis ring S) :
    characterSubsetAdmissible basis ring (S.image (conjLabel basis)) := by
  intro g
  have hcoeff : (characterSubsetIdempotent basis (S.image (conjLabel basis))).coeff g =
      (characterSubsetIdempotent basis S).coeff g⁻¹ := by
    rw [characterSubsetIdempotent_coeff_sum, characterSubsetIdempotent_coeff_sum,
      Finset.sum_image fun l _ l' _ h => conjLabel_injective basis h]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [conjLabel_spec, conjLabel_spec, conj_character_one, finite_character_conjugate_inverse,
      inv_inv]
  change (characterSubsetIdempotent basis (S.image (conjLabel basis))).coeff g ∈ ring
  rw [hcoeff]
  exact hS g⁻¹

theorem conjLabel_mem_coefficientBlock (ring : Subring ℂ) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (l : basis.index)
    (hl : l ∈ coefficientBlock basis ring principal) :
    conjLabel basis l ∈ coefficientBlock basis ring principal := by
  have hσp : conjLabel basis principal = principal := conjLabel_eq_of_spec basis _ _ fun g => by
    rw [hprincipal]
    simp
  rw [coefficientBlock_mem_iff] at hl ⊢
  intro S hS
  have h := hl _ (characterSubsetAdmissible_image_conjLabel basis ring S hS)
  have hmem : ∀ l', l' ∈ S.image (conjLabel basis) ↔ conjLabel basis l' ∈ S := by
    intro l'
    rw [Finset.mem_image]
    constructor
    · rintro ⟨l'', hl'', rfl⟩
      rwa [conjLabel_conjLabel]
    · intro h'
      exact ⟨_, h', conjLabel_conjLabel basis l'⟩
  rw [hmem, hmem, hσp] at h
  exact h

end Conjugation

theorem ker_eq_bot_of_character_ne_one {G : Type} [Group G] [IsSimpleGroup G]
    (data : FiniteComplexRepresentation G) (hirr : data.IsIrreducible)
    (hne : data.character ≠ 1) : MonoidHom.ker data.representation = ⊥ := by
  have : data.representation.IsIrreducible := hirr
  obtain ⟨g, hg⟩ :=
    CFSG.DisconnectedInvolutionGraph.Helpers.irreducible_nonprincipal_action_nontrivial
      data.representation fun h => hne h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.ker data.representation) with h | h
  · exact h
  · exact absurd (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top g)) hg

theorem sum_filter_neg_eq_sum_filter_pos {ι : Type*} (B : Finset ι) (σ : ι → ι)
    (hσB : ∀ χ ∈ B, σ χ ∈ B) (hσσ : ∀ χ, σ (σ χ) = χ) (f : ι → ℤ)
    (hf : ∀ χ ∈ B, f (σ χ) = -f χ) (g : ι → ℤ) (hg : ∀ χ ∈ B, g (σ χ) = g χ) :
    ∑ χ ∈ B.filter (fun χ => f χ < 0), g χ = ∑ χ ∈ B.filter (fun χ => 0 < f χ), g χ := by
  apply Finset.sum_nbij' σ σ
  · intro χ hχ
    simp only [Finset.mem_filter] at hχ ⊢
    exact ⟨hσB χ hχ.1, by rw [hf χ hχ.1]; linarith [hχ.2]⟩
  · intro χ hχ
    simp only [Finset.mem_filter] at hχ ⊢
    exact ⟨hσB χ hχ.1, by rw [hf χ hχ.1]; linarith [hχ.2]⟩
  · intro χ _
    exact hσσ χ
  · intro χ _
    exact hσσ χ
  · intro χ hχ
    simp only [Finset.mem_filter] at hχ
    exact (hg χ hχ.1).symm

theorem sum_eq_sum_pos_add_sum_neg_add_sum_zero {ι : Type*} (B : Finset ι) (f : ι → ℤ)
    (g : ι → ℤ) :
    ∑ χ ∈ B, g χ = ∑ χ ∈ B.filter (fun χ => 0 < f χ), g χ +
      ∑ χ ∈ B.filter (fun χ => f χ < 0), g χ + ∑ χ ∈ B.filter (fun χ => f χ = 0), g χ := by
  rw [← Finset.sum_filter_add_sum_filter_not B (fun χ => 0 < f χ),
    ← Finset.sum_filter_add_sum_filter_not (B.filter fun χ => ¬ 0 < f χ) (fun χ => f χ < 0),
    Finset.filter_filter, Finset.filter_filter, add_assoc]
  congr 2
  · apply Finset.sum_congr _ fun _ _ => rfl
    ext χ
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, -, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by omega, h2⟩
  · apply Finset.sum_congr _ fun _ _ => rfl
    ext χ
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by omega, by omega⟩

end CFSG.Wreathed.FourPointGaussianColumns
