module

public import CFSG.CharacterTheory.Blocks.InnerProduct

public noncomputable section

namespace CFSG

open TwoRankLowerBound.Helpers
open scoped BigOperators Classical

theorem blocksInnerProduct_self_re_nonneg {G : Type} [Group G] [Fintype G]
    (f : G → ℂ) : 0 ≤ (BlocksInnerProduct f f).re := by
  have hcard : (0 : ℝ) < Nat.card G := Nat.cast_pos.mpr Nat.card_pos
  have heq : (BlocksInnerProduct f f).re =
      (Nat.card G : ℝ)⁻¹ * ∑ x, Complex.normSq (f x) := by
    simp only [BlocksInnerProduct, Complex.mul_conj, ← Complex.ofReal_sum,
      ← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  rw [heq]
  exact mul_nonneg (inv_nonneg.mpr hcard.le)
    (Finset.sum_nonneg fun x _ => Complex.normSq_nonneg (f x))

theorem blocksInnerProduct_self_zero {G : Type} [Group G] [Fintype G]
    (f : G → ℂ) (hzero : BlocksInnerProduct f f = 0) : f = 0 := by
  have hsum : ∑ x, f x * starRingEnd ℂ (f x) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (inv_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne'))
  have hreal : ∑ x, Complex.normSq (f x) = 0 := by
    simpa only [Complex.re_sum, Complex.mul_conj, Complex.ofReal_re, Complex.zero_re]
      using congrArg Complex.re hsum
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun x (_ : x ∈ Finset.univ) => Complex.normSq_nonneg (f x))).mp hreal
  funext x
  exact Complex.normSq_eq_zero.mp (hterm x (Finset.mem_univ x))

theorem characterPairing_sub_right {G : Type} [Group G] [Fintype G]
    (f a b : G → ℂ) :
    characterPairing f (a - b) = characterPairing f a - characterPairing f b := by
  simp only [characterPairing, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem blocksInnerProduct_orthonormal_residual
    {G index : Type} [Group G] [Fintype G] [Fintype index] [DecidableEq index]
    (v : index → G → ℂ) (hv : ∀ i, v i ∈ BlocksVChar G)
    (horth : ∀ i j, BlocksInnerProduct (v i) (v j) = if i = j then 1 else 0)
    (f : G → ℂ) (hf : f ∈ BlocksVChar G) (coefficient : index → ℤ)
    (hcoefficient : ∀ i, BlocksInnerProduct f (v i) = (coefficient i : ℂ)) :
    BlocksInnerProduct
        (f - fun x => ∑ i, (coefficient i : ℂ) * v i x)
        (f - fun x => ∑ i, (coefficient i : ℂ) * v i x) =
      BlocksInnerProduct f f - ((∑ i, coefficient i ^ 2 : ℤ) : ℂ) := by
  let expansion : G → ℂ := fun x => ∑ i, (coefficient i : ℂ) * v i x
  have hexpansion : expansion ∈ BlocksVChar G := by
    have heq : expansion = ∑ i, coefficient i • v i := by
      funext x
      simp only [expansion, Finset.sum_apply, zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply]
    rw [heq]
    exact (BlocksVChar G).sum_mem fun i _ => (BlocksVChar G).zsmul_mem (hv i) _
  have hcoefficient' : ∀ i, characterPairing f (v i) = (coefficient i : ℂ) := by
    intro i
    rw [← blocksInnerProduct_eq_characterPairing _ (hv i)]
    exact hcoefficient i
  have horth' : ∀ i j, characterPairing (v i) (v j) = if i = j then 1 else 0 := by
    intro i j
    rw [← blocksInnerProduct_eq_characterPairing _ (hv j)]
    exact horth i j
  have hleft : characterPairing expansion f = ((∑ i, coefficient i ^ 2 : ℤ) : ℂ) := by
    rw [characterPairing_comm, characterPairing_expansion_right]
    simp only [hcoefficient', Int.cast_sum, pow_two, Int.cast_mul]
  have hright : characterPairing f expansion = ((∑ i, coefficient i ^ 2 : ℤ) : ℂ) := by
    rw [characterPairing_comm]
    exact hleft
  have hnorm : characterPairing expansion expansion = ((∑ i, coefficient i ^ 2 : ℤ) : ℂ) := by
    rw [characterPairing_expansion_left]
    have hpair : ∀ i, characterPairing (v i) expansion = (coefficient i : ℂ) := by
      intro i
      rw [characterPairing_expansion_right]
      simp [horth']
    simp only [hpair, Int.cast_sum, pow_two, Int.cast_mul]
  change BlocksInnerProduct (f - expansion) (f - expansion) = _
  rw [blocksInnerProduct_eq_characterPairing _ ((BlocksVChar G).sub_mem hf hexpansion),
    characterPairing_sub_left, characterPairing_sub_right, characterPairing_sub_right,
    hleft, hright, hnorm, ← blocksInnerProduct_eq_characterPairing _ hf]
  ring

theorem blocksVChar_norm_two_orthonormal_pair_connector
    {G : Type} [Group G] [Fintype G]
    (v : Fin 4 → G → ℂ) (hv : ∀ i, v i ∈ BlocksVChar G)
    (horth : ∀ i j, BlocksInnerProduct (v i) (v j) = if i = j then 1 else 0)
    {f : G → ℂ} (hf : f ∈ BlocksVChar G) (hnorm : BlocksInnerProduct f f = 2)
    (hfirst : BlocksInnerProduct f (v 0 - v 1) = 1)
    (hsecond : BlocksInnerProduct f (v 2 - v 3) = -1) :
    ∃ a b : G → ℂ, (a = v 0 ∨ a = -v 1) ∧ (b = v 2 ∨ b = -v 3) ∧ f = a - b := by
  choose coefficient hcoefficient using fun i => blocksInnerProduct_virtual_integer hf (hv i)
  let expansion : G → ℂ := fun x => ∑ i, (coefficient i : ℂ) * v i x
  have hresidual := blocksInnerProduct_orthonormal_residual v hv horth f hf
    coefficient hcoefficient
  change BlocksInnerProduct (f - expansion) (f - expansion) = _ at hresidual
  have hbound : (∑ i, coefficient i ^ 2 : ℤ) ≤ 2 := by
    have hnonneg := blocksInnerProduct_self_re_nonneg (f - expansion)
    rw [hresidual, hnorm] at hnonneg
    norm_num only [Complex.sub_re, Complex.intCast_re] at hnonneg
    have hnonneg' : (0 : ℤ) ≤ 2 - ∑ i, coefficient i ^ 2 := by exact_mod_cast hnonneg
    omega
  have hvalues : ∀ i, coefficient i = 0 ∨ coefficient i = 1 ∨ coefficient i = -1 := by
    intro i
    by_cases hzero : coefficient i = 0
    · exact Or.inl hzero
    · right
      have hle : coefficient i ^ 2 ≤ 2 :=
        (Finset.single_le_sum (fun j _ => sq_nonneg (coefficient j))
          (Finset.mem_univ i)).trans hbound
      exact sq_eq_one_iff.mp (Int.sq_eq_one_of_sq_le_three (by omega) hzero)
  have hdifference (i j : Fin 4) :
      BlocksInnerProduct f (v i - v j) = (coefficient i - coefficient j : ℤ) := by
    rw [blocksInnerProduct_eq_characterPairing _ ((BlocksVChar G).sub_mem (hv i) (hv j)),
      characterPairing_sub_right, ← blocksInnerProduct_eq_characterPairing _ (hv i),
      ← blocksInnerProduct_eq_characterPairing _ (hv j), hcoefficient, hcoefficient,
      Int.cast_sub]
  have hfirst' : coefficient 0 - coefficient 1 = 1 := by
    apply Int.cast_injective (α := ℂ)
    simpa only [Int.cast_one] using (hdifference 0 1).symm.trans hfirst
  have hsecond' : coefficient 2 - coefficient 3 = -1 := by
    apply Int.cast_injective (α := ℂ)
    simpa only [Int.cast_neg, Int.cast_one] using (hdifference 2 3).symm.trans hsecond
  have hfirstcases : (coefficient 0 = 1 ∧ coefficient 1 = 0) ∨
      (coefficient 0 = 0 ∧ coefficient 1 = -1) := by
    have := hvalues 0
    have := hvalues 1
    omega
  have hsecondcases : (coefficient 2 = -1 ∧ coefficient 3 = 0) ∨
      (coefficient 2 = 0 ∧ coefficient 3 = 1) := by
    have := hvalues 2
    have := hvalues 3
    omega
  have hsum : (∑ i, coefficient i ^ 2 : ℤ) = 2 := by
    rcases hfirstcases with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
      rcases hsecondcases with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;>
      norm_num [Fin.sum_univ_succ, h0, h1, h2, h3]
  have hequal : f = expansion := by
    apply sub_eq_zero.mp
    apply blocksInnerProduct_self_zero
    rw [hresidual, hnorm, hsum, Int.cast_ofNat, sub_self]
  rcases hfirstcases with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
    rcases hsecondcases with ⟨h2, h3⟩ | ⟨h2, h3⟩
  · refine ⟨v 0, v 2, Or.inl rfl, Or.inl rfl, ?_⟩
    funext x
    simpa [expansion, Fin.sum_univ_succ, h0, h1, h2, h3, sub_eq_add_neg] using congrFun hequal x
  · refine ⟨v 0, -v 3, Or.inl rfl, Or.inr rfl, ?_⟩
    funext x
    simpa [expansion, Fin.sum_univ_succ, h0, h1, h2, h3, sub_eq_add_neg] using congrFun hequal x
  · refine ⟨-v 1, v 2, Or.inr rfl, Or.inl rfl, ?_⟩
    funext x
    simpa [expansion, Fin.sum_univ_succ, h0, h1, h2, h3, sub_eq_add_neg] using congrFun hequal x
  · refine ⟨-v 1, -v 3, Or.inr rfl, Or.inr rfl, ?_⟩
    funext x
    simpa [expansion, Fin.sum_univ_succ, h0, h1, h2, h3, sub_eq_add_neg] using congrFun hequal x

end CFSG
