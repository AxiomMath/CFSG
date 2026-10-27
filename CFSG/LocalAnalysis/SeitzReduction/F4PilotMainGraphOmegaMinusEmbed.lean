module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusEmbed

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG Subgroup Matrix
open CFSG.Assembly.LowTwoRank

variable (k : Type) [Field k]

@[expose] def minusVec : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → k :=
  Pi.single (Sum.inr (Sum.inr 0)) 1

@[expose] def minusEmb : Fin 3 ⊕ Fin 3 → Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 :=
  Sum.elim (fun i => Sum.inl i) fun i => Sum.inr (Sum.inl i)

theorem minusEmb_injective : Function.Injective minusEmb := by
  rintro (i | i) (j | j) h
  · exact congrArg Sum.inl (Sum.inl_injective h)
  · exact absurd h Sum.inl_ne_inr
  · exact absurd h Sum.inr_ne_inl
  · exact congrArg Sum.inr (Sum.inl_injective (Sum.inr_injective h))

theorem minusEmb_ne_u (j : Fin 3 ⊕ Fin 3) : minusEmb j ≠ Sum.inr (Sum.inr 0) := by
  rcases j with j | j
  · exact Sum.inl_ne_inr
  · intro h
    exact Sum.inl_ne_inr (Sum.inr_injective h)

theorem minusEmb_ne_w (j : Fin 3 ⊕ Fin 3) : minusEmb j ≠ Sum.inr (Sum.inr 1) := by
  rcases j with j | j
  · exact Sum.inl_ne_inr
  · intro h
    exact Sum.inl_ne_inr (Sum.inr_injective h)

theorem minusVec_minusEmb (j : Fin 3 ⊕ Fin 3) : minusVec k (minusEmb j) = 0 :=
  Pi.single_eq_of_ne (minusEmb_ne_u j) _

theorem statedQuadMinus_minusVec (b c : k) : StatedQuadMinus 4 k b c (minusVec k) = 1 := by
  simp [StatedQuadMinus, minusVec]

@[expose] def polarMinus (b : k) (x y : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → k) : k :=
  (∑ i : Fin 3, (x (minusEmb (Sum.inl i)) * y (minusEmb (Sum.inr i)) +
      x (minusEmb (Sum.inr i)) * y (minusEmb (Sum.inl i)))) +
    b * (x (Sum.inr (Sum.inr 0)) * y (Sum.inr (Sum.inr 1)) +
      x (Sum.inr (Sum.inr 1)) * y (Sum.inr (Sum.inr 0)))

theorem polarMinus_eq [CharP k 2] (b c : k) (x y : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → k) :
    polarMinus k b x y = StatedQuadMinus 4 k b c (x + y) - StatedQuadMinus 4 k b c x -
      StatedQuadMinus 4 k b c y := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  simp only [polarMinus, StatedQuadMinus, Pi.add_apply]
  have hs : ∑ i : Fin 3, (x (minusEmb (Sum.inl i)) * y (minusEmb (Sum.inr i)) +
      x (minusEmb (Sum.inr i)) * y (minusEmb (Sum.inl i))) =
      ∑ i : Fin (4 - 1), ((x (Sum.inl i) + y (Sum.inl i)) * (x (Sum.inr (Sum.inl i)) +
        y (Sum.inr (Sum.inl i))) - x (Sum.inl i) * x (Sum.inr (Sum.inl i)) -
          y (Sum.inl i) * y (Sum.inr (Sum.inl i))) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [minusEmb, Sum.elim_inl, Sum.elim_inr]
    ring
  rw [hs]
  simp only [Finset.sum_sub_distrib]
  linear_combination (-(x (Sum.inr (Sum.inr 0)) * y (Sum.inr (Sum.inr 0)) +
    c * x (Sum.inr (Sum.inr 1)) * y (Sum.inr (Sum.inr 1)))) * h2

variable {k}

theorem polarMinus_mulVec [CharP k 2] {b c : k}
    {A : Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k}
    (hA : ∀ x, StatedQuadMinus 4 k b c (A *ᵥ x) = StatedQuadMinus 4 k b c x)
    (x y : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → k) :
    polarMinus k b (A *ᵥ x) (A *ᵥ y) = polarMinus k b x y := by
  rw [polarMinus_eq k b c, polarMinus_eq k b c, ← mulVec_add, hA, hA, hA]

theorem polarMinus_minusVec (b : k) (z : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → k) :
    polarMinus k b z (minusVec k) = b * z (Sum.inr (Sum.inr 1)) := by
  rw [polarMinus]
  simp only [minusVec_minusEmb, mul_zero, add_zero, Finset.sum_const_zero, zero_add]
  simp [minusVec]

theorem dotProduct_minusVec (r : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → k) :
    r ⬝ᵥ minusVec k = r (Sum.inr (Sum.inr 0)) := by
  rw [minusVec, dotProduct_single, mul_one]

variable (k)

@[expose] def minusStab (b c : k) : Subgroup (GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) where
  carrier := {A | (∀ x, StatedQuadMinus 4 k b c ((A : Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2)
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) *ᵥ x) = StatedQuadMinus 4 k b c x) ∧
    (A : Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) *ᵥ
      minusVec k = minusVec k}
  mul_mem' {A B} hA hB := by
    refine ⟨fun x => ?_, ?_⟩
    · rw [Units.val_mul, ← mulVec_mulVec, hA.1, hB.1]
    · rw [Units.val_mul, ← mulVec_mulVec, hB.2, hA.2]
  one_mem' := ⟨fun x => by rw [Units.val_one, one_mulVec], by rw [Units.val_one, one_mulVec]⟩
  inv_mem' {A} hA := by
    have hinv : ∀ y, (A : Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2)
        (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) *ᵥ
        (((A⁻¹ : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) : Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕
          Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) *ᵥ y) = y :=
      fun y => by rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    refine ⟨fun x => ?_, ?_⟩
    · rw [← hA.1, hinv]
    · conv_lhs => rw [← hA.2]
      rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

variable {k}

theorem minusStab_col [CharP k 2] {b c : k} (hb : b ≠ 0)
    {A : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k} (hA : A ∈ minusStab k b c)
    (j : Fin 3 ⊕ Fin 3) :
    (A : Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k)
      (Sum.inr (Sum.inr 1)) (minusEmb j) = 0 := by
  have h := polarMinus_mulVec hA.1 (Pi.single (minusEmb j) 1) (minusVec k)
  rw [hA.2, polarMinus_minusVec, polarMinus_minusVec, mulVec_single_one,
    Pi.single_eq_of_ne (minusEmb_ne_w j).symm, mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left hb

theorem minusStab_row {b c : k} {A : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k}
    (hA : A ∈ minusStab k b c) (i : Fin 3 ⊕ Fin 3) :
    (A : Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k)
      (minusEmb i) (Sum.inr (Sum.inr 0)) = 0 := by
  have h := congrFun hA.2 (minusEmb i)
  rw [mulVec, dotProduct_minusVec, minusVec_minusEmb] at h
  exact h

theorem minusStab_submatrix_mul [CharP k 2] {b c : k} (hb : b ≠ 0)
    {A B : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k} (hA : A ∈ minusStab k b c)
    (hB : B ∈ minusStab k b c) :
    ((A * B : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) : Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2)
        (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k).submatrix minusEmb minusEmb =
      (A : Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2)
          (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k).submatrix minusEmb minusEmb *
        (B : Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2)
          (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k).submatrix minusEmb minusEmb := by
  ext i j
  have hcol := minusStab_col hb hB j
  have hrow := minusStab_row hA i
  simp only [submatrix_apply, Units.val_mul, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  rw [hrow, hcol, zero_mul, mul_zero, add_zero, add_zero]
  rfl

theorem minusStab_submatrix_symplectic [CharP k 2] {b c : k} (hb : b ≠ 0)
    {A : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k} (hA : A ∈ minusStab k b c) :
    ((A : Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2)
        (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k).submatrix minusEmb minusEmb)ᵀ *
        (fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k) *
        (A : Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2)
          (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k).submatrix minusEmb minusEmb =
      fromBlocks 0 1 (-1) 0 := by
  ext a a'
  rw [transpose_mul_spJ_mul_apply, spJ_apply]
  have h := polarMinus_mulVec hA.1 (Pi.single (minusEmb a) 1) (Pi.single (minusEmb a') 1)
  rw [mulVec_single_one, mulVec_single_one] at h
  unfold polarMinus at h
  simp only [Matrix.col_apply, minusStab_col hb hA a, minusStab_col hb hA a',
    Pi.single_eq_of_ne (minusEmb_ne_u a).symm, Pi.single_eq_of_ne (minusEmb_ne_w a).symm,
    Pi.single_eq_of_ne (minusEmb_ne_u a').symm, Pi.single_eq_of_ne (minusEmb_ne_w a').symm,
    mul_zero, zero_mul, add_zero] at h
  have hs : ∀ (x y : Fin 3 ⊕ Fin 3),
      (Pi.single (minusEmb x) (1 : k) : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → k) (minusEmb y) =
        (Pi.single x (1 : k) : Fin 3 ⊕ Fin 3 → k) y := fun x y => by
    simp only [Pi.single_apply, minusEmb_injective.eq_iff]
  simp only [hs] at h
  simp only [submatrix_apply, CharTwo.sub_eq_add]
  exact h

variable (k)

@[expose] noncomputable def resMinusMat [CharP k 2] {b c : k} (hb : b ≠ 0) :
    minusStab k b c →* Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k where
  toFun A := ((A : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) : Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕
    Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k).submatrix minusEmb minusEmb
  map_one' := by
    change ((1 : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) : Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕
      Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k).submatrix minusEmb minusEmb = 1
    rw [Units.val_one]
    exact Matrix.submatrix_one _ minusEmb_injective
  map_mul' A B := minusStab_submatrix_mul hb A.2 B.2

@[expose] noncomputable def resMinus [CharP k 2] {b c : k} (hb : b ≠ 0) :
    minusStab k b c →* StatedSp 3 k :=
  (resMinusMat k hb).toHomUnits.codRestrict (StatedSp 3 k) fun A => by
    rw [LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
    exact minusStab_submatrix_symplectic hb A.2

end CFSG.SeitzReduction.F4Pilot
