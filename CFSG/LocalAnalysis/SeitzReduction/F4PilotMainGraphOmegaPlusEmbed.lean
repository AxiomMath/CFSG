module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFactBlock
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSetup

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG Subgroup Matrix
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.OmegaPilot (diagOmega isometryClosure isometry_of_mem_isometryClosure)

variable (k : Type) [Field k]

@[expose] def omegaPlusVec : Fin 4 ⊕ Fin 4 → k :=
  Pi.single (Sum.inl 3) 1 + Pi.single (Sum.inr 3) 1

@[expose] def plusEmb : Fin 3 ⊕ Fin 3 → Fin 4 ⊕ Fin 4 := Sum.map Fin.castSucc Fin.castSucc

theorem plusEmb_injective : Function.Injective plusEmb :=
  Sum.map_injective.2 ⟨Fin.castSucc_injective 3, Fin.castSucc_injective 3⟩

theorem plusEmb_ne_inl_three (j : Fin 3 ⊕ Fin 3) : plusEmb j ≠ Sum.inl 3 := by
  rcases j with j | j
  · intro h
    have := Sum.inl_injective h
    exact absurd this (Fin.castSucc_ne_last j)
  · exact Sum.inr_ne_inl

theorem plusEmb_ne_inr_three (j : Fin 3 ⊕ Fin 3) : plusEmb j ≠ Sum.inr 3 := by
  rcases j with j | j
  · exact Sum.inl_ne_inr
  · intro h
    have := Sum.inr_injective h
    exact absurd this (Fin.castSucc_ne_last j)

theorem omegaPlusVec_inl (i : Fin 4) : omegaPlusVec k (Sum.inl i) = if i = 3 then 1 else 0 := by
  by_cases hi : i = 3
  · subst hi
    simp [omegaPlusVec]
  · simp [omegaPlusVec, hi]

theorem omegaPlusVec_inr (i : Fin 4) : omegaPlusVec k (Sum.inr i) = if i = 3 then 1 else 0 := by
  by_cases hi : i = 3
  · subst hi
    simp [omegaPlusVec]
  · simp [omegaPlusVec, hi]

theorem castSucc_ne_three (j : Fin 3) : Fin.castSucc j ≠ (3 : Fin 4) := by
  fin_cases j <;> decide

theorem omegaPlusVec_plusEmb (j : Fin 3 ⊕ Fin 3) : omegaPlusVec k (plusEmb j) = 0 := by
  rcases j with j | j
  · rw [plusEmb, Sum.map_inl, omegaPlusVec_inl]
    exact ite_eq_right_iff.mpr fun h => absurd h (castSucc_ne_three j)
  · rw [plusEmb, Sum.map_inr, omegaPlusVec_inr]
    exact ite_eq_right_iff.mpr fun h => absurd h (castSucc_ne_three j)

theorem statedQuadPlus_omegaPlusVec : StatedQuadPlus 4 k (omegaPlusVec k) = 1 := by
  simp only [StatedQuadPlus, omegaPlusVec_inl, omegaPlusVec_inr, Fin.sum_univ_four]
  simp

@[expose] def polarPlus (x y : Fin 4 ⊕ Fin 4 → k) : k :=
  ∑ i, (x (Sum.inl i) * y (Sum.inr i) + x (Sum.inr i) * y (Sum.inl i))

theorem polarPlus_eq (x y : Fin 4 ⊕ Fin 4 → k) :
    polarPlus k x y = StatedQuadPlus 4 k (x + y) - StatedQuadPlus 4 k x - StatedQuadPlus 4 k y := by
  simp only [polarPlus, StatedQuadPlus, Pi.add_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

variable {k}

theorem polarPlus_mulVec {A : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k}
    (hA : ∀ x, StatedQuadPlus 4 k (A *ᵥ x) = StatedQuadPlus 4 k x) (x y : Fin 4 ⊕ Fin 4 → k) :
    polarPlus k (A *ᵥ x) (A *ᵥ y) = polarPlus k x y := by
  rw [polarPlus_eq, polarPlus_eq, ← mulVec_add, hA, hA, hA]

theorem polarPlus_omegaPlusVec (z : Fin 4 ⊕ Fin 4 → k) :
    polarPlus k z (omegaPlusVec k) = z (Sum.inl 3) + z (Sum.inr 3) := by
  simp only [polarPlus, omegaPlusVec_inl, omegaPlusVec_inr, Fin.sum_univ_four]
  simp

theorem dotProduct_omegaPlusVec (r : Fin 4 ⊕ Fin 4 → k) :
    r ⬝ᵥ omegaPlusVec k = r (Sum.inl 3) + r (Sum.inr 3) := by
  simp only [dotProduct, Fintype.sum_sum_type, omegaPlusVec_inl, omegaPlusVec_inr,
    Fin.sum_univ_four]
  simp

theorem polarPlus_split (x y : Fin 4 ⊕ Fin 4 → k) :
    polarPlus k x y = (∑ i : Fin 3, (x (plusEmb (Sum.inl i)) * y (plusEmb (Sum.inr i)) +
      x (plusEmb (Sum.inr i)) * y (plusEmb (Sum.inl i)))) +
        (x (Sum.inl 3) * y (Sum.inr 3) + x (Sum.inr 3) * y (Sum.inl 3)) := by
  rw [polarPlus, Fin.sum_univ_castSucc]
  rfl

variable (k)

@[expose] def plusStab : Subgroup (GL (Fin 4 ⊕ Fin 4) k) where
  carrier := {A | (∀ x, StatedQuadPlus 4 k ((A : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k) *ᵥ x) =
      StatedQuadPlus 4 k x) ∧
    (A : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k) *ᵥ omegaPlusVec k = omegaPlusVec k}
  mul_mem' {A B} hA hB := by
    refine ⟨fun x => ?_, ?_⟩
    · rw [Units.val_mul, ← mulVec_mulVec, hA.1, hB.1]
    · rw [Units.val_mul, ← mulVec_mulVec, hB.2, hA.2]
  one_mem' := ⟨fun x => by rw [Units.val_one, one_mulVec], by rw [Units.val_one, one_mulVec]⟩
  inv_mem' {A} hA := by
    have hinv : ∀ y, (A : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k) *ᵥ
        (((A⁻¹ : GL (Fin 4 ⊕ Fin 4) k) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k) *ᵥ y) = y :=
      fun y => by rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    refine ⟨fun x => ?_, ?_⟩
    · rw [← hA.1, hinv]
    · conv_lhs => rw [← hA.2]
      rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

variable {k}

variable [CharP k 2]

theorem plusStab_col {A : GL (Fin 4 ⊕ Fin 4) k} (hA : A ∈ plusStab k) (j : Fin 3 ⊕ Fin 3) :
    (A : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k) (Sum.inl 3) (plusEmb j) =
      (A : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k) (Sum.inr 3) (plusEmb j) := by
  have h := polarPlus_mulVec hA.1 (Pi.single (plusEmb j) 1) (omegaPlusVec k)
  rw [hA.2, polarPlus_omegaPlusVec, polarPlus_omegaPlusVec, mulVec_single_one,
    Pi.single_eq_of_ne (plusEmb_ne_inl_three j).symm,
    Pi.single_eq_of_ne (plusEmb_ne_inr_three j).symm, add_zero] at h
  have h' := eq_neg_of_add_eq_zero_left h
  rwa [CharTwo.neg_eq] at h'

omit [CharP k 2] in
theorem plusStab_row {A : GL (Fin 4 ⊕ Fin 4) k} (hA : A ∈ plusStab k) (i : Fin 3 ⊕ Fin 3) :
    (A : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k) (plusEmb i) (Sum.inl 3) +
      (A : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k) (plusEmb i) (Sum.inr 3) = 0 := by
  have h := congrFun hA.2 (plusEmb i)
  rw [mulVec, dotProduct_omegaPlusVec, omegaPlusVec_plusEmb] at h
  exact h

theorem plusStab_submatrix_mul {A B : GL (Fin 4 ⊕ Fin 4) k} (hA : A ∈ plusStab k)
    (hB : B ∈ plusStab k) :
    ((A * B : GL (Fin 4 ⊕ Fin 4) k) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k).submatrix
        plusEmb plusEmb =
      (A : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k).submatrix plusEmb plusEmb *
        (B : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k).submatrix plusEmb plusEmb := by
  ext i j
  have hcol := plusStab_col hB j
  have hrow := plusStab_row hA i
  simp only [submatrix_apply, Units.val_mul, mul_apply, Fintype.sum_sum_type,
    Fin.sum_univ_castSucc]
  have e1 : ∀ c : Fin 3, plusEmb (Sum.inl c) = Sum.inl (Fin.castSucc c) := fun _ => rfl
  have e2 : ∀ c : Fin 3, plusEmb (Sum.inr c) = Sum.inr (Fin.castSucc c) := fun _ => rfl
  simp only [e1, e2]
  have hl : (Fin.last 3 : Fin 4) = 3 := rfl
  rw [hl, hcol]
  linear_combination (B : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k) (Sum.inr 3) (plusEmb j) * hrow

omit [CharP k 2] in
theorem transpose_mul_spJ_mul_apply (N : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k)
    (a b : Fin 3 ⊕ Fin 3) :
    (Nᵀ * (fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k) * N) a b =
      ∑ i : Fin 3, (N (Sum.inl i) a * N (Sum.inr i) b - N (Sum.inr i) a * N (Sum.inl i) b) := by
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, transpose_apply, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
    add_zero, zero_add, one_apply, Matrix.neg_apply, mul_ite, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_neg, neg_mul,
    Finset.sum_neg_distrib, Finset.sum_const_zero]
  rw [Finset.sum_sub_distrib]
  ring

omit [CharP k 2] in
theorem spJ_apply (a b : Fin 3 ⊕ Fin 3) :
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k) a b =
      ∑ i : Fin 3, ((Pi.single a (1 : k) : Fin 3 ⊕ Fin 3 → k) (Sum.inl i) *
          (Pi.single b (1 : k) : Fin 3 ⊕ Fin 3 → k) (Sum.inr i) -
        (Pi.single a (1 : k) : Fin 3 ⊕ Fin 3 → k) (Sum.inr i) *
          (Pi.single b (1 : k) : Fin 3 ⊕ Fin 3 → k) (Sum.inl i)) := by
  rcases a with a | a <;> rcases b with b | b <;> simp [Pi.single_apply, one_apply, eq_comm]

theorem plusStab_submatrix_symplectic {A : GL (Fin 4 ⊕ Fin 4) k} (hA : A ∈ plusStab k) :
    ((A : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k).submatrix plusEmb plusEmb)ᵀ *
        (fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k) *
        (A : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k).submatrix plusEmb plusEmb =
      fromBlocks 0 1 (-1) 0 := by
  ext a b
  rw [transpose_mul_spJ_mul_apply, spJ_apply]
  have h := polarPlus_mulVec hA.1 (Pi.single (plusEmb a) 1) (Pi.single (plusEmb b) 1)
  rw [mulVec_single_one, mulVec_single_one, polarPlus_split, polarPlus_split] at h
  simp only [Matrix.col_apply, plusStab_col hA a, plusStab_col hA b,
    Pi.single_eq_of_ne (plusEmb_ne_inl_three a).symm,
    Pi.single_eq_of_ne (plusEmb_ne_inr_three a).symm,
    Pi.single_eq_of_ne (plusEmb_ne_inl_three b).symm,
    Pi.single_eq_of_ne (plusEmb_ne_inr_three b).symm,
    mul_zero, add_zero, CharTwo.add_self_eq_zero] at h
  have hs : ∀ (c d : Fin 3 ⊕ Fin 3),
      (Pi.single (plusEmb c) (1 : k) : Fin 4 ⊕ Fin 4 → k) (plusEmb d) =
        (Pi.single c (1 : k) : Fin 3 ⊕ Fin 3 → k) d := fun c d => by
    simp only [Pi.single_apply, plusEmb_injective.eq_iff]
  simp only [hs] at h
  simp only [submatrix_apply, CharTwo.sub_eq_add]
  exact h

variable (k)

@[expose] noncomputable def resPlusMat :
    plusStab k →* Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k where
  toFun A := ((A : GL (Fin 4 ⊕ Fin 4) k) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k).submatrix
    plusEmb plusEmb
  map_one' := by
    change ((1 : GL (Fin 4 ⊕ Fin 4) k) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k).submatrix
      plusEmb plusEmb = 1
    rw [Units.val_one]
    exact Matrix.submatrix_one _ plusEmb_injective
  map_mul' A B := plusStab_submatrix_mul A.2 B.2

@[expose] noncomputable def resPlus : plusStab k →* StatedSp 3 k :=
  (resPlusMat k).toHomUnits.codRestrict (StatedSp 3 k) fun A => by
    rw [LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
    exact plusStab_submatrix_symplectic A.2

end CFSG.SeitzReduction.F4Pilot
