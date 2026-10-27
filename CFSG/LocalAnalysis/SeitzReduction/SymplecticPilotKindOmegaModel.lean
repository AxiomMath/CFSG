module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup Matrix
open CFSG.Assembly.LowTwoRank

variable (k : Type) [Field k] (r : ℕ)

@[expose] def kOmegaVec : Fin (r + 1) ⊕ Fin (r + 1) → k :=
  Pi.single (Sum.inl (Fin.last r)) 1 + Pi.single (Sum.inr (Fin.last r)) 1

@[expose] def kOmegaEmb : Fin r ⊕ Fin r → Fin (r + 1) ⊕ Fin (r + 1) :=
  Sum.map Fin.castSucc Fin.castSucc

variable {r}

theorem kOmegaEmb_injective : Function.Injective (kOmegaEmb r) :=
  Sum.map_injective.2 ⟨Fin.castSucc_injective r, Fin.castSucc_injective r⟩

theorem kOmegaEmb_ne_inl_last (j : Fin r ⊕ Fin r) : kOmegaEmb r j ≠ Sum.inl (Fin.last r) := by
  rcases j with j | j
  · intro h
    exact Fin.castSucc_ne_last j (Sum.inl_injective h)
  · exact Sum.inr_ne_inl

theorem kOmegaEmb_ne_inr_last (j : Fin r ⊕ Fin r) : kOmegaEmb r j ≠ Sum.inr (Fin.last r) := by
  rcases j with j | j
  · exact Sum.inl_ne_inr
  · intro h
    exact Fin.castSucc_ne_last j (Sum.inr_injective h)

theorem kOmegaVec_inl (i : Fin (r + 1)) :
    kOmegaVec k r (Sum.inl i) = if i = Fin.last r then 1 else 0 := by
  by_cases hi : i = Fin.last r
  · subst hi
    simp [kOmegaVec]
  · simp [kOmegaVec, hi]

theorem kOmegaVec_inr (i : Fin (r + 1)) :
    kOmegaVec k r (Sum.inr i) = if i = Fin.last r then 1 else 0 := by
  by_cases hi : i = Fin.last r
  · subst hi
    simp [kOmegaVec]
  · simp [kOmegaVec, hi]

theorem kOmegaVec_kOmegaEmb (j : Fin r ⊕ Fin r) : kOmegaVec k r (kOmegaEmb r j) = 0 := by
  rcases j with j | j
  · rw [kOmegaEmb, Sum.map_inl, kOmegaVec_inl]
    exact ite_eq_right_iff.mpr fun h => absurd h (Fin.castSucc_ne_last j)
  · rw [kOmegaEmb, Sum.map_inr, kOmegaVec_inr]
    exact ite_eq_right_iff.mpr fun h => absurd h (Fin.castSucc_ne_last j)

theorem kOmega_statedQuadPlus_vec : StatedQuadPlus (r + 1) k (kOmegaVec k r) = 1 := by
  simp only [StatedQuadPlus, kOmegaVec_inl, kOmegaVec_inr, Fin.sum_univ_castSucc]
  simp [Fin.castSucc_ne_last]

variable (r)

@[expose] def kOmegaPolar (x y : Fin (r + 1) ⊕ Fin (r + 1) → k) : k :=
  ∑ i, (x (Sum.inl i) * y (Sum.inr i) + x (Sum.inr i) * y (Sum.inl i))

variable {r}

theorem kOmegaPolar_eq (x y : Fin (r + 1) ⊕ Fin (r + 1) → k) :
    kOmegaPolar k r x y =
      StatedQuadPlus (r + 1) k (x + y) - StatedQuadPlus (r + 1) k x -
        StatedQuadPlus (r + 1) k y := by
  simp only [kOmegaPolar, StatedQuadPlus, Pi.add_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

variable {k}

theorem kOmegaPolar_mulVec {A : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) k}
    (hA : ∀ x, StatedQuadPlus (r + 1) k (A *ᵥ x) = StatedQuadPlus (r + 1) k x)
    (x y : Fin (r + 1) ⊕ Fin (r + 1) → k) :
    kOmegaPolar k r (A *ᵥ x) (A *ᵥ y) = kOmegaPolar k r x y := by
  rw [kOmegaPolar_eq, kOmegaPolar_eq, ← mulVec_add, hA, hA, hA]

theorem kOmegaPolar_kOmegaVec (z : Fin (r + 1) ⊕ Fin (r + 1) → k) :
    kOmegaPolar k r z (kOmegaVec k r) = z (Sum.inl (Fin.last r)) + z (Sum.inr (Fin.last r)) := by
  simp only [kOmegaPolar, kOmegaVec_inl, kOmegaVec_inr, Fin.sum_univ_castSucc]
  simp [Fin.castSucc_ne_last]

theorem kOmega_dotProduct_vec (w : Fin (r + 1) ⊕ Fin (r + 1) → k) :
    w ⬝ᵥ kOmegaVec k r = w (Sum.inl (Fin.last r)) + w (Sum.inr (Fin.last r)) := by
  simp only [dotProduct, Fintype.sum_sum_type, kOmegaVec_inl, kOmegaVec_inr,
    Fin.sum_univ_castSucc]
  simp [Fin.castSucc_ne_last]

theorem kOmegaPolar_split (x y : Fin (r + 1) ⊕ Fin (r + 1) → k) :
    kOmegaPolar k r x y = (∑ i : Fin r, (x (kOmegaEmb r (Sum.inl i)) * y (kOmegaEmb r (Sum.inr i)) +
      x (kOmegaEmb r (Sum.inr i)) * y (kOmegaEmb r (Sum.inl i)))) +
        (x (Sum.inl (Fin.last r)) * y (Sum.inr (Fin.last r)) +
          x (Sum.inr (Fin.last r)) * y (Sum.inl (Fin.last r))) := by
  rw [kOmegaPolar, Fin.sum_univ_castSucc]
  rfl

variable (k r)

@[expose] def kOmegaStab : Subgroup (GL (Fin (r + 1) ⊕ Fin (r + 1)) k) where
  carrier := {A | (∀ x, StatedQuadPlus (r + 1) k
      ((A : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) k) *ᵥ x) =
        StatedQuadPlus (r + 1) k x) ∧
    (A : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) k) *ᵥ kOmegaVec k r =
      kOmegaVec k r}
  mul_mem' {A B} hA hB := by
    refine ⟨fun x => ?_, ?_⟩
    · rw [Units.val_mul, ← mulVec_mulVec, hA.1, hB.1]
    · rw [Units.val_mul, ← mulVec_mulVec, hB.2, hA.2]
  one_mem' := ⟨fun x => by rw [Units.val_one, one_mulVec], by rw [Units.val_one, one_mulVec]⟩
  inv_mem' {A} hA := by
    have hinv : ∀ y, (A : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) k) *ᵥ
        (((A⁻¹ : GL (Fin (r + 1) ⊕ Fin (r + 1)) k) :
          Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) k) *ᵥ y) = y :=
      fun y => by rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    refine ⟨fun x => ?_, ?_⟩
    · rw [← hA.1, hinv]
    · conv_lhs => rw [← hA.2]
      rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

variable {k r}

variable [CharP k 2]

theorem kOmegaStab_col {A : GL (Fin (r + 1) ⊕ Fin (r + 1)) k} (hA : A ∈ kOmegaStab k r)
    (j : Fin r ⊕ Fin r) :
    (A : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) k)
        (Sum.inl (Fin.last r)) (kOmegaEmb r j) =
      (A : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) k)
        (Sum.inr (Fin.last r)) (kOmegaEmb r j) := by
  have h := kOmegaPolar_mulVec hA.1 (Pi.single (kOmegaEmb r j) 1) (kOmegaVec k r)
  rw [hA.2, kOmegaPolar_kOmegaVec, kOmegaPolar_kOmegaVec, mulVec_single_one,
    Pi.single_eq_of_ne (kOmegaEmb_ne_inl_last j).symm,
    Pi.single_eq_of_ne (kOmegaEmb_ne_inr_last j).symm, add_zero] at h
  have h' := eq_neg_of_add_eq_zero_left h
  rwa [CharTwo.neg_eq] at h'

omit [CharP k 2] in
theorem kOmegaStab_row {A : GL (Fin (r + 1) ⊕ Fin (r + 1)) k} (hA : A ∈ kOmegaStab k r)
    (i : Fin r ⊕ Fin r) :
    (A : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) k) (kOmegaEmb r i)
        (Sum.inl (Fin.last r)) +
      (A : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) k) (kOmegaEmb r i)
        (Sum.inr (Fin.last r)) = 0 := by
  have h := congrFun hA.2 (kOmegaEmb r i)
  rw [mulVec, kOmega_dotProduct_vec, kOmegaVec_kOmegaEmb] at h
  exact h

theorem kOmegaStab_submatrix_mul {A B : GL (Fin (r + 1) ⊕ Fin (r + 1)) k}
    (hA : A ∈ kOmegaStab k r) (hB : B ∈ kOmegaStab k r) :
    ((A * B : GL (Fin (r + 1) ⊕ Fin (r + 1)) k) :
        Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) k).submatrix
        (kOmegaEmb r) (kOmegaEmb r) =
      (A : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) k).submatrix
          (kOmegaEmb r) (kOmegaEmb r) *
        (B : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) k).submatrix
          (kOmegaEmb r) (kOmegaEmb r) := by
  ext i j
  have hcol := kOmegaStab_col hB j
  have hrow := kOmegaStab_row hA i
  simp only [submatrix_apply, Units.val_mul, mul_apply, Fintype.sum_sum_type,
    Fin.sum_univ_castSucc]
  have e1 : ∀ c : Fin r, kOmegaEmb r (Sum.inl c) = Sum.inl (Fin.castSucc c) := fun _ => rfl
  have e2 : ∀ c : Fin r, kOmegaEmb r (Sum.inr c) = Sum.inr (Fin.castSucc c) := fun _ => rfl
  simp only [e1, e2]
  rw [hcol]
  linear_combination
    (B : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) k)
      (Sum.inr (Fin.last r)) (kOmegaEmb r j) * hrow

omit [CharP k 2] in
theorem kOmega_transpose_mul_spJ_mul_apply (N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)
    (a b : Fin r ⊕ Fin r) :
    (Nᵀ * (fromBlocks 0 1 (-1) 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) * N) a b =
      ∑ i : Fin r, (N (Sum.inl i) a * N (Sum.inr i) b - N (Sum.inr i) a * N (Sum.inl i) b) := by
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, transpose_apply, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
    add_zero, zero_add, one_apply, Matrix.neg_apply, mul_ite, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_neg, neg_mul,
    Finset.sum_neg_distrib, Finset.sum_const_zero]
  rw [Finset.sum_sub_distrib]
  ring

omit [CharP k 2] in
theorem kOmega_spJ_apply (a b : Fin r ⊕ Fin r) :
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) a b =
      ∑ i : Fin r, ((Pi.single a (1 : k) : Fin r ⊕ Fin r → k) (Sum.inl i) *
          (Pi.single b (1 : k) : Fin r ⊕ Fin r → k) (Sum.inr i) -
        (Pi.single a (1 : k) : Fin r ⊕ Fin r → k) (Sum.inr i) *
          (Pi.single b (1 : k) : Fin r ⊕ Fin r → k) (Sum.inl i)) := by
  rcases a with a | a <;> rcases b with b | b <;> simp [Pi.single_apply, one_apply, eq_comm]

theorem kOmegaStab_submatrix_symplectic {A : GL (Fin (r + 1) ⊕ Fin (r + 1)) k}
    (hA : A ∈ kOmegaStab k r) :
    ((A : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) k).submatrix
        (kOmegaEmb r) (kOmegaEmb r))ᵀ *
        (fromBlocks 0 1 (-1) 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) *
        (A : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) k).submatrix
          (kOmegaEmb r) (kOmegaEmb r) =
      fromBlocks 0 1 (-1) 0 := by
  ext a b
  rw [kOmega_transpose_mul_spJ_mul_apply, kOmega_spJ_apply]
  have h := kOmegaPolar_mulVec hA.1 (Pi.single (kOmegaEmb r a) 1) (Pi.single (kOmegaEmb r b) 1)
  rw [mulVec_single_one, mulVec_single_one, kOmegaPolar_split, kOmegaPolar_split] at h
  simp only [Matrix.col_apply, kOmegaStab_col hA a, kOmegaStab_col hA b,
    Pi.single_eq_of_ne (kOmegaEmb_ne_inl_last a).symm,
    Pi.single_eq_of_ne (kOmegaEmb_ne_inr_last a).symm,
    Pi.single_eq_of_ne (kOmegaEmb_ne_inl_last b).symm,
    Pi.single_eq_of_ne (kOmegaEmb_ne_inr_last b).symm,
    mul_zero, add_zero, CharTwo.add_self_eq_zero] at h
  have hs : ∀ (c d : Fin r ⊕ Fin r),
      (Pi.single (kOmegaEmb r c) (1 : k) : Fin (r + 1) ⊕ Fin (r + 1) → k) (kOmegaEmb r d) =
        (Pi.single c (1 : k) : Fin r ⊕ Fin r → k) d := fun c d => by
    simp only [Pi.single_apply, kOmegaEmb_injective.eq_iff]
  simp only [hs] at h
  simp only [submatrix_apply, CharTwo.sub_eq_add]
  exact h

variable (k r)

@[expose] noncomputable def kOmegaResMat :
    kOmegaStab k r →* Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k where
  toFun A := ((A : GL (Fin (r + 1) ⊕ Fin (r + 1)) k) :
    Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) k).submatrix
      (kOmegaEmb r) (kOmegaEmb r)
  map_one' := by
    change ((1 : GL (Fin (r + 1) ⊕ Fin (r + 1)) k) :
      Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) k).submatrix
        (kOmegaEmb r) (kOmegaEmb r) = 1
    rw [Units.val_one]
    exact Matrix.submatrix_one _ kOmegaEmb_injective
  map_mul' A B := kOmegaStab_submatrix_mul A.2 B.2

@[expose] noncomputable def kOmegaRes : kOmegaStab k r →* StatedSp r k :=
  (kOmegaResMat k r).toHomUnits.codRestrict (StatedSp r k) fun A => by
    rw [LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
    exact kOmegaStab_submatrix_symplectic A.2

end CFSG.SeitzReduction.SymplecticPilot
