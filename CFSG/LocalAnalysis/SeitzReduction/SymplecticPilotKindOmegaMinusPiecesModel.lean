module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaModel
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesEmbed
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCores

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup Matrix
open CFSG.Assembly.LowTwoRank

variable (k : Type) [Field k] (r : ℕ)

@[expose] def kOmMVec : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2 → k :=
  Pi.single (Sum.inr (Sum.inr 0)) 1

@[expose] def kOmMEmb : Fin r ⊕ Fin r → Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2 :=
  Sum.elim (fun i => Sum.inl i) fun i => Sum.inr (Sum.inl i)

variable {r}

@[simp] theorem kOmMEmb_inl (i : Fin r) :
    kOmMEmb r (Sum.inl i) = (Sum.inl i : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) := rfl

@[simp] theorem kOmMEmb_inr (i : Fin r) :
    kOmMEmb r (Sum.inr i) = (Sum.inr (Sum.inl i) : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) :=
  rfl

theorem kOmMEmb_injective : Function.Injective (kOmMEmb r) := by
  rintro (i | i) (j | j) h
  · exact congrArg Sum.inl (Sum.inl_injective h)
  · exact absurd h Sum.inl_ne_inr
  · exact absurd h Sum.inr_ne_inl
  · exact congrArg Sum.inr (Sum.inl_injective (Sum.inr_injective h))

theorem kOmMEmb_ne_tail (j : Fin r ⊕ Fin r) (t : Fin 2) : kOmMEmb r j ≠ Sum.inr (Sum.inr t) := by
  rcases j with j | j
  · exact Sum.inl_ne_inr
  · intro h
    exact Sum.inl_ne_inr (Sum.inr_injective h)

theorem kOmMVec_kOmMEmb (j : Fin r ⊕ Fin r) : kOmMVec k r (kOmMEmb r j) = 0 :=
  Pi.single_eq_of_ne (kOmMEmb_ne_tail j 0) _

theorem kOmM_statedQuadMinus_vec (b c : k) : StatedQuadMinus (r + 1) k b c (kOmMVec k r) = 1 := by
  simp [StatedQuadMinus, kOmMVec]

variable (r)

@[expose] def kOmMPolar (b : k) (x y : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2 → k) : k :=
  (∑ i : Fin r, (x (Sum.inl i) * y (Sum.inr (Sum.inl i)) +
      x (Sum.inr (Sum.inl i)) * y (Sum.inl i))) +
    b * (x (Sum.inr (Sum.inr 0)) * y (Sum.inr (Sum.inr 1)) +
      x (Sum.inr (Sum.inr 1)) * y (Sum.inr (Sum.inr 0)))

variable {r}

theorem kOmMPolar_eq [CharP k 2] (b c : k) (x y : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2 → k) :
    kOmMPolar k r b x y = StatedQuadMinus (r + 1) k b c (x + y) - StatedQuadMinus (r + 1) k b c x -
      StatedQuadMinus (r + 1) k b c y := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  simp only [kOmMPolar, StatedQuadMinus, Pi.add_apply]
  have hs : ∑ i : Fin r, (x (Sum.inl i) * y (Sum.inr (Sum.inl i)) +
      x (Sum.inr (Sum.inl i)) * y (Sum.inl i)) =
      ∑ i : Fin (r + 1 - 1), ((x (Sum.inl i) + y (Sum.inl i)) * (x (Sum.inr (Sum.inl i)) +
        y (Sum.inr (Sum.inl i))) - x (Sum.inl i) * x (Sum.inr (Sum.inl i)) -
          y (Sum.inl i) * y (Sum.inr (Sum.inl i))) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [hs]
  simp only [Finset.sum_sub_distrib]
  linear_combination (-(x (Sum.inr (Sum.inr 0)) * y (Sum.inr (Sum.inr 0)) +
    c * x (Sum.inr (Sum.inr 1)) * y (Sum.inr (Sum.inr 1)))) * h2

variable {k}

theorem kOmMPolar_mulVec [CharP k 2] {b c : k}
    {A : Matrix (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2)
      (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k}
    (hA : ∀ x, StatedQuadMinus (r + 1) k b c (A *ᵥ x) = StatedQuadMinus (r + 1) k b c x)
    (x y : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2 → k) :
    kOmMPolar k r b (A *ᵥ x) (A *ᵥ y) = kOmMPolar k r b x y := by
  rw [kOmMPolar_eq k b c, kOmMPolar_eq k b c, ← mulVec_add, hA, hA, hA]

theorem kOmMPolar_vec (b : k) (z : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2 → k) :
    kOmMPolar k r b z (kOmMVec k r) = b * z (Sum.inr (Sum.inr 1)) := by
  simp [kOmMPolar, kOmMVec]

theorem kOmM_dotProduct_vec (w : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2 → k) :
    w ⬝ᵥ kOmMVec k r = w (Sum.inr (Sum.inr 0)) := by
  rw [kOmMVec, dotProduct_single, mul_one]

variable (k r)

@[expose] def kOmMStab (b c : k) :
    Subgroup (GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k) where
  carrier := {A | (∀ x, StatedQuadMinus (r + 1) k b c
      ((A : Matrix (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2)
        (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k) *ᵥ x) =
          StatedQuadMinus (r + 1) k b c x) ∧
    (A : Matrix (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2)
      (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k) *ᵥ kOmMVec k r = kOmMVec k r}
  mul_mem' {A B} hA hB := by
    refine ⟨fun x => ?_, ?_⟩
    · rw [Units.val_mul, ← mulVec_mulVec, hA.1, hB.1]
    · rw [Units.val_mul, ← mulVec_mulVec, hB.2, hA.2]
  one_mem' := ⟨fun x => by rw [Units.val_one, one_mulVec], by rw [Units.val_one, one_mulVec]⟩
  inv_mem' {A} hA := by
    have hinv : ∀ y, (A : Matrix (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2)
        (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k) *ᵥ
        (((A⁻¹ : GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k) :
          Matrix (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2)
            (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k) *ᵥ y) = y :=
      fun y => by rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    refine ⟨fun x => ?_, ?_⟩
    · rw [← hA.1, hinv]
    · conv_lhs => rw [← hA.2]
      rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

variable {k r}

theorem kOmMStab_col [CharP k 2] {b c : k} (hb : b ≠ 0)
    {A : GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k} (hA : A ∈ kOmMStab k r b c)
    (j : Fin r ⊕ Fin r) :
    (A : Matrix (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2)
      (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k) (Sum.inr (Sum.inr 1)) (kOmMEmb r j) = 0 := by
  have h := kOmMPolar_mulVec hA.1 (Pi.single (kOmMEmb r j) 1) (kOmMVec k r)
  rw [hA.2, kOmMPolar_vec, kOmMPolar_vec, mulVec_single_one,
    Pi.single_eq_of_ne (kOmMEmb_ne_tail j 1).symm, mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left hb

theorem kOmMStab_row {b c : k} {A : GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k}
    (hA : A ∈ kOmMStab k r b c) (i : Fin r ⊕ Fin r) :
    (A : Matrix (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2)
      (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k) (kOmMEmb r i) (Sum.inr (Sum.inr 0)) = 0 := by
  have h := congrFun hA.2 (kOmMEmb r i)
  rw [mulVec, kOmM_dotProduct_vec, kOmMVec_kOmMEmb] at h
  exact h

theorem kOmMStab_submatrix_mul [CharP k 2] {b c : k} (hb : b ≠ 0)
    {A B : GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k} (hA : A ∈ kOmMStab k r b c)
    (hB : B ∈ kOmMStab k r b c) :
    ((A * B : GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k) :
        Matrix (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2)
          (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k).submatrix (kOmMEmb r) (kOmMEmb r) =
      (A : Matrix (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2)
          (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k).submatrix (kOmMEmb r) (kOmMEmb r) *
        (B : Matrix (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2)
          (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k).submatrix (kOmMEmb r) (kOmMEmb r) := by
  ext i j
  have hcol := kOmMStab_col hb hB j
  have hrow := kOmMStab_row hA i
  simp only [submatrix_apply, Units.val_mul, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  rw [hrow, hcol, zero_mul, mul_zero, add_zero, add_zero]
  rfl

theorem kOmM_transpose_mul_spJ_mul_apply (N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)
    (a a' : Fin r ⊕ Fin r) :
    (Nᵀ * (fromBlocks 0 1 (-1) 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) * N) a a' =
      ∑ i : Fin r, (N (Sum.inl i) a * N (Sum.inr i) a' - N (Sum.inr i) a * N (Sum.inl i) a') :=
  kOmega_transpose_mul_spJ_mul_apply N a a'

theorem kOmMStab_submatrix_symplectic [CharP k 2] {b c : k} (hb : b ≠ 0)
    {A : GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k} (hA : A ∈ kOmMStab k r b c) :
    ((A : Matrix (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2)
        (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k).submatrix (kOmMEmb r) (kOmMEmb r))ᵀ *
        (fromBlocks 0 1 (-1) 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) *
        (A : Matrix (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2)
          (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k).submatrix (kOmMEmb r) (kOmMEmb r) =
      fromBlocks 0 1 (-1) 0 := by
  ext a a'
  rw [kOmM_transpose_mul_spJ_mul_apply, kOmega_spJ_apply]
  have h := kOmMPolar_mulVec hA.1 (Pi.single (kOmMEmb r a) 1) (Pi.single (kOmMEmb r a') 1)
  rw [mulVec_single_one, mulVec_single_one] at h
  unfold kOmMPolar at h
  simp only [Matrix.col_apply, kOmMStab_col hb hA a, kOmMStab_col hb hA a',
    Pi.single_eq_of_ne (kOmMEmb_ne_tail a 0).symm, Pi.single_eq_of_ne (kOmMEmb_ne_tail a 1).symm,
    Pi.single_eq_of_ne (kOmMEmb_ne_tail a' 0).symm, Pi.single_eq_of_ne (kOmMEmb_ne_tail a' 1).symm,
    mul_zero, zero_mul, add_zero] at h
  have hs : ∀ (x y : Fin r ⊕ Fin r),
      (Pi.single (kOmMEmb r x) (1 : k) : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2 → k)
        (kOmMEmb r y) = (Pi.single x (1 : k) : Fin r ⊕ Fin r → k) y := fun x y => by
    simp only [Pi.single_apply, kOmMEmb_injective.eq_iff]
  have hs1 : ∀ (x : Fin r ⊕ Fin r) (i : Fin r),
      (Pi.single (kOmMEmb r x) (1 : k) : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2 → k)
        (Sum.inl i) = (Pi.single x (1 : k) : Fin r ⊕ Fin r → k) (Sum.inl i) :=
    fun x i => hs x (Sum.inl i)
  have hs2 : ∀ (x : Fin r ⊕ Fin r) (i : Fin r),
      (Pi.single (kOmMEmb r x) (1 : k) : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2 → k)
        (Sum.inr (Sum.inl i)) = (Pi.single x (1 : k) : Fin r ⊕ Fin r → k) (Sum.inr i) :=
    fun x i => hs x (Sum.inr i)
  simp only [hs1, hs2] at h
  simp only [submatrix_apply, kOmMEmb_inl, kOmMEmb_inr, CharTwo.sub_eq_add]
  exact h

variable (k r)

@[expose] noncomputable def kOmMResMat [CharP k 2] {b c : k} (hb : b ≠ 0) :
    kOmMStab k r b c →* Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k where
  toFun A := ((A : GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k) :
    Matrix (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2)
      (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k).submatrix (kOmMEmb r) (kOmMEmb r)
  map_one' := by
    change ((1 : GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k) :
      Matrix (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2)
        (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k).submatrix (kOmMEmb r) (kOmMEmb r) = 1
    rw [Units.val_one]
    exact Matrix.submatrix_one _ kOmMEmb_injective
  map_mul' A B := kOmMStab_submatrix_mul hb A.2 B.2

@[expose] noncomputable def kOmMRes [CharP k 2] {b c : k} (hb : b ≠ 0) :
    kOmMStab k r b c →* StatedSp r k :=
  (kOmMResMat k r hb).toHomUnits.codRestrict (StatedSp r k) fun A => by
    rw [LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
    exact kOmMStab_submatrix_symplectic hb A.2

theorem coe_kOmMRes [CharP k 2] {b c : k} (hb : b ≠ 0) (A : kOmMStab k r b c) :
    (((kOmMRes k r hb A : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
      ((A : GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k) :
        Matrix (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2)
          (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k).submatrix (kOmMEmb r) (kOmMEmb r) := rfl

@[expose] def kOmMDiagUnits : (Fin r → kˣ) →* (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2 → kˣ) where
  toFun t := Sum.elim t (Sum.elim (fun i => (t i)⁻¹) fun _ => 1)
  map_one' := by
    funext a
    rcases a with i | i | j <;> simp
  map_mul' t s := by
    funext a
    rcases a with i | i | j
    · rfl
    · simp only [Sum.elim_inr, Sum.elim_inl, Pi.mul_apply, _root_.mul_inv_rev]
      exact mul_comm _ _
    · simp

@[expose] noncomputable def kOmMDiag :
    (Fin r → kˣ) →* GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k :=
  TauCeti.diagGL.comp (kOmMDiagUnits k r)

@[expose] def kOmMWeight (t : Fin r → kˣ) : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2 → k :=
  Sum.elim (fun i => ((t i : kˣ) : k)) (Sum.elim (fun i => (((t i)⁻¹ : kˣ) : k)) fun _ => 1)

variable {k r}

@[simp] theorem kOmMWeight_inl (t : Fin r → kˣ) (i : Fin r) :
    kOmMWeight k r t (Sum.inl i) = ((t i : kˣ) : k) := rfl

@[simp] theorem kOmMWeight_inr_inl (t : Fin r → kˣ) (i : Fin r) :
    kOmMWeight k r t (Sum.inr (Sum.inl i)) = (((t i)⁻¹ : kˣ) : k) := rfl

@[simp] theorem kOmMWeight_inr_inr (t : Fin r → kˣ) (j : Fin 2) :
    kOmMWeight k r t (Sum.inr (Sum.inr j)) = 1 := rfl

theorem kOmMDiag_coe (t : Fin r → kˣ) :
    (kOmMDiag k r t : Matrix (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2)
      (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k) = diagonal (kOmMWeight k r t) := by
  rw [kOmMDiag, MonoidHom.comp_apply, TauCeti.diagGL_coe]
  congr 1
  funext a
  rcases a with i | i | j <;> rfl

theorem kOmMDiag_apply_ne (t : Fin r → kˣ) {a a' : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2}
    (h : a ≠ a') : (kOmMDiag k r t : Matrix (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2)
      (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k) a a' = 0 := by
  rw [kOmMDiag_coe, diagonal_apply_ne _ h]

theorem kOmMDiag_apply_self (t : Fin r → kˣ) (a : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) :
    (kOmMDiag k r t : Matrix (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2)
      (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k) a a = kOmMWeight k r t a := by
  rw [kOmMDiag_coe, diagonal_apply_eq]

theorem kOmM_isHypFrame (b c : k) :
    OmegaPilot.IsHypFrame (CFSG.LieType.Universal.Spin.quadMinus (r + 1) k b c)
      (fun i : Fin r => (Sum.inl i : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2))
      (fun i : Fin r => Sum.inr (Sum.inl i)) where
  hyp i := OmegaPilot.isHypCoord_quadMinus (n := r + 1) b c i
  left_injective := fun _ _ h => Sum.inl_injective h
  right_injective := fun _ _ h => Sum.inl_injective (Sum.inr_injective h)
  left_ne_right _ _ := Sum.inl_ne_inr

theorem kOmM_toLinEquiv_diag (b c : k) (t : Fin r → kˣ) :
    CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k
        (kOmMDiag k r t) =
      OmegaPilot.frameLin (fun i : Fin r => (Sum.inl i : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2))
        (fun i : Fin r => Sum.inr (Sum.inl i)) t := by
  ext v a
  rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, OmegaPilot.frameLin_apply,
    kOmMDiag_coe, mulVec_diagonal]
  congr 1
  rcases a with i | i | j
  · rw [kOmMWeight_inl, (kOmM_isHypFrame b c).frameEntry_left]
  · rw [kOmMWeight_inr_inl, (kOmM_isHypFrame b c).frameEntry_right]
  · rw [kOmMWeight_inr_inr, OmegaPilot.frameEntry_of_forall_ne t (fun _ => Sum.inr_ne_inl)
      (fun _ h => Sum.inr_ne_inl (Sum.inr_injective h)), Units.val_one]

theorem kOmMDiag_mem [Finite k] [CharP k 2] (b c : k) (t : Fin r → kˣ) :
    kOmMDiag k r t ∈ StatedOmega (StatedQuadMinus (r + 1) k b c) := by
  rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap
      (CFSG.LieType.Universal.Spin.coe_quadMinus (r + 1) k b c), Subgroup.mem_comap,
    MulEquiv.coe_toMonoidHom, kOmM_toLinEquiv_diag b c]
  exact (kOmM_isHypFrame b c).frameLin_mem_orthDerived t

theorem kOmMDiag_mulVec_vec (t : Fin r → kˣ) :
    (kOmMDiag k r t : Matrix (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2)
      (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k) *ᵥ kOmMVec k r = kOmMVec k r := by
  rw [kOmMDiag_coe]
  funext i
  rw [mulVec_diagonal]
  rcases i with i | i | j
  · simp [kOmMVec]
  · simp [kOmMVec]
  · rw [kOmMWeight_inr_inr, one_mul]

theorem kOmM_isometry_of_mem {b c : k}
    {A : GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k}
    (hA : A ∈ StatedOmega (StatedQuadMinus (r + 1) k b c))
    (x : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2 → k) :
    StatedQuadMinus (r + 1) k b c ((A : Matrix (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2)
      (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k) *ᵥ x) = StatedQuadMinus (r + 1) k b c x :=
  F4Pilot.isometry_of_mem_statedOmega hA x
