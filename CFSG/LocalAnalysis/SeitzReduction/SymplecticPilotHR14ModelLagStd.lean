module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCentralizerB1
public import CFSG.LieType.BorelTits.Symplectic

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.LieType.BorelTits (spJ transpose_mul_mul_of_mem_statedSp)
open scoped MatrixGroups

variable {m : ℕ} {F : Type} [Field F]

section Alt

variable (m F) in
@[expose] def lagAlt : Submodule F (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) where
  carrier := {C | Cᵀ = C ∧ ∀ a, C a a = 0}
  add_mem' {C D} hC hD := ⟨by rw [transpose_add, hC.1, hD.1], fun a => by
    rw [Matrix.add_apply, hC.2, hD.2, add_zero]⟩
  zero_mem' := ⟨transpose_zero, fun _ => rfl⟩
  smul_mem' c C hC := ⟨by rw [transpose_smul, hC.1], fun a => by
    rw [Matrix.smul_apply, hC.2, smul_zero]⟩

variable (m F) in
@[expose] def lagOmegaStar : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F →ₗ[F] F where
  toFun C := ∑ i, C (Sum.inl i) (Sum.inr i)
  map_add' C D := by simp [Finset.sum_add_distrib]
  map_smul' c C := by simp [Finset.mul_sum]

theorem lagOmegaStar_apply (C : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) :
    lagOmegaStar m F C = ∑ i, C (Sum.inl i) (Sum.inr i) := rfl

variable (m F) in
@[expose] def lagR0 : Submodule F (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) :=
  lagAlt m F ⊓ LinearMap.ker (lagOmegaStar m F)

@[expose] def lagNum : Fin m ⊕ Fin m → ℕ := Sum.elim (fun i => i.val) (fun i => m + i.val)

theorem lagNum_injective : Function.Injective (lagNum (m := m)) := by
  intro a b h
  rcases a with i | i <;> rcases b with j | j <;> simp only [lagNum, Sum.elim_inl,
    Sum.elim_inr] at h
  · exact congrArg Sum.inl (Fin.ext h)
  · omega
  · omega
  · exact congrArg Sum.inr (Fin.ext (by omega))

@[expose] def lagUpper (C : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F :=
  Matrix.of fun a b => if lagNum a < lagNum b then C a b else 0

theorem lagUpper_apply (C : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) (a b : Fin m ⊕ Fin m) :
    lagUpper C a b = if lagNum a < lagNum b then C a b else 0 := rfl

theorem eq_lagUpper_add_transpose {C : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F}
    (hC : C ∈ lagAlt m F) : C = lagUpper C + (lagUpper C)ᵀ := by
  ext a b
  rw [Matrix.add_apply, transpose_apply, lagUpper_apply, lagUpper_apply]
  rcases lt_trichotomy (lagNum a) (lagNum b) with h | h | h
  · rw [ite_eq_left h, ite_eq_right (by omega), add_zero]
  · rw [lagNum_injective h, ite_eq_right (lt_irrefl _), add_zero, hC.2]
  · rw [ite_eq_right (by omega), ite_eq_left h, zero_add, ← transpose_apply C a b, hC.1]

theorem lagOmegaStar_add_transpose [CharP F 2] (M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) :
    lagOmegaStar m F (M + Mᵀ) = trace (spJ m F * M) := by
  rw [lagOmegaStar_apply, trace, Fintype.sum_sum_type]
  simp only [Matrix.add_apply, transpose_apply, diag_apply, spJ, mul_apply, Fintype.sum_sum_type,
    fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂]
  simp [Matrix.one_apply, CharTwo.neg_eq, Finset.sum_add_distrib, add_comm]

theorem lagOmegaStar_conj [CharP F 2] {C : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F}
    (hC : C ∈ lagAlt m F) (A : StatedSp m F) :
    lagOmegaStar m F (mat m F A * C * (mat m F A)ᵀ) = lagOmegaStar m F C := by
  have hA := transpose_mul_mul_of_mem_statedSp A.2
  rw [← mat_apply] at hA
  set U := lagUpper C
  have hdec : mat m F A * C * (mat m F A)ᵀ =
      mat m F A * U * (mat m F A)ᵀ + (mat m F A * U * (mat m F A)ᵀ)ᵀ := by
    conv_lhs => rw [eq_lagUpper_add_transpose hC]
    rw [Matrix.mul_add, Matrix.add_mul, transpose_mul, transpose_mul, transpose_transpose,
      Matrix.mul_assoc, Matrix.mul_assoc]
  rw [hdec, lagOmegaStar_add_transpose, eq_lagUpper_add_transpose hC, lagOmegaStar_add_transpose,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, hA]

theorem conj_mem_lagAlt [CharP F 2] {C : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F}
    (hC : C ∈ lagAlt m F) (M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) :
    M * C * Mᵀ ∈ lagAlt m F := by
  refine ⟨by rw [transpose_mul, transpose_mul, transpose_transpose, hC.1, Matrix.mul_assoc], ?_⟩
  intro a
  conv_lhs => rw [eq_lagUpper_add_transpose hC]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, ← transpose_apply (M * lagUpper C * Mᵀ) a a,
    transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc]
  exact CharTwo.add_self_eq_zero _

theorem conj_mem_lagR0 [CharP F 2] {C : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F}
    (hC : C ∈ lagR0 m F) (A : StatedSp m F) :
    mat m F A * C * (mat m F A)ᵀ ∈ lagR0 m F :=
  ⟨conj_mem_lagAlt hC.1 _, by
    show lagOmegaStar m F _ = 0
    rw [lagOmegaStar_conj hC.1]
    exact hC.2⟩

end Alt

section Groups

theorem lag_neg_eq [CharP F 2] {ι κ : Type*} (M : Matrix ι κ F) : -M = M := by
  ext a b
  rw [Matrix.neg_apply, CharTwo.neg_eq]

theorem spJ_mul_spJ_of_charTwo [CharP F 2] : spJ m F * spJ m F = 1 := by
  rw [CFSG.LieType.BorelTits.spJ_mul_spJ, lag_neg_eq]

variable (m F) in
@[expose] def lagRadMat : Multiplicative (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) →*
    Matrix ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) F where
  toFun C := fromBlocks 1 (Multiplicative.toAdd C) 0 1
  map_one' := by simp [fromBlocks_one]
  map_mul' C D := by
    rw [fromBlocks_multiply]
    simp [toAdd_mul, add_comm]

variable (m F) in
@[expose] noncomputable def lagRad : Multiplicative (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) →*
    GL ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) F :=
  (lagRadMat m F).toHomUnits

theorem coe_lagRad (C : Multiplicative (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F)) :
    ((lagRad m F C : GL ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) F) :
      Matrix ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) F) =
      fromBlocks 1 (Multiplicative.toAdd C) 0 1 := rfl

theorem lagRad_injective : Function.Injective (lagRad m F) := by
  intro C D h
  have h1 := congrArg (fun g : GL ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) F =>
    (g : Matrix ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) F)) h
  simp only [coe_lagRad] at h1
  exact (fromBlocks_inj.1 h1).2.1

variable (m F) in
@[expose] noncomputable def lagLeviMat [CharP F 2] : StatedSp m F →*
    Matrix ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) F where
  toFun A := fromBlocks (mat m F A) 0 0 (spJ m F * mat m F A * spJ m F)
  map_one' := by
    rw [map_one, Matrix.mul_one, spJ_mul_spJ_of_charTwo, fromBlocks_one]
  map_mul' A B := by
    rw [fromBlocks_multiply, map_mul]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    congr 1
    calc spJ m F * (mat m F A * mat m F B) * spJ m F =
        spJ m F * mat m F A * (spJ m F * spJ m F) * mat m F B * spJ m F := by
          rw [spJ_mul_spJ_of_charTwo, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = spJ m F * mat m F A * spJ m F * (spJ m F * mat m F B * spJ m F) := by
          simp only [Matrix.mul_assoc]

variable (m F) in
@[expose] noncomputable def lagLevi [CharP F 2] : StatedSp m F →*
    GL ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) F :=
  (lagLeviMat m F).toHomUnits

theorem coe_lagLevi [CharP F 2] (A : StatedSp m F) :
    ((lagLevi m F A : GL ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) F) :
      Matrix ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) F) =
      fromBlocks (mat m F A) 0 0 (spJ m F * mat m F A * spJ m F) := rfl

theorem lagLevi_injective [CharP F 2] : Function.Injective (lagLevi m F) := by
  intro A B h
  have h1 := congrArg (fun g : GL ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) F =>
    (g : Matrix ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) F)) h
  simp only [coe_lagLevi] at h1
  exact mat_injective (fromBlocks_inj.1 h1).1

theorem lagLevi_mul_lagRad [CharP F 2] (A : StatedSp m F)
    (C : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) :
    lagLevi m F A * lagRad m F (Multiplicative.ofAdd C) =
      lagRad m F (Multiplicative.ofAdd (mat m F A * C * (mat m F A)ᵀ)) * lagLevi m F A := by
  have hA := transpose_mul_mul_of_mem_statedSp A.2
  rw [← mat_apply] at hA
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_lagLevi, coe_lagRad, coe_lagRad, toAdd_ofAdd, toAdd_ofAdd,
    fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 1
  calc mat m F A * C = mat m F A * C * ((mat m F A)ᵀ * spJ m F * mat m F A * spJ m F) := by
        rw [hA, spJ_mul_spJ_of_charTwo, Matrix.mul_one]
    _ = mat m F A * C * (mat m F A)ᵀ * (spJ m F * mat m F A * spJ m F) := by
        simp only [Matrix.mul_assoc]

open scoped commutatorElement in
theorem commutatorElement_lagRad_lagLevi [CharP F 2] (A : StatedSp m F)
    (C : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) :
    ⁅lagRad m F (Multiplicative.ofAdd C), lagLevi m F A⁆ =
      lagRad m F (Multiplicative.ofAdd (C - mat m F A * C * (mat m F A)ᵀ)) := by
  have h1 : lagLevi m F A * (lagRad m F (Multiplicative.ofAdd C))⁻¹ =
      lagRad m F (Multiplicative.ofAdd (mat m F A * (-C) * (mat m F A)ᵀ)) * lagLevi m F A := by
    rw [← map_inv, ← ofAdd_neg, lagLevi_mul_lagRad]
  rw [commutatorElement_def]
  calc lagRad m F (Multiplicative.ofAdd C) * lagLevi m F A *
        (lagRad m F (Multiplicative.ofAdd C))⁻¹ * (lagLevi m F A)⁻¹ =
      lagRad m F (Multiplicative.ofAdd C) *
        (lagLevi m F A * (lagRad m F (Multiplicative.ofAdd C))⁻¹) * (lagLevi m F A)⁻¹ := by
        group
    _ = lagRad m F (Multiplicative.ofAdd C) *
        lagRad m F (Multiplicative.ofAdd (mat m F A * (-C) * (mat m F A)ᵀ)) := by
        rw [h1]
        group
    _ = _ := by
        rw [← map_mul, ← ofAdd_add, Matrix.mul_neg, Matrix.neg_mul, ← sub_eq_add_neg]

variable (m F) in
@[expose] noncomputable def lagR0Grp : Subgroup (GL ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) F) where
  carrier := {g | ∃ C ∈ lagR0 m F, lagRad m F (Multiplicative.ofAdd C) = g}
  mul_mem' := by
    rintro _ _ ⟨C, hC, rfl⟩ ⟨D, hD, rfl⟩
    exact ⟨C + D, add_mem hC hD, by rw [ofAdd_add, map_mul]⟩
  one_mem' := ⟨0, zero_mem _, by rw [ofAdd_zero, map_one]⟩
  inv_mem' := by
    rintro _ ⟨C, hC, rfl⟩
    exact ⟨-C, neg_mem hC, by rw [ofAdd_neg, map_inv]⟩

variable (m F) in
@[expose] noncomputable def lagX [CharP F 2] :
    Subgroup (GL ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) F) :=
  (lagLevi m F).range

theorem isPGroup_lagR0Grp [CharP F 2] : IsPGroup 2 (lagR0Grp m F) := by
  rintro ⟨g, C, hC, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one, ← map_pow, ← ofAdd_nsmul, two_nsmul,
    ← two_smul F C, CharTwo.two_eq_zero, zero_smul, ofAdd_zero, map_one]

theorem conj_mem_lagR0Grp [CharP F 2] (A : StatedSp m F)
    {g : GL ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) F} (hg : g ∈ lagR0Grp m F) :
    lagLevi m F A * g * (lagLevi m F A)⁻¹ ∈ lagR0Grp m F := by
  obtain ⟨C, hC, rfl⟩ := hg
  refine ⟨_, conj_mem_lagR0 hC A, ?_⟩
  rw [lagLevi_mul_lagRad, mul_inv_cancel_right]

theorem lagX_le_normalizer [CharP F 2] : lagX m F ≤ normalizer (lagR0Grp m F : Set _) := by
  rintro _ ⟨A, rfl⟩
  rw [mem_normalizer_iff]
  intro g
  refine ⟨conj_mem_lagR0Grp A, fun h => ?_⟩
  have := conj_mem_lagR0Grp A⁻¹ h
  rwa [map_inv, inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc,
    inv_mul_cancel, mul_one] at this

end Groups

section Elementary

@[expose] def lagE (u v : Fin m ⊕ Fin m → F) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F :=
  vecMulVec u v + vecMulVec v u

theorem lagE_apply (u v : Fin m ⊕ Fin m → F) (x y : Fin m ⊕ Fin m) :
    lagE u v x y = u x * v y + v x * u y := rfl

theorem lagE_mem_lagAlt [CharP F 2] (u v : Fin m ⊕ Fin m → F) : lagE u v ∈ lagAlt m F :=
  ⟨by rw [lagE, transpose_add, transpose_vecMulVec, transpose_vecMulVec, add_comm], fun a => by
    rw [lagE_apply, mul_comm (v a), CharTwo.add_self_eq_zero]⟩

theorem conj_lagE (M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) (u v : Fin m ⊕ Fin m → F) :
    M * lagE u v * Mᵀ = lagE (M *ᵥ u) (M *ᵥ v) := by
  rw [lagE, Matrix.mul_add, Matrix.add_mul, mul_vecMulVec, mul_vecMulVec, vecMulVec_mul,
    vecMulVec_mul, vecMul_transpose, vecMul_transpose, lagE]

theorem lagE_add_left (u u' v : Fin m ⊕ Fin m → F) : lagE (u + u') v = lagE u v + lagE u' v := by
  rw [lagE, lagE, lagE, add_vecMulVec, vecMulVec_add]
  abel

theorem lagE_sub_right (u v v' : Fin m ⊕ Fin m → F) : lagE u (v - v') = lagE u v - lagE u v' := by
  rw [lagE, lagE, lagE, sub_vecMulVec, vecMulVec_sub]
  abel

theorem lagE_smul_left (c : F) (u v : Fin m ⊕ Fin m → F) : lagE (c • u) v = c • lagE u v := by
  rw [lagE, lagE, smul_vecMulVec, vecMulVec_smul, smul_add]

abbrev lagEl (a b : Fin m ⊕ Fin m) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F :=
  lagE (Pi.single a 1) (Pi.single b 1)

theorem lagEl_apply (a b x y : Fin m ⊕ Fin m) :
    (lagEl a b : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) x y =
      (if x = a ∧ y = b then 1 else 0) + (if x = b ∧ y = a then 1 else 0) := by
  simp only [lagEl, lagE_apply, Pi.single_apply, ite_and]
  split_ifs <;> simp

theorem lagOmegaStar_lagEl_of_ne_swap {a b : Fin m ⊕ Fin m} (hb : b ≠ a.swap) :
    lagOmegaStar m F (lagEl a b) = 0 := by
  rw [lagOmegaStar_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [lagEl_apply]
  rcases a with a | a <;> rcases b with b | b <;> simp_all [Sum.swap, eq_comm]

theorem eq_sum_lagUpper_smul_lagEl {D : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F}
    (hD : D ∈ lagAlt m F) : D = ∑ a, ∑ b, lagUpper D a b • (lagEl a b : Matrix _ _ F) := by
  conv_lhs => rw [eq_lagUpper_add_transpose hD]
  ext x y
  rw [Matrix.add_apply, transpose_apply, Matrix.sum_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, lagEl_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_and]
  simp [Finset.sum_ite_eq]

theorem diagonal_mulVec_single (d : Fin m ⊕ Fin m → F) (a : Fin m ⊕ Fin m) :
    diagonal d *ᵥ Pi.single a 1 = d a • Pi.single a 1 := by
  ext x
  rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs with h
  · rw [h]
  · simp

open scoped commutatorElement in
theorem lagRad_sub_conj_mem_commutator [CharP F 2] {C : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F}
    (hC : C ∈ lagR0 m F) (A : StatedSp m F) :
    lagRad m F (Multiplicative.ofAdd (C - mat m F A * C * (mat m F A)ᵀ)) ∈
      ⁅lagR0Grp m F, lagX m F⁆ := by
  rw [← commutatorElement_lagRad_lagLevi]
  exact commutator_mem_commutator ⟨C, hC, rfl⟩ ⟨A, rfl⟩

theorem diagSpEntry_mulSingle_ne_one {k : Fin m} {κ : Fˣ} (hκ : (κ : F) ≠ 1)
    {a : Fin m ⊕ Fin m} (ha : a ∈ coords k) : diagSpEntry (Pi.mulSingle k κ) a ≠ 1 := by
  rcases mem_coords.1 ha with rfl | rfl
  · rwa [diagSpEntry_mulSingle_inl_self]
  · rw [diagSpEntry_mulSingle_inr_self]
    intro h
    apply hκ
    have h2 : ((κ⁻¹ : Fˣ) : F) * κ = 1 * κ := by rw [h]
    rwa [Units.inv_mul, one_mul, eq_comm] at h2

theorem lagRad_smul_lagEl_mem [CharP F 2] {κ : F} (hκ0 : κ ≠ 0) (hκ1 : κ ≠ 1)
    {a b : Fin m ⊕ Fin m} (hab : b ≠ a) (hb : b ≠ a.swap) (c : F) :
    lagRad m F (Multiplicative.ofAdd (c • (lagEl a b : Matrix _ _ F))) ∈
      ⁅lagR0Grp m F, lagX m F⁆ := by
  obtain ⟨k, hk⟩ : ∃ k : Fin m, a ∈ coords k := by
    rcases a with k | k
    · exact ⟨k, inl_mem_coords k⟩
    · exact ⟨k, inr_mem_coords k⟩
  set u : Fˣ := Units.mk0 κ hκ0
  set d := diagSpEntry (Pi.mulSingle k u) with hd
  have hA : mat m F (rootTorusHom F m k u) = diagonal d := by
    rw [rootTorusHom_apply, mat_diagSp]
  have hbk : b ∉ coords k := by
    rw [mem_coords]
    rintro (rfl | rfl) <;> rcases mem_coords.1 hk with rfl | rfl <;> simp_all [Sum.swap]
  have hdb : d b = 1 := diagSpEntry_mulSingle_of_not_mem k u hbk
  have hda : d a ≠ 1 := diagSpEntry_mulSingle_ne_one (by simpa [u] using hκ1) hk
  have h1 : 1 - d a ≠ 0 := sub_ne_zero.2 (Ne.symm hda)
  have hC : (c * (1 - d a)⁻¹) • (lagEl a b : Matrix _ _ F) ∈ lagR0 m F :=
    ⟨Submodule.smul_mem _ _ (lagE_mem_lagAlt _ _), by
      show lagOmegaStar m F _ = 0
      rw [map_smul, lagOmegaStar_lagEl_of_ne_swap hb, smul_zero]⟩
  have key := lagRad_sub_conj_mem_commutator hC (rootTorusHom F m k u)
  convert key using 3
  rw [Matrix.mul_smul, Matrix.smul_mul, hA, conj_lagE, diagonal_mulVec_single,
    diagonal_mulVec_single, hdb, one_smul, lagE_smul_left, smul_smul, ← sub_smul]
  congr 1
  field_simp

end Elementary

section Generation

theorem mat_leviTv_mulVec_inl {i j : Fin m} (hij : i ≠ j) :
    mat m F (leviTv F hij 1) *ᵥ Pi.single (Sum.inl j) 1 =
      Pi.single (Sum.inl j) 1 + Pi.single (Sum.inl i) 1 := by
  rw [mulVec_single_one, mat_leviTv, coe_transvectionUnit_inv_transpose]
  ext x
  rcases x with x | x
  · simp only [Matrix.col_apply, fromBlocks_apply₁₁, transvection, Matrix.add_apply,
      Matrix.one_apply, single_apply, Pi.add_apply, Pi.single_apply, Sum.inl.injEq, and_true]
    by_cases h1 : x = j
    · subst h1
      simp [Ne.symm hij, hij]
    · by_cases h2 : x = i
      · subst h2
        simp [h1]
      · simp [h1, h2, Ne.symm h2]
  · simp [Matrix.col_apply]

theorem mat_leviTv_mulVec_inr {i j : Fin m} (hij : i ≠ j) :
    mat m F (leviTv F hij 1) *ᵥ Pi.single (Sum.inr i) 1 =
      Pi.single (Sum.inr i) 1 - Pi.single (Sum.inr j) 1 := by
  rw [mulVec_single_one, mat_leviTv, coe_transvectionUnit_inv_transpose]
  ext x
  rcases x with x | x
  · simp [Matrix.col_apply]
  · simp only [Matrix.col_apply, fromBlocks_apply₂₂, Matrix.add_apply, Matrix.one_apply,
      single_apply, Pi.sub_apply, Pi.single_apply, Sum.inr.injEq, and_true]
    by_cases h1 : x = i
    · subst h1
      simp [hij, Ne.symm hij]
    · by_cases h2 : x = j
      · subst h2
        simp [h1]
      · simp [h1, h2, Ne.symm h2]

theorem lagRad_smul_pair_mem [CharP F 2] {κ : F} (hκ0 : κ ≠ 0) (hκ1 : κ ≠ 1) {i j : Fin m}
    (hij : i ≠ j) (c : F) :
    lagRad m F (Multiplicative.ofAdd (c • ((lagEl (Sum.inl i) (Sum.inr i) : Matrix _ _ F) -
      lagEl (Sum.inl j) (Sum.inr j)))) ∈ ⁅lagR0Grp m F, lagX m F⁆ := by
  have hC : c • (lagEl (Sum.inl j) (Sum.inr i) : Matrix _ _ F) ∈ lagR0 m F :=
    ⟨Submodule.smul_mem _ _ (lagE_mem_lagAlt _ _), by
      show lagOmegaStar m F _ = 0
      rw [map_smul, lagOmegaStar_lagEl_of_ne_swap (by simp [Sum.swap, hij]), smul_zero]⟩
  have key := lagRad_sub_conj_mem_commutator hC (leviTv F hij 1)
  have key2 := lagRad_smul_lagEl_mem hκ0 hκ1 (a := Sum.inl i) (b := Sum.inr j) (by simp)
    (by simp [Sum.swap, Ne.symm hij]) c
  have := mul_mem key2 (inv_mem key)
  convert this using 1
  rw [← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add]
  congr 2
  rw [Matrix.mul_smul, Matrix.smul_mul, conj_lagE, mat_leviTv_mulVec_inl, mat_leviTv_mulVec_inr,
    lagE_add_left, lagE_sub_right, lagE_sub_right]
  simp only [smul_sub, smul_add]
  abel

theorem lagEl_pair_apply (i k : Fin m) :
    (lagEl (Sum.inl i) (Sum.inr i) : Matrix _ _ F) (Sum.inl k) (Sum.inr k) =
      if k = i then 1 else 0 := by
  rw [lagEl_apply]
  simp

theorem lagRad_mem_commutator_of_mem_lagR0 [CharP F 2] (hm : 1 ≤ m) {κ : F} (hκ0 : κ ≠ 0)
    (hκ1 : κ ≠ 1) {C : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F} (hC : C ∈ lagR0 m F) :
    lagRad m F (Multiplicative.ofAdd C) ∈ ⁅lagR0Grp m F, lagX m F⁆ := by
  set i₀ : Fin m := ⟨0, hm⟩
  set P : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F := ∑ i, C (Sum.inl i) (Sum.inr i) •
    ((lagEl (Sum.inl i) (Sum.inr i) : Matrix _ _ F) - lagEl (Sum.inl i₀) (Sum.inr i₀)) with hPdef
  have hP : Multiplicative.ofAdd P ∈ (⁅lagR0Grp m F, lagX m F⁆).comap (lagRad m F) := by
    rw [hPdef, ofAdd_sum]
    refine Subgroup.prod_mem _ fun i _ => ?_
    rw [Subgroup.mem_comap]
    by_cases hi : i = i₀
    · rw [hi, sub_self, smul_zero, ofAdd_zero, map_one]
      exact one_mem _
    · exact lagRad_smul_pair_mem hκ0 hκ1 hi _
  set D := C - P with hDdef
  have hDalt : D ∈ lagAlt m F := sub_mem hC.1 (Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (sub_mem (lagE_mem_lagAlt _ _) (lagE_mem_lagAlt _ _)))
  have hω : ∑ i, C (Sum.inl i) (Sum.inr i) = 0 := hC.2
  have hDpair : ∀ k, D (Sum.inl k) (Sum.inr k) = 0 := by
    intro k
    rw [hDdef, hPdef, Matrix.sub_apply, Matrix.sum_apply]
    simp only [Matrix.smul_apply, Matrix.sub_apply, lagEl_pair_apply, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
    by_cases hk : k = i₀ <;> simp [hk, hω]
  have hD : Multiplicative.ofAdd D ∈ (⁅lagR0Grp m F, lagX m F⁆).comap (lagRad m F) := by
    rw [eq_sum_lagUpper_smul_lagEl hDalt, ofAdd_sum]
    refine Subgroup.prod_mem _ fun a _ => ?_
    rw [ofAdd_sum]
    refine Subgroup.prod_mem _ fun b _ => ?_
    rw [Subgroup.mem_comap]
    by_cases hab : b = a
    · rw [hab, lagUpper_apply, ite_eq_right (lt_irrefl _), zero_smul, ofAdd_zero, map_one]
      exact one_mem _
    by_cases hb : b = a.swap
    · have h0 : lagUpper D a b = 0 := by
        rw [hb, lagUpper_apply]
        rcases a with k | k
        · simp [Sum.swap, hDpair]
        · rw [ite_eq_right]
          simp [Sum.swap, lagNum]
      rw [h0, zero_smul, ofAdd_zero, map_one]
      exact one_mem _
    · exact lagRad_smul_lagEl_mem hκ0 hκ1 hab hb _
  have hCD : C = D + P := by rw [hDdef, sub_add_cancel]
  rw [hCD, ofAdd_add, ← Subgroup.mem_comap]
  exact mul_mem hD hP

theorem commutator_lagR0Grp_lagX [CharP F 2] (hm : 1 ≤ m) {κ : F} (hκ0 : κ ≠ 0) (hκ1 : κ ≠ 1) :
    ⁅lagR0Grp m F, lagX m F⁆ = lagR0Grp m F := by
  apply le_antisymm
  · rw [commutator_le]
    rintro _ ⟨C, hC, rfl⟩ _ ⟨A, rfl⟩
    rw [commutatorElement_lagRad_lagLevi]
    exact ⟨_, sub_mem hC (conj_mem_lagR0 hC A), rfl⟩
  · rintro _ ⟨C, hC, rfl⟩
    exact lagRad_mem_commutator_of_mem_lagR0 hm hκ0 hκ1 hC

end Generation

section Centralizer

theorem conj_apply_eq_dotProduct (M C : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F)
    (x y : Fin m ⊕ Fin m) :
    (M * C * Mᵀ) x y = (fun p => M x p) ⬝ᵥ (C *ᵥ fun q => M y q) := by
  simp only [mul_apply, transpose_apply, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum,
    mul_assoc]
  exact Finset.sum_comm

theorem mat_leviTv_row_inl {i j : Fin m} (hij : i ≠ j) :
    (fun p => mat m F (leviTv F hij 1) (Sum.inl i) p) =
      Pi.single (Sum.inl i) 1 + Pi.single (Sum.inl j) 1 := by
  rw [mat_leviTv, coe_transvectionUnit_inv_transpose]
  ext p
  rcases p with p | p
  · simp only [fromBlocks_apply₁₁, transvection, Matrix.add_apply, Matrix.one_apply, single_apply,
      Pi.add_apply, Pi.single_apply, Sum.inl.injEq, true_and]
    by_cases h1 : p = i
    · subst h1
      simp [hij, Ne.symm hij]
    · by_cases h2 : p = j
      · subst h2
        simp [h1, Ne.symm h1]
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  · simp

theorem mat_leviTv_row_inr {i j : Fin m} (hij : i ≠ j) :
    (fun p => mat m F (leviTv F hij 1) (Sum.inr j) p) =
      Pi.single (Sum.inr j) 1 - Pi.single (Sum.inr i) 1 := by
  rw [mat_leviTv, coe_transvectionUnit_inv_transpose]
  ext p
  rcases p with p | p
  · simp
  · simp only [fromBlocks_apply₂₂, Matrix.add_apply, Matrix.one_apply, single_apply,
      Pi.sub_apply, Pi.single_apply, Sum.inr.injEq, true_and]
    by_cases h1 : p = j
    · subst h1
      simp [hij, Ne.symm hij]
    · by_cases h2 : p = i
      · subst h2
        simp [h1, Ne.symm h1]
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]

theorem eq_one_of_commute_lagX [CharP F 2] (hmo : Odd m) {κ : F} (hκ0 : κ ≠ 0) (hκ1 : κ ≠ 1)
    {g : GL ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) F} (hg : g ∈ lagR0Grp m F)
    (hc : ∀ x ∈ lagX m F, x * g = g * x) : g = 1 := by
  obtain ⟨C, hC, rfl⟩ := hg
  have hfix : ∀ A : StatedSp m F, mat m F A * C * (mat m F A)ᵀ = C := by
    intro A
    have h := hc _ ⟨A, rfl⟩
    rw [lagLevi_mul_lagRad] at h
    exact congrArg Multiplicative.toAdd (lagRad_injective (mul_right_cancel h))
  have hnp : ∀ x y : Fin m ⊕ Fin m, y ≠ x → y ≠ x.swap → C x y = 0 := by
    intro x y hyx hy
    obtain ⟨k, hk⟩ : ∃ k : Fin m, x ∈ coords k := by
      rcases x with k | k
      · exact ⟨k, inl_mem_coords k⟩
      · exact ⟨k, inr_mem_coords k⟩
    set u : Fˣ := Units.mk0 κ hκ0
    have hyk : y ∉ coords k := by
      rw [mem_coords]
      rintro (rfl | rfl) <;> rcases mem_coords.1 hk with rfl | rfl <;> simp_all [Sum.swap]
    have hdy : diagSpEntry (Pi.mulSingle k u) y = 1 := diagSpEntry_mulSingle_of_not_mem k u hyk
    have hdx : diagSpEntry (Pi.mulSingle k u) x ≠ 1 :=
      diagSpEntry_mulSingle_ne_one (by simpa [u] using hκ1) hk
    have h := congrFun (congrFun (hfix (rootTorusHom F m k u)) x) y
    rw [rootTorusHom_apply, mat_diagSp, diagonal_transpose, mul_diagonal, diagonal_mul, hdy,
      mul_one] at h
    have h2 : (diagSpEntry (Pi.mulSingle k u) x - 1) * C x y = 0 := by
      rw [sub_mul, h, one_mul, sub_self]
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hdx)
  have hpe : ∀ i j : Fin m, C (Sum.inl i) (Sum.inr i) = C (Sum.inl j) (Sum.inr j) := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    have h := congrFun (congrFun (hfix (leviTv F hij 1)) (Sum.inl i)) (Sum.inr j)
    rw [conj_apply_eq_dotProduct, mat_leviTv_row_inl hij, mat_leviTv_row_inr hij] at h
    simp only [add_dotProduct, mulVec_sub, mulVec_single_one, dotProduct_sub, single_dotProduct,
      one_mul, Matrix.col_apply] at h
    have h1 : C (Sum.inl i) (Sum.inr j) = 0 := hnp _ _ (by simp) (by simp [Sum.swap, Ne.symm hij])
    have h2 : C (Sum.inl j) (Sum.inr i) = 0 := hnp _ _ (by simp) (by simp [Sum.swap, hij])
    rw [h1, h2] at h
    linear_combination -h
  have hω : ∑ i, C (Sum.inl i) (Sum.inr i) = 0 := hC.2
  have hm1 : (m : F) = 1 := by
    obtain ⟨k, rfl⟩ := hmo
    push_cast
    rw [CharTwo.two_eq_zero, zero_mul, zero_add]
  have hc0 : ∀ i : Fin m, C (Sum.inl i) (Sum.inr i) = 0 := by
    intro i
    have h : ∑ j, C (Sum.inl j) (Sum.inr j) = (m : F) * C (Sum.inl i) (Sum.inr i) := by
      rw [Finset.sum_congr rfl fun j _ => hpe j i, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    rw [hω, hm1, one_mul] at h
    exact h.symm
  have hC0 : C = 0 := by
    ext x y
    rw [Matrix.zero_apply]
    by_cases hyx : y = x
    · rw [hyx]
      exact hC.1.2 x
    by_cases hy : y = x.swap
    · rw [hy]
      rcases x with k | k
      · exact hc0 k
      · rw [Sum.swap_inr, ← transpose_apply C, hC.1.1]
        exact hc0 k
    · exact hnp x y hyx hy
  rw [hC0, ofAdd_zero, map_one]

end Centralizer

section Order

variable (m F) in
@[expose] def lagSymEquiv :
    {C : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F // Cᵀ = C} ≃ (Sym2 (Fin m ⊕ Fin m) → F) :=
  (Equiv.subtypeEquiv Matrix.of.symm fun C => by
    rw [← Matrix.ext_iff]
    exact ⟨fun h a b => h b a, fun h i j => h j i⟩).trans
    (Sym2.lift (α := Fin m ⊕ Fin m) (β := F))

omit [Field F] in
theorem card_lagSym [Finite F] :
    Nat.card {C : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F // Cᵀ = C} =
      Nat.card F ^ (2 * m * (2 * m + 1) / 2) := by
  rw [Nat.card_congr (lagSymEquiv m F), Nat.card_fun, Nat.card_eq_fintype_card (α := Sym2 _),
    Sym2.card, Fintype.card_sum, Fintype.card_fin, ← two_mul, Nat.choose_two_right,
    Nat.add_sub_cancel, mul_comm]

theorem card_lagSym_le [Finite F] [CharP F 2] :
    Nat.card {C : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F // Cᵀ = C} ≤
      Nat.card (lagAlt m F) * Nat.card F ^ (2 * m) := by
  have hmem : ∀ S : {C : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F // Cᵀ = C},
      S.1 + diagonal (fun a => S.1 a a) ∈ lagAlt m F := fun S =>
    ⟨by rw [transpose_add, S.2, diagonal_transpose], fun a => by
      rw [Matrix.add_apply, diagonal_apply_eq, CharTwo.add_self_eq_zero]⟩
  have hinj : Function.Injective fun S : {C : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F // Cᵀ = C} =>
      ((⟨_, hmem S⟩ : lagAlt m F), fun a => S.1 a a) := by
    intro S T h
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    apply Subtype.ext
    rw [h2] at h1
    exact add_right_cancel h1
  calc Nat.card {C : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F // Cᵀ = C}
      ≤ Nat.card (lagAlt m F × (Fin m ⊕ Fin m → F)) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card (lagAlt m F) * Nat.card F ^ (2 * m) := by
      rw [Nat.card_prod, Nat.card_fun, Nat.card_sum, Nat.card_eq_fintype_card (α := Fin m),
        Fintype.card_fin, ← two_mul]

theorem card_lagAlt_le [Finite F] [CharP F 2] (hm : 1 ≤ m) :
    Nat.card (lagAlt m F) ≤ Nat.card (lagR0 m F) * Nat.card F := by
  set E : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F :=
    lagEl (Sum.inl (⟨0, hm⟩ : Fin m)) (Sum.inr ⟨0, hm⟩) with hEdef
  have hE : lagOmegaStar m F E = 1 := by
    rw [lagOmegaStar_apply, hEdef]
    simp [lagEl_pair_apply]
  have hmem : ∀ C : lagAlt m F, (C : Matrix _ _ F) - lagOmegaStar m F C • E ∈ lagR0 m F :=
    fun C => ⟨sub_mem C.2 (Submodule.smul_mem _ _ (lagE_mem_lagAlt _ _)), by
      show lagOmegaStar m F _ = 0
      rw [map_sub, map_smul, hE, smul_eq_mul, mul_one, sub_self]⟩
  have hinj : Function.Injective fun C : lagAlt m F =>
      ((⟨_, hmem C⟩ : lagR0 m F), lagOmegaStar m F C) := by
    intro C D h
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    apply Subtype.ext
    rw [h2] at h1
    exact sub_left_injective h1
  calc Nat.card (lagAlt m F) ≤ Nat.card (lagR0 m F × F) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card (lagR0 m F) * Nat.card F := Nat.card_prod _ _

theorem card_lagR0Grp : Nat.card (lagR0Grp m F) = Nat.card (lagR0 m F) := by
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun C : lagR0 m F =>
    (⟨lagRad m F (Multiplicative.ofAdd (C : Matrix _ _ F)), C, C.2, rfl⟩ : lagR0Grp m F)) ⟨?_, ?_⟩)
  · intro C D h
    exact Subtype.ext (lagRad_injective (congrArg Subtype.val h))
  · rintro ⟨_, C, hC, rfl⟩
    exact ⟨⟨C, hC⟩, rfl⟩

theorem card_lagR0Grp_lower [Finite F] [CharP F 2] (hm : 1 ≤ m) :
    Nat.card F ^ (2 * m * (2 * m + 1) / 2) ≤
      Nat.card (lagR0Grp m F) * Nat.card F * Nat.card F ^ (2 * m) := by
  rw [← card_lagSym, card_lagR0Grp]
  exact card_lagSym_le.trans (Nat.mul_le_mul_right _ (card_lagAlt_le hm))

end Order

section Perfect

variable (m F) in
@[expose] noncomputable def lagXEquiv [CharP F 2] : StatedSp m F ≃* lagX m F :=
  MonoidHom.ofInjective lagLevi_injective

variable (m F) in
@[expose] noncomputable def lagP [CharP F 2] :
    Subgroup (GL ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) F) :=
  lagR0Grp m F ⊔ lagX m F

theorem commutator_lagP [CharP F 2] [Group.IsPerfect (StatedSp m F)] (hm : 1 ≤ m) {κ : F}
    (hκ0 : κ ≠ 0) (hκ1 : κ ≠ 1) : ⁅lagP m F, lagP m F⁆ = lagP m F := by
  have hX : ⁅lagX m F, lagX m F⁆ = lagX m F := by
    have : Group.IsPerfect (lagX m F) := Group.IsPerfect.range _
    exact Subgroup.commutator_eq_self
  refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) ?_
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  apply sup_le
  · calc lagR0Grp m F = ⁅lagR0Grp m F, lagX m F⁆ := (commutator_lagR0Grp_lagX hm hκ0 hκ1).symm
      _ ≤ ⁅lagP m F, lagP m F⁆ := Subgroup.commutator_mono le_sup_left le_sup_right
  · calc lagX m F = ⁅lagX m F, lagX m F⁆ := hX.symm
      _ ≤ ⁅lagP m F, lagP m F⁆ := Subgroup.commutator_mono le_sup_right le_sup_right

end Perfect

end CFSG.SeitzReduction.SymplecticPilot
