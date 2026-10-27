module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.MatrixExtensionSymmetric
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix

open Matrix CFSG.Assembly.LowTwoRank SymplecticFlag SymplecticTorusWeyl

section Maps

variable {n : ℕ}

theorem binarySym_transpose (B : binarySymMatrices n) :
    (B : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = B :=
  B.2

variable (n) in
@[expose] def tauSym : Multiplicative (binarySymMatrices n) →* StatedSp n (ZMod 2) where
  toFun B := upperUnipotentSp n (ZMod 2) (binarySym_transpose B.toAdd)
  map_one' := statedSp_ext (by simp [fromBlocks_one])
  map_mul' B C := statedSp_ext (by
    simp only [Subgroup.coe_mul, Units.val_mul, coe_upperUnipotentSp, toAdd_mul,
      AddSubgroup.coe_add, fromBlocks_multiply]
    simp [add_comm])

theorem coe_tauSym (B : Multiplicative (binarySymMatrices n)) :
    (((tauSym n B : StatedSp n (ZMod 2)) : GL (Fin n ⊕ Fin n) (ZMod 2)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)) =
      fromBlocks 1 (B.toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) 0 1 :=
  coe_upperUnipotentSp _

theorem tauSym_injective : Function.Injective (tauSym n) := by
  intro B C h
  have h' := congrArg (fun g : StatedSp n (ZMod 2) => ((g : GL (Fin n ⊕ Fin n) (ZMod 2)) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2))) h
  simp only [coe_tauSym, fromBlocks_inj] at h'
  exact Multiplicative.toAdd.injective (Subtype.ext h'.2.1)

theorem coe_leviSp_inv (A : GL (Fin n) (ZMod 2)) :
    ((((leviSp A)⁻¹ : StatedSp n (ZMod 2)) : GL (Fin n ⊕ Fin n) (ZMod 2)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)) =
      fromBlocks ((A⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) 0 0
        (A : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ := by
  rw [← map_inv, coe_leviSp, inv_inv]

theorem congr_mem_binarySymMatrices (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (B : binarySymMatrices n) : A * (B : Matrix (Fin n) (Fin n) (ZMod 2)) * Aᵀ ∈
      binarySymMatrices n := by
  rw [mem_binarySymMatrices, transpose_mul, transpose_mul, transpose_transpose,
    binarySym_transpose, Matrix.mul_assoc]

theorem leviSp_mul_tauSym_mul_inv (A : GL (Fin n) (ZMod 2))
    (B : Multiplicative (binarySymMatrices n)) :
    leviSp A * tauSym n B * (leviSp A)⁻¹ = tauSym n (Multiplicative.ofAdd
      ⟨A * (B.toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) * (A : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ,
        congr_mem_binarySymMatrices _ _⟩) := by
  apply statedSp_ext
  have h₁ : (A : Matrix (Fin n) (Fin n) (ZMod 2)) * ((A⁻¹ : GL (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h₂ : ((A⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *
      (A : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = 1 := by
    rw [← transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one]
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_leviSp, coe_leviSp_inv,
    coe_tauSym, coe_tauSym, toAdd_ofAdd, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add, h₂, h₁]

theorem tauSym_eq_leviSp {B : Multiplicative (binarySymMatrices n)} {A : GL (Fin n) (ZMod 2)}
    (h : tauSym n B = leviSp A) : B = 1 ∧ A = 1 := by
  have h' := congrArg (fun g : StatedSp n (ZMod 2) => ((g : GL (Fin n ⊕ Fin n) (ZMod 2)) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2))) h
  simp only [coe_tauSym, coe_leviSp, fromBlocks_inj] at h'
  refine ⟨Multiplicative.toAdd.injective (Subtype.ext h'.2.1), Units.ext h'.1.symm⟩

theorem leviSp_injective {K : Type} [Field K] :
    Function.Injective (leviSp : GL (Fin n) K →* StatedSp n K) := by
  intro A A' h
  have h' := congrArg (fun g : StatedSp n K => ((g : GL (Fin n ⊕ Fin n) K) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) h
  simp only [coe_leviSp, fromBlocks_inj] at h'
  exact Units.ext h'.1

end Maps

section Unitriangular

variable (n : ℕ) (K : Type) [Field K]

@[expose] def unitriangularGL : Subgroup (GL (Fin n) K) where
  carrier := {A | IsUnitriangular (A : Matrix (Fin n) (Fin n) K)}
  one_mem' := isUnitriangular_one
  mul_mem' {A B} hA hB := by
    change IsUnitriangular ((A : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K))
    exact IsUnitriangular.mul hA hB
  inv_mem' {A} hA := by
    change IsUnitriangular ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [coe_units_inv]
    exact IsUnitriangular.inv hA

variable {n K}

theorem mem_unitriangularGL {A : GL (Fin n) K} :
    A ∈ unitriangularGL n K ↔ IsUnitriangular (A : Matrix (Fin n) (Fin n) K) :=
  Iff.rfl

theorem leviSp_mem_unipotent {A : GL (Fin n) K} (hA : A ∈ unitriangularGL n K) :
    leviSp A ∈ unipotent n K := by
  refine ⟨A, 0, hA, transpose_zero, ?_⟩
  rw [coe_leviSp, blockMat, Matrix.mul_zero, coe_units_inv]

theorem tauSym_mem_unipotent (B : Multiplicative (binarySymMatrices n)) :
    tauSym n B ∈ unipotent n (ZMod 2) := by
  refine ⟨1, B.toAdd, isUnitriangular_one, binarySym_transpose _, ?_⟩
  rw [coe_tauSym, blockMat, Matrix.one_mul, inv_one, transpose_one]

theorem exists_eq_leviSp_mul_tauSym {g : StatedSp n (ZMod 2)} (hg : g ∈ unipotent n (ZMod 2)) :
    ∃ A ∈ unitriangularGL n (ZMod 2), ∃ B : Multiplicative (binarySymMatrices n),
      g = leviSp A * tauSym n B := by
  obtain ⟨A, C, hA, hC, hgA⟩ := hg
  refine ⟨nonsingInvUnit A hA.isUnit_det, hA, Multiplicative.ofAdd ⟨C, hC⟩, ?_⟩
  apply statedSp_ext
  rw [hgA, Subgroup.coe_mul, Units.val_mul, coe_leviSp, coe_tauSym, blockMat_eq_mul]
  rfl

end Unitriangular

section Levi

theorem isPerfect_GL_three_zmod_two : Group.IsPerfect (GL (Fin 3) (ZMod 2)) := by
  have : Group.IsPerfect (SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  exact Group.IsPerfect.ofSurjective bijective_toGL_three_zmod_two.2

@[expose] def rangeLeviSpEquiv :
    (leviSp : GL (Fin 3) (ZMod 2) →* StatedSp 3 (ZMod 2)).range ≃*
      StatedProj (StatedSL 3 (ZMod 2)) :=
  (((MonoidHom.ofInjective leviSp_injective).symm.trans
    (MulEquiv.ofBijective _ bijective_toGL_three_zmod_two).symm).trans
    ((QuotientGroup.quotientMulEquivOfEq center_SL_three_zmod_two_eq_bot).trans
      QuotientGroup.quotientBot).symm).trans
    (projectiveSpecialLinearGroupEquivStatedProj 3 (ZMod 2))

theorem lieModel_range_leviSp :
    CFSG.Blueprint.LieModel (leviSp : GL (Fin 3) (ZMod 2) →* StatedSp 3 (ZMod 2)).range
      .PSL 3 2 1 :=
  Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩, ZMod 2,
    inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one], ⟨rangeLeviSpEquiv⟩⟩

end Levi

section Model

@[expose] def statedSpCongr {K L : Type} [Field K] [Field L] (φ : K ≃+* L) (n : ℕ) :
    StatedSp n K ≃* StatedSp n L :=
  ((MulEquiv.subgroupCongr CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic).trans
    (MonoidHom.toMulEquiv (TauCeti.GLSymplectic.map (Fin n) (φ : K →+* L))
      (TauCeti.GLSymplectic.map (Fin n) (φ.symm : L →+* K))
      (by
        rw [← TauCeti.GLSymplectic.map_comp, show ((φ.symm : L →+* K).comp (φ : K →+* L)) =
          RingHom.id K from RingHom.ext fun x => φ.symm_apply_apply x, TauCeti.GLSymplectic.map_id])
      (by
        rw [← TauCeti.GLSymplectic.map_comp, show ((φ : K →+* L).comp (φ.symm : L →+* K)) =
          RingHom.id L from RingHom.ext fun x => φ.apply_symm_apply x,
          TauCeti.GLSymplectic.map_id]))).trans
    (MulEquiv.subgroupCongr CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic.symm)

theorem statedScalars_subgroupOf_eq_bot {K : Type} [Field K] (hK : Nat.card K = 2) (n : ℕ) :
    (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hg
  rw [Subgroup.mem_bot]
  have hc1 : (c : K) = 1 := by
    have : Finite K := Nat.finite_of_card_ne_zero (by omega)
    have hu : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
    have : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp hu).1
    rw [Subsingleton.elim c 1, Units.val_one]
  apply statedSp_ext
  rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, hc1, map_one]
  rfl

theorem nonempty_mulEquiv_statedSp_of_lieModel {Q : Type} [Group Q]
    (hQ : CFSG.Blueprint.LieModel Q .PSp 3 2 1) : Nonempty (Q ≃* StatedSp 3 (ZMod 2)) := by
  rcases hQ with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hc
    have : Fintype K := Fintype.ofFinite K
    have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
    have hcard : Fintype.card K = Fintype.card (ZMod 2) := by
      rw [ZMod.card, ← Nat.card_eq_fintype_card, hK2]
    exact ⟨(e.trans ((QuotientGroup.quotientMulEquivOfEq
      (statedScalars_subgroupOf_eq_bot hK2 3)).trans QuotientGroup.quotientBot)).trans
      (statedSpCongr (FiniteField.ringEquivOfCardEq hcard) 3)⟩
  all_goals exact absurd h0 (by decide)

end Model

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
