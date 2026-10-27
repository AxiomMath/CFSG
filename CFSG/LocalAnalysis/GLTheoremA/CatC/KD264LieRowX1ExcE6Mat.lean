module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Exc.E6

open scoped MatrixGroups Matrix

section Blocks

variable {K : Type} [Field K]

@[expose] def blkEquiv : Fin 4 ⊕ Fin 2 ≃ Fin 6 :=
  finSumFinEquiv.trans (Equiv.swap (3 : Fin (4 + 2)) 4)

@[expose] noncomputable def blkM (A : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 6) (Fin 6) K :=
  Matrix.reindexAlgEquiv K K blkEquiv (Matrix.fromBlocks A 0 0 1)

theorem blkM_mul (A B : Matrix (Fin 4) (Fin 4) K) : blkM (A * B) = blkM A * blkM B := by
  simp only [blkM, ← map_mul, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, Matrix.mul_one]

theorem blkM_one : blkM (1 : Matrix (Fin 4) (Fin 4) K) = 1 := by
  simp [blkM, Matrix.fromBlocks_one]

theorem det_blkM (A : Matrix (Fin 4) (Fin 4) K) : (blkM A).det = A.det := by
  rw [blkM, Matrix.det_reindexAlgEquiv, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

@[expose] noncomputable def blk : SL(4, K) →* SL(6, K) where
  toFun h := ⟨blkM (h : Matrix (Fin 4) (Fin 4) K), by rw [det_blkM, h.2]⟩
  map_one' := Subtype.ext (by simp [blkM_one])
  map_mul' h h' := Subtype.ext (by
    show blkM ((h * h' : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) =
      blkM (h : Matrix (Fin 4) (Fin 4) K) * blkM (h' : Matrix (Fin 4) (Fin 4) K)
    rw [Matrix.SpecialLinearGroup.coe_mul, blkM_mul])

theorem blk_injective : Function.Injective (blk (K := K)) := by
  intro h h' hh
  have h1 : blkM (h : Matrix (Fin 4) (Fin 4) K) = blkM (h' : Matrix (Fin 4) (Fin 4) K) :=
    congrArg Subtype.val hh
  have h2 := (Matrix.reindexAlgEquiv K K blkEquiv).injective h1
  exact Subtype.ext (Matrix.fromBlocks_inj.1 h2).1

end Blocks

section Generic

variable {R : Type*} [CommRing R]

@[expose] def M2 : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 1]

@[expose] noncomputable def Tm : Matrix (Fin 6) (Fin 6) R :=
  Matrix.reindexAlgEquiv R R blkEquiv (Matrix.fromBlocks 1 0 0 M2)

theorem map_M2 {S : Type*} [CommRing S] (f : R →+* S) : (M2 : Matrix (Fin 2) (Fin 2) R).map f = M2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M2]

theorem map_Tm {S : Type*} [CommRing S] (f : R →+* S) :
    (Tm : Matrix (Fin 6) (Fin 6) R).map f = Tm := by
  ext i j
  simp only [Tm, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.map_apply]
  generalize blkEquiv.symm i = a
  generalize blkEquiv.symm j = b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, ← map_M2 f]

end Generic

section Centralizer

variable {K : Type} [Field K] [CharP K 2]

theorem blkM_comm_Tm (A : Matrix (Fin 4) (Fin 4) K) : blkM A * Tm = Tm * blkM A := by
  simp only [blkM, Tm, ← map_mul, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]

theorem M2_add_one_mul : ((M2 : Matrix (Fin 2) (Fin 2) K) + 1) * M2 = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M2, Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two, h2]

theorem M2_mul_add_one : (M2 : Matrix (Fin 2) (Fin 2) K) * (M2 + 1) = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M2, Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two, h2]

theorem matrix_add_self {m n : Type*} (B : Matrix m n K) : B + B = 0 := by
  ext i j
  simp [CharTwo.add_self_eq_zero]

theorem blocks_eq_zero_of_comm {A : Matrix (Fin 4) (Fin 4) K} {B : Matrix (Fin 4) (Fin 2) K}
    {C : Matrix (Fin 2) (Fin 4) K} {D : Matrix (Fin 2) (Fin 2) K}
    (h : Matrix.fromBlocks A B C D * Matrix.fromBlocks 1 0 0 M2 =
      Matrix.fromBlocks 1 0 0 M2 * Matrix.fromBlocks A B C D) : B = 0 ∧ C = 0 := by
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.one_mul, Matrix.fromBlocks_inj] at h
  obtain ⟨-, hB, hC, -⟩ := h
  constructor
  · have h1 : B * (M2 + 1 : Matrix (Fin 2) (Fin 2) K) = 0 := by
      rw [Matrix.mul_add, Matrix.mul_one, hB, matrix_add_self]
    calc B = B * 1 := (Matrix.mul_one B).symm
      _ = B * (((M2 : Matrix (Fin 2) (Fin 2) K) + 1) * M2) := by rw [M2_add_one_mul]
      _ = (B * ((M2 : Matrix (Fin 2) (Fin 2) K) + 1)) * M2 := (Matrix.mul_assoc _ _ _).symm
      _ = (0 : Matrix (Fin 4) (Fin 2) K) * M2 := congrArg (fun x => x * M2) h1
      _ = 0 := Matrix.zero_mul _
  · have h1 : (M2 + 1 : Matrix (Fin 2) (Fin 2) K) * C = 0 := by
      rw [Matrix.add_mul, Matrix.one_mul, ← hC, matrix_add_self]
    calc C = 1 * C := (Matrix.one_mul C).symm
      _ = ((M2 : Matrix (Fin 2) (Fin 2) K) * (M2 + 1)) * C := by rw [M2_mul_add_one]
      _ = M2 * (((M2 : Matrix (Fin 2) (Fin 2) K) + 1) * C) := Matrix.mul_assoc _ _ _
      _ = (M2 : Matrix (Fin 2) (Fin 2) K) * (0 : Matrix (Fin 2) (Fin 4) K) :=
          congrArg (fun x => M2 * x) h1
      _ = 0 := Matrix.mul_zero _

theorem exists_blockDiag_of_comm {g : Matrix (Fin 6) (Fin 6) K} (hg : g * Tm = Tm * g) :
    ∃ (A : Matrix (Fin 4) (Fin 4) K) (D : Matrix (Fin 2) (Fin 2) K),
      (Matrix.reindexAlgEquiv K K blkEquiv).symm g = Matrix.fromBlocks A 0 0 D := by
  set e := Matrix.reindexAlgEquiv K K blkEquiv with he
  set g' := e.symm g with hg'
  have hcomm : g' * Matrix.fromBlocks 1 0 0 M2 = Matrix.fromBlocks 1 0 0 M2 * g' := by
    apply e.injective
    rw [map_mul, map_mul, hg', AlgEquiv.apply_symm_apply]
    exact hg
  obtain ⟨A, B, C, D, hABCD⟩ : ∃ (A : Matrix (Fin 4) (Fin 4) K) (B : Matrix (Fin 4) (Fin 2) K)
      (C : Matrix (Fin 2) (Fin 4) K) (D : Matrix (Fin 2) (Fin 2) K),
      g' = Matrix.fromBlocks A B C D :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks g').symm⟩
  rw [hABCD] at hcomm
  obtain ⟨hB, hC⟩ := blocks_eq_zero_of_comm hcomm
  exact ⟨A, D, by rw [hABCD, hB, hC]⟩

theorem blk_conj_mem {g : SL(6, K)}
    (hg : (g : Matrix (Fin 6) (Fin 6) K) * Tm = Tm * (g : Matrix (Fin 6) (Fin 6) K))
    (h : SL(4, K)) : ∃ h' : SL(4, K), g * blk h = blk h' * g := by
  obtain ⟨A, D, hAD⟩ := exists_blockDiag_of_comm hg
  set e := Matrix.reindexAlgEquiv K K blkEquiv with he
  have hdet : A.det * D.det = 1 := by
    have h1 := congrArg Matrix.det hAD
    rw [Matrix.det_fromBlocks_zero₂₁] at h1
    rw [← h1]
    have : (e.symm (g : Matrix (Fin 6) (Fin 6) K)).det = 1 := by
      rw [he, Matrix.reindexAlgEquiv_symm, Matrix.det_reindexAlgEquiv, g.2]
    exact this
  have hAu : IsUnit A.det := IsUnit.of_mul_eq_one D.det hdet
  have hdet' : (A * (h : Matrix (Fin 4) (Fin 4) K) * A⁻¹).det = 1 := by
    rw [Matrix.det_conj ((Matrix.isUnit_iff_isUnit_det A).2 hAu), h.2]
  refine ⟨⟨A * (h : Matrix (Fin 4) (Fin 4) K) * A⁻¹, hdet'⟩, Subtype.ext ?_⟩
  show (g : Matrix (Fin 6) (Fin 6) K) * blkM (h : Matrix (Fin 4) (Fin 4) K) =
    blkM (A * (h : Matrix (Fin 4) (Fin 4) K) * A⁻¹) * (g : Matrix (Fin 6) (Fin 6) K)
  apply e.symm.injective
  have hblk : ∀ X : Matrix (Fin 4) (Fin 4) K, e.symm (blkM X) = Matrix.fromBlocks X 0 0 1 :=
    fun X => AlgEquiv.symm_apply_apply _ _
  rw [map_mul, map_mul, hblk, hblk, hAD]
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.one_mul, Matrix.fromBlocks_inj]
  refine ⟨?_, trivial, trivial, trivial⟩
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAu, Matrix.mul_one]

theorem blk_commute (h : SL(4, K)) :
    ((blk h : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) * Tm = Tm * (blk h : Matrix (Fin 6) (Fin 6) K) :=
  blkM_comm_Tm _

end Centralizer

section Facts

variable {K : Type} [Field K]

theorem eq_zero_or_eq_one_of_card_two' (hK : Nat.card K = 2) (x : K) : x = 0 ∨ x = 1 := by
  obtain ⟨a, b, hab, hS⟩ := Nat.card_eq_two_iff.1 hK
  have hmem : ∀ y : K, y = a ∨ y = b := fun y => by
    have : y ∈ ({a, b} : Set K) := by rw [hS]; exact Set.mem_univ y
    simpa using this
  by_contra hne
  push Not at hne
  obtain ⟨hx0, hx1⟩ := hne
  have h01' : (0 : K) ≠ 1 := zero_ne_one
  rcases hmem 0 with h0 | h0 <;> rcases hmem 1 with h1 | h1 <;> rcases hmem x with hx | hx
  all_goals first
    | exact h01' (h0.trans h1.symm)
    | exact hx0 (hx.trans h0.symm)
    | exact hx1 (hx.trans h1.symm)

theorem center_sl4_eq_bot (hK : Nat.card K = 2) : Subgroup.center SL(4, K) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨r, hr4, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  have hr1 : r = 1 := by
    rcases eq_zero_or_eq_one_of_card_two' hK r with rfl | rfl
    · simp at hr4
    · rfl
  rw [Subgroup.mem_bot]
  refine Subtype.ext ?_
  rw [← hrz, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]

@[expose] def om4 : Matrix (Fin 4) (Fin 4) (ZMod 2) := !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem om4_pow : om4 ^ 3 = 1 := by decide +kernel

theorem det_om4 : om4.det = 1 := by decide +kernel

variable [CharP K 2]

noncomputable def omSL : SL(4, K) :=
  ⟨(ZMod.castHom (dvd_refl 2) K).mapMatrix om4, by
    rw [← RingHom.map_det, det_om4, map_one]⟩

theorem omSL_pow_three : (omSL : SL(4, K)) ^ 3 = 1 := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  change ((ZMod.castHom (dvd_refl 2) K).mapMatrix om4) ^ 3 = 1
  rw [← map_pow, om4_pow, map_one]

theorem omSL_ne_one : (omSL : SL(4, K)) ≠ 1 := by
  intro h
  have h1 : ((ZMod.castHom (dvd_refl 2) K).mapMatrix om4 : Matrix (Fin 4) (Fin 4) K) = 1 :=
    congrArg Subtype.val h
  have h2 := congrFun (congrFun h1 0) 0
  simp [om4, RingHom.mapMatrix_apply] at h2

theorem three_dvd_card_sl4 : 3 ∣ Nat.card SL(4, K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h : orderOf (omSL : SL(4, K)) = 3 := orderOf_eq_prime omSL_pow_three omSL_ne_one
  rw [← h]
  exact orderOf_dvd_natCard _

end Facts

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Exc.E6

end
