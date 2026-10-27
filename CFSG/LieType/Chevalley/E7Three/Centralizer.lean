module

public import CFSG.LieType.Chevalley.E7Three.CentralizerFrame
public import CFSG.LieType.Chevalley.E7Three.CentralizerMatrix

public noncomputable section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.Centralizer

open Matrix CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KA5L CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.WeakCT CFSG.AGLEmbedding
  CFSG.LieType.Chevalley.E7Three.Weyl CFSG.LieType.Chevalley.E7Three.Cube
  CFSG.LieType.Chevalley.E7Three.PauliWords CFSG.LieType.Chevalley.E7Three.Product
  CFSG.LieType.Chevalley.E7Three.Frames CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Chevalley.E7Three.CentralizerMatrix

open scoped MatrixGroups Kronecker

@[expose] def e6 : Fin 2 × Fin 3 ≃ Fin 6 := finProdFinEquiv.trans (finCongr (by norm_num))

theorem e6_apply_val (p : Fin 2 × Fin 3) : (e6 p : ℕ) = p.2 + 3 * p.1 := by
  change ((finProdFinEquiv p : Fin (2 * 3)) : ℕ) = _
  rw [finProdFinEquiv_apply_val]

variable {K : Type} [Field K]

variable (K) in
@[expose] def kronSL2 : SL(2, K) →* SL(6, K) where
  toFun M := ⟨reindexAlgEquiv K K e6 ((M : Matrix (Fin 2) (Fin 2) K) ⊗ₖ
      (1 : Matrix (Fin 3) (Fin 3) K)), by
    rw [det_reindexAlgEquiv, det_kronecker, M.2, det_one, one_pow, one_pow, mul_one]⟩
  map_one' := Subtype.ext (by
    simp only [Matrix.SpecialLinearGroup.coe_one, one_kronecker_one, map_one])
  map_mul' M N := Subtype.ext (by
    change reindexAlgEquiv K K e6 (((M * N : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) ⊗ₖ
        (1 : Matrix (Fin 3) (Fin 3) K)) =
      reindexAlgEquiv K K e6 ((M : Matrix (Fin 2) (Fin 2) K) ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) K)) *
        reindexAlgEquiv K K e6 ((N : Matrix (Fin 2) (Fin 2) K) ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) K))
    rw [← map_mul, ← mul_kronecker_mul, Matrix.one_mul]
    rfl)

theorem coe_kronSL2 (M : SL(2, K)) : ((kronSL2 K M : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) =
    reindex e6 e6 ((M : Matrix (Fin 2) (Fin 2) K) ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) K)) := rfl

variable [CharP K 2]

theorem coe_upper_mul_lower (A : SL(3, K)) :
    ((upperSL3 K A * lowerSL3 K A : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) =
      reindex e6 e6 ((1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ (A : Matrix (Fin 3) (Fin 3) K)) := by
  ext p q
  obtain ⟨⟨i, j⟩, rfl⟩ := e6.surjective p
  obtain ⟨⟨i', j'⟩, rfl⟩ := e6.surjective q
  rw [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    kroneckerMap_apply, Matrix.SpecialLinearGroup.coe_mul, upperSL3, lowerSL3, coe_blockSL,
    coe_blockSL, Matrix.mul_apply, Fin.sum_univ_six]
  simp only [CFSG.ClassicalInvolution.Phan.blockMat_apply, e6_apply_val]
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
    simp [Matrix.one_apply, Fin.ext_iff, e6_apply_val]

theorem coe_scalar6 {ζ : Kˣ} (hζ : ζ ^ 3 = 1) :
    ((upperSL3 K (centralWord ζ) * lowerSL3 K (centralWord ζ) : SL(6, K)) :
      Matrix (Fin 6) (Fin 6) K) = (ζ : K) • (1 : Matrix (Fin 6) (Fin 6) K) := by
  rw [coe_upper_mul_lower, centralWord_val ζ hζ, Matrix.scalar_apply, ← smul_one_eq_diagonal,
    kronecker_smul, one_kronecker_one]
  ext i j
  rw [reindex_apply, submatrix_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.one_apply]
  simp only [e6.symm.injective.eq_iff]

theorem reindex_e6_mul (X Y : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) K) :
    reindex e6 e6 X * reindex e6 e6 Y = reindex e6 e6 (X * Y) := by
  rw [← reindexAlgEquiv_apply K K, ← reindexAlgEquiv_apply K K, ← reindexAlgEquiv_apply K K,
    map_mul]

theorem sl3_eq_center_mul {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) (B : SL(3, K)) {z₁ z₂ : SL(3, K)}
    (hz₁ : z₁ ∈ Subgroup.center SL(3, K)) (hz₂ : z₂ ∈ Subgroup.center SL(3, K))
    (hX : B * diagonalWord ζ = z₁ * (diagonalWord ζ * B))
    (hC : B * cycleWord ^ 2 = z₂ * (cycleWord ^ 2 * B)) :
    ∃ (a b : ℕ) (z : SL(3, K)), z ∈ Subgroup.center SL(3, K) ∧
      B = z * (diagonalWord ζ ^ a * cycleWord ^ b) := by
  have hζK : IsPrimitiveRoot (ζ : K) 3 := IsPrimitiveRoot.coe_units_iff.2 hζ
  obtain ⟨r₁, hr₁, hz₁e⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz₁
  obtain ⟨r₂, hr₂, hz₂e⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz₂
  rw [Fintype.card_fin] at hr₁ hr₂
  have hsc (r : K) (M : Matrix (Fin 3) (Fin 3) K) : Matrix.scalar (Fin 3) r * M = r • M := by
    rw [Matrix.scalar_apply, ← smul_one_eq_diagonal, smul_mul_assoc, Matrix.one_mul]
  have hY3 : (heisYMat : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    have := congrArg (fun g : SL(3, K) => (g : Matrix (Fin 3) (Fin 3) K))
      (cycleWord_pow_three (K := K))
    simpa only [Matrix.SpecialLinearGroup.coe_pow, cycleWord_val,
      Matrix.SpecialLinearGroup.coe_one] using this
  have hY4 : (heisYMat : Matrix (Fin 3) (Fin 3) K) ^ 4 = heisYMat := by
    rw [pow_succ, hY3, Matrix.one_mul]
  have hmX : (B : Matrix (Fin 3) (Fin 3) K) * heisXMat (ζ : K) =
      r₁ • (heisXMat (ζ : K) * B) := by
    have := congrArg (fun g : SL(3, K) => (g : Matrix (Fin 3) (Fin 3) K)) hX
    simp only [Matrix.SpecialLinearGroup.coe_mul, diagonalWord_val ζ hζ.pow_eq_one] at this
    rw [this, ← hz₁e, hsc]
  have hmY2 : (B : Matrix (Fin 3) (Fin 3) K) * heisYMat ^ 2 =
      r₂ • (heisYMat ^ 2 * (B : Matrix (Fin 3) (Fin 3) K)) := by
    have := congrArg (fun g : SL(3, K) => (g : Matrix (Fin 3) (Fin 3) K)) hC
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow,
      cycleWord_val] at this
    rw [this, ← hz₂e, hsc]
  have hmY : (B : Matrix (Fin 3) (Fin 3) K) * heisYMat =
      r₂ ^ 2 • (heisYMat * (B : Matrix (Fin 3) (Fin 3) K)) := by
    calc (B : Matrix (Fin 3) (Fin 3) K) * heisYMat =
          ((B : Matrix (Fin 3) (Fin 3) K) * heisYMat ^ 2) * heisYMat ^ 2 := by
          rw [Matrix.mul_assoc, ← pow_add, hY4]
      _ = (r₂ • (heisYMat ^ 2 * (B : Matrix (Fin 3) (Fin 3) K))) * heisYMat ^ 2 := by
          rw [hmY2]
      _ = r₂ • (heisYMat ^ 2 * ((B : Matrix (Fin 3) (Fin 3) K) * heisYMat ^ 2)) := by
          rw [smul_mul_assoc, Matrix.mul_assoc]
      _ = r₂ • (heisYMat ^ 2 * (r₂ • (heisYMat ^ 2 * (B : Matrix (Fin 3) (Fin 3) K)))) := by
          rw [hmY2]
      _ = r₂ ^ 2 • (heisYMat * (B : Matrix (Fin 3) (Fin 3) K)) := by
          rw [mul_smul_comm, smul_smul, ← Matrix.mul_assoc, ← pow_add, hY4, sq]
  obtain ⟨a, b, r, hr⟩ := eq_smul_heis_of_twisted hζK hr₁
    (by rw [← pow_mul, mul_comm, pow_mul, hr₂, one_pow]) hmX hmY
  have hW : ((diagonalWord ζ ^ a * cycleWord ^ b : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      heisXMat (ζ : K) ^ a * heisYMat ^ b := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow,
      diagonalWord_val ζ hζ.pow_eq_one, cycleWord_val]
  have hdet : r ^ 3 = 1 := by
    have h1 := B.2
    have h2 := (diagonalWord ζ ^ a * cycleWord ^ b).2
    rw [hW] at h2
    rw [hr, Matrix.det_smul, h2, mul_one, Fintype.card_fin] at h1
    exact h1
  refine ⟨a, b, ⟨Matrix.scalar (Fin 3) r, by
    rw [Matrix.scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      hdet]⟩, ?_, ?_⟩
  · exact Matrix.SpecialLinearGroup.mem_center_iff.2 ⟨r, by rw [Fintype.card_fin, hdet], rfl⟩
  · have hB : (B : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) r *
        ((diagonalWord ζ ^ a * cycleWord ^ b : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) := by
      rw [hW, hsc, hr]
    exact Subtype.ext hB

theorem sl6_eq_kronSL2_mul {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) (A : SL(6, K))
    (hX : A * (upperSL3 K (diagonalWord ζ) * lowerSL3 K (diagonalWord ζ)) =
      upperSL3 K (diagonalWord ζ) * lowerSL3 K (diagonalWord ζ) * A)
    (hC : A * (upperSL3 K cycleWord * lowerSL3 K cycleWord) =
      upperSL3 K cycleWord * lowerSL3 K cycleWord * A) :
    ∃ (M : SL(2, K)) (j : ℕ),
      A = kronSL2 K M * (upperSL3 K (centralWord ζ) * lowerSL3 K (centralWord ζ)) ^ j := by
  have hζK : IsPrimitiveRoot (ζ : K) 3 := IsPrimitiveRoot.coe_units_iff.2 hζ
  set N : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) K :=
    reindex e6.symm e6.symm (A : Matrix (Fin 6) (Fin 6) K) with hN
  have hA : (A : Matrix (Fin 6) (Fin 6) K) = reindex e6 e6 N := by
    ext i j
    simp [hN]
  have key (W : SL(3, K))
      (hW : A * (upperSL3 K W * lowerSL3 K W) = upperSL3 K W * lowerSL3 K W * A) :
      N * ((1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ (W : Matrix (Fin 3) (Fin 3) K)) =
        ((1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ (W : Matrix (Fin 3) (Fin 3) K)) * N := by
    have hW' : (A : Matrix (Fin 6) (Fin 6) K) *
        reindex e6 e6 ((1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ (W : Matrix (Fin 3) (Fin 3) K)) =
          reindex e6 e6 ((1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ (W : Matrix (Fin 3) (Fin 3) K)) * A := by
      rw [← coe_upper_mul_lower, ← Matrix.SpecialLinearGroup.coe_mul, hW,
        Matrix.SpecialLinearGroup.coe_mul]
    rw [hA, reindex_e6_mul, reindex_e6_mul] at hW'
    exact (reindex e6 e6).injective hW'
  have hNX := key (diagonalWord ζ) hX
  rw [diagonalWord_val ζ hζ.pow_eq_one] at hNX
  have hNY := key cycleWord hC
  rw [cycleWord_val] at hNY
  have hNk := eq_kronecker_one_of_commute hζK hNX hNY
  set M0 : Matrix (Fin 2) (Fin 2) K := Matrix.of fun i i' => N (i, 0) (i', 0) with hM0
  have hdet0 : M0.det ^ 3 = 1 := by
    have h := A.2
    rw [hA, det_reindex_self, hNk, det_kronecker, det_one, one_pow, mul_one, Fintype.card_fin] at h
    exact h
  obtain ⟨k, -, hkζ⟩ := hζK.eq_pow_of_pow_eq_one hdet0
  have hζ0 : (ζ : K) ≠ 0 := ζ.ne_zero
  set ν : K := (ζ : K) ^ (2 * k) with hν
  have hν0 : ν ≠ 0 := pow_ne_zero _ hζ0
  have hν2 : ν ^ 2 = M0.det := by
    rw [hν, ← hkζ, ← pow_mul, show 2 * k * 2 = k + 3 * k by ring, pow_add, pow_mul,
      hζK.pow_eq_one, one_pow, mul_one]
  have hdet0' : M0.det ≠ 0 := by
    rw [← hν2]
    exact pow_ne_zero _ hν0
  have hM1 : (ν⁻¹ • M0).det = 1 := by
    rw [det_smul, Fintype.card_fin, inv_pow, hν2, inv_mul_cancel₀ hdet0']
  refine ⟨⟨ν⁻¹ • M0, hM1⟩, 2 * k, ?_⟩
  have hmat : (A : Matrix (Fin 6) (Fin 6) K) =
      ((kronSL2 K ⟨ν⁻¹ • M0, hM1⟩ : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) *
        ((upperSL3 K (centralWord ζ) * lowerSL3 K (centralWord ζ)) ^ (2 * k) : SL(6, K)) := by
    have h1 : ((kronSL2 K ⟨ν⁻¹ • M0, hM1⟩ : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) =
        reindex e6 e6 ((ν⁻¹ • M0) ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) K)) := rfl
    have h2 : (((upperSL3 K (centralWord ζ) * lowerSL3 K (centralWord ζ)) ^ (2 * k) : SL(6, K)) :
        Matrix (Fin 6) (Fin 6) K) = ν • (1 : Matrix (Fin 6) (Fin 6) K) := by
      rw [Matrix.SpecialLinearGroup.coe_pow, coe_scalar6 hζ.pow_eq_one, smul_pow, one_pow]
    rw [h1, h2, hA, hNk, Matrix.mul_smul, Matrix.mul_one]
    ext i j
    simp only [reindex_apply, submatrix_apply, Matrix.smul_apply, kroneckerMap_apply, smul_eq_mul]
    change M0 _ _ * _ = ν * ((ν⁻¹ * M0 _ _) * _)
    field_simp
  exact Subtype.ext hmat

@[expose] def a5SimpleRoots : Set (Fin Tag.E7.rank → ℤ) :=
  {r | ∃ i ∈ a5Nodes .E7, r = Pi.single i 1 ∨ r = -Pi.single i 1}

theorem range_a5Frame_le_rootSpan :
    (a5Frame K).range ≤ rootSpan .E7 K a5SimpleRoots := by
  rw [range_a5Frame, subsystemGroup, Subgroup.closure_le]
  rintro _ ⟨i, hi, c, rfl | rfl⟩
  · exact Subgroup.mem_iSup_of_mem (Pi.single i 1)
      (Subgroup.mem_iSup_of_mem ⟨i, hi, Or.inl rfl⟩ (xUnit_mem_rootSubgroup i c))
  · exact Subgroup.mem_iSup_of_mem (-Pi.single i 1)
      (Subgroup.mem_iSup_of_mem ⟨i, hi, Or.inr rfl⟩ (yUnit_mem_rootSubgroup i c))

theorem range_a5Frame_le_adjointGroup : (a5Frame K).range ≤ adjointGroup .E7 K :=
  range_a5Frame_le_rootSpan.trans (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α)

theorem a5Frame_mem_adjointGroup (A : SL(6, K)) : a5Frame K A ∈ adjointGroup .E7 K :=
  range_a5Frame_le_adjointGroup ⟨A, rfl⟩

theorem a5_orthogonal_a2 : ∀ i : Fin Tag.E7.rank, (i : ℕ) ∈ ({1, 3, 4, 5, 6} : Finset ℕ) →
    ∀ j k : Fin 3, (Pi.single i 1 : Fin Tag.E7.rank → ℤ) ⬝ᵥ
      (Tag.E7.symmetrizedCartan *ᵥ nativeA2Roots 2 j k) = 0 := by
  decide +kernel

theorem a5Frame_commute_theta_two (w : NativeFrame K) (A : SL(6, K)) (B : SL(3, K)) :
    Commute (a5Frame K A) (theta w 2 B) := by
  have hS₁ : ∀ r ∈ a5SimpleRoots, IsRoot .E7 r := by
    rintro r ⟨i, -, rfl | rfl⟩
    · exact isRoot_single _ i
    · exact isRoot_neg_single _ i
  have hS₂ : ∀ r ∈ {r | ∃ i j : Fin 3, i ≠ j ∧ r = nativeA2Roots 2 i j}, IsRoot .E7 r := by
    rintro r ⟨i, j, hij, rfl⟩
    exact (w.isFrame 2).isRoot i j hij
  have horth : ∀ α ∈ a5SimpleRoots, ∀ β ∈ {r | ∃ i j : Fin 3, i ≠ j ∧ r = nativeA2Roots 2 i j},
      α ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ β) = 0 := by
    rintro α ⟨i, hi, rfl | rfl⟩ β ⟨j, k, -, rfl⟩
    · have hi' : (i : ℕ) ∈ ({1, 3, 4, 5, 6} : Finset ℕ) := by
        simpa [a5Nodes] using hi
      exact a5_orthogonal_a2 i hi' j k
    · have hi' : (i : ℕ) ∈ ({1, 3, 4, 5, 6} : Finset ℕ) := by
        simpa [a5Nodes] using hi
      rw [neg_dotProduct, a5_orthogonal_a2 i hi' j k, neg_zero]
  have hx : a5Frame K A ∈ rootSpan .E7 K a5SimpleRoots := range_a5Frame_le_rootSpan ⟨A, rfl⟩
  have hy : theta w 2 B ∈ rootSpan .E7 K {r | ∃ i j : Fin 3, i ≠ j ∧ r = nativeA2Roots 2 i j} := by
    rw [← range_theta_two]
    exact ⟨B, rfl⟩
  exact rootSpan_commute_of_orth (L := K) (Or.inr (Or.inr (Or.inl rfl))) hS₁ hS₂ horth _ hx _ hy

theorem theta_two_injective (w : NativeFrame K) : Function.Injective (theta w 2) := by
  intro A B h
  have h' := congrArg (conjDiag3 (w.diag 2)⁻¹) ((w.isFrame 2).injective h)
  have e : ∀ C : SL(3, K), conjDiag3 (w.diag 2)⁻¹ (conjDiag3 (w.diag 2) C) = C := fun C => by
    simpa only [inv_inv] using conjDiag3_conjDiag3_inv (w.diag 2)⁻¹ C
  simpa only [conjDiag3Hom_apply, e] using h'

theorem frame_mul (w : NativeFrame K) (A₁ A₂ : SL(6, K)) (B₁ B₂ : SL(3, K)) :
    a5Frame K A₁ * theta w 2 B₁ * (a5Frame K A₂ * theta w 2 B₂) =
      a5Frame K (A₁ * A₂) * theta w 2 (B₁ * B₂) := by
  rw [map_mul, map_mul, mul_assoc, ← mul_assoc (theta w 2 B₁),
    ← (a5Frame_commute_theta_two w A₂ B₁).eq]
  group

theorem frame_pow (w : NativeFrame K) (A : SL(6, K)) (B : SL(3, K)) (n : ℕ) :
    (a5Frame K A * theta w 2 B) ^ n = a5Frame K (A ^ n) * theta w 2 (B ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, frame_mul, ← pow_succ, ← pow_succ]

theorem frame_inv (w : NativeFrame K) (A : SL(6, K)) (B : SL(3, K)) :
    (a5Frame K A * theta w 2 B)⁻¹ = a5Frame K A⁻¹ * theta w 2 B⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, frame_mul, mul_inv_cancel, mul_inv_cancel, map_one, map_one, one_mul]

theorem mem_center_of_a5Frame_eq (w : NativeFrame K) {A : SL(6, K)} {B : SL(3, K)}
    (h : a5Frame K A = theta w 2 B) : B ∈ Subgroup.center SL(3, K) := by
  rw [Subgroup.mem_center_iff]
  intro C
  apply theta_two_injective w
  rw [map_mul, map_mul, ← h]
  exact (a5Frame_commute_theta_two w A C).eq.symm

theorem exists_center_of_frame_eq (w : NativeFrame K) {A₁ A₂ : SL(6, K)} {B₁ B₂ : SL(3, K)}
    (h : a5Frame K A₁ * theta w 2 B₁ = a5Frame K A₂ * theta w 2 B₂) :
    ∃ z ∈ Subgroup.center SL(3, K), B₁ = z * B₂ := by
  have h' : a5Frame K (A₂⁻¹ * A₁) = theta w 2 (B₂ * B₁⁻¹) := by
    rw [map_mul, map_mul, map_inv, map_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc,
      eq_mul_inv_iff_mul_eq, h]
  refine ⟨(B₂ * B₁⁻¹)⁻¹, Subgroup.inv_mem _ (mem_center_of_a5Frame_eq w h'), ?_⟩
  group

theorem kronSL2_commute (M : SL(2, K)) (W : SL(3, K)) :
    Commute (kronSL2 K M) (upperSL3 K W * lowerSL3 K W) := by
  apply Subtype.ext
  change ((kronSL2 K M : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) *
      ((upperSL3 K W * lowerSL3 K W : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) =
    ((upperSL3 K W * lowerSL3 K W : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) *
      ((kronSL2 K M : SL(6, K)) : Matrix (Fin 6) (Fin 6) K)
  rw [coe_kronSL2, coe_upper_mul_lower, reindex_e6_mul, reindex_e6_mul, ← mul_kronecker_mul,
    ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]

theorem exists_centralWord_pow {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) {z : SL(3, K)}
    (hz : z ∈ Subgroup.center SL(3, K)) : ∃ m : ℕ, z = centralWord ζ ^ m := by
  obtain ⟨r, hr, hzr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  rw [Fintype.card_fin] at hr
  obtain ⟨m, -, hm⟩ := (IsPrimitiveRoot.coe_units_iff.2 hζ).eq_pow_of_pow_eq_one hr
  refine ⟨m, Subtype.ext ?_⟩
  change (z : Matrix (Fin 3) (Fin 3) K) = ((centralWord ζ ^ m : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)
  rw [Matrix.SpecialLinearGroup.coe_pow, centralWord_val ζ hζ.pow_eq_one, ← map_pow, hm, hzr]

theorem a5Frame_injective {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) : Function.Injective (a5Frame K) := by
  obtain ⟨w⟩ := nativeFrame_exists (K := K)
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro z hz
  obtain ⟨r, hr, hzr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 (ker_a5Frame_le_center hz)
  rw [Fintype.card_fin] at hr
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hr3 : r ^ 3 = 1 := by
    have h : (r ^ 3 - 1) ^ 2 = 0 := by linear_combination hr + (1 - r ^ 3) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h)
  have hζK := IsPrimitiveRoot.coe_units_iff.2 hζ
  obtain ⟨k, hk, hkr⟩ := hζK.eq_pow_of_pow_eq_one hr3
  have hz' : z = (upperSL3 K (centralWord ζ) * lowerSL3 K (centralWord ζ)) ^ k := by
    apply Subtype.ext
    change (z : Matrix (Fin 6) (Fin 6) K) = (((upperSL3 K (centralWord ζ) *
      lowerSL3 K (centralWord ζ)) ^ k : SL(6, K)) : Matrix (Fin 6) (Fin 6) K)
    rw [Matrix.SpecialLinearGroup.coe_pow, coe_scalar6 hζ.pow_eq_one, smul_pow, one_pow, hkr, ← hzr,
      Matrix.scalar_apply, smul_one_eq_diagonal]
  have h1 : (scalarWord ζ : ModGL .E7 K) ^ k = 1 := by
    rw [MonoidHom.mem_ker, hz', map_pow, ← scalarWord_eq w ζ] at hz
    exact hz
  rw [scalarWord_val ζ hζ.pow_eq_one] at h1
  change rootDiagUnitHom .E7 K (cubeChar ζ scalarExp) ^ k = 1 at h1
  rw [← map_pow, ← map_one (rootDiagUnitHom .E7 K)] at h1
  have h1' := congrFun (rootDiagUnit_injective h1) (e7Index 2)
  simp only [Pi.pow_apply, Pi.one_apply, cubeChar, scalarExp] at h1'
  have hk0 : k = 0 := by
    have : (ζ : Kˣ) ^ k = 1 := by
      have e : (![0, 0, 1, 0, 0, 0, 0] : Fin Tag.E7.rank → ℤ) (e7Index 2) = 1 := rfl
      rwa [e, zpow_one] at h1'
    have := (hζ.pow_eq_one_iff_dvd k).1 this
    omega
  rw [hz', hk0, pow_zero]
  exact Subgroup.one_mem _

variable (K) in
@[expose] def cubeSL2 : SL(2, K) →* ModGL .E7 K := (a5Frame K).comp (kronSL2 K)

@[expose] def cubeE (ζ : Kˣ) (hζ : ζ ^ 3 = 1) : Subgroup (ModGL .E7 K) :=
  (cubeHom ζ hζ).range.map (adjointGroup .E7 K).subtype

@[expose] def cubeCent (ζ : Kˣ) (hζ : ζ ^ 3 = 1) : Subgroup (ModGL .E7 K) :=
  adjointGroup .E7 K ⊓ Subgroup.centralizer (cubeE ζ hζ : Set (ModGL .E7 K))

theorem mem_cubeE {ζ : Kˣ} {hζ : ζ ^ 3 = 1} {x : ModGL .E7 K} :
    x ∈ cubeE ζ hζ ↔ ∃ f, x = (cubeHom ζ hζ f : ModGL .E7 K) := by
  constructor
  · rintro ⟨_, ⟨f, rfl⟩, rfl⟩
    exact ⟨f, rfl⟩
  · rintro ⟨f, rfl⟩
    exact ⟨_, ⟨f, rfl⟩, rfl⟩

theorem generators_mem_cubeE (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (i : Fin 3) :
    (generators ζ i : ModGL .E7 K) ∈ cubeE ζ hζ :=
  ⟨_, generators_mem_range ζ hζ i, rfl⟩

theorem cubeE_le_adjointGroup (ζ : Kˣ) (hζ : ζ ^ 3 = 1) : cubeE ζ hζ ≤ adjointGroup .E7 K := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem cubeE_commute {ζ : Kˣ} {hζ : ζ ^ 3 = 1} {x y : ModGL .E7 K} (hx : x ∈ cubeE ζ hζ)
    (hy : y ∈ cubeE ζ hζ) : Commute x y := by
  obtain ⟨f, rfl⟩ := mem_cubeE.1 hx
  obtain ⟨f', rfl⟩ := mem_cubeE.1 hy
  change (cubeHom ζ hζ f : ModGL .E7 K) * cubeHom ζ hζ f' = cubeHom ζ hζ f' * cubeHom ζ hζ f
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, mul_comm]

theorem cubeE_le_cubeCent (ζ : Kˣ) (hζ : ζ ^ 3 = 1) : cubeE ζ hζ ≤ cubeCent ζ hζ :=
  fun _ hx => ⟨cubeE_le_adjointGroup ζ hζ hx, Subgroup.mem_centralizer_iff.2 fun _ hy =>
    (cubeE_commute hy hx).eq⟩

theorem mem_cubeCent_iff {ζ : Kˣ} {hζ : ζ ^ 3 = 1} {g : ModGL .E7 K} :
    g ∈ cubeCent ζ hζ ↔ g ∈ adjointGroup .E7 K ∧ Commute g (scalarWord ζ : ModGL .E7 K) ∧
      Commute g (pairedWord ζ : ModGL .E7 K) ∧ Commute g (cyclic (K := K) : ModGL .E7 K) := by
  constructor
  · rintro ⟨hG, hC⟩
    have h (i : Fin 3) : Commute g (generators ζ i : ModGL .E7 K) :=
      ((Subgroup.mem_centralizer_iff.1 hC) _ (generators_mem_cubeE ζ hζ i)).symm
    exact ⟨hG, h 0, h 1, h 2⟩
  · rintro ⟨hG, hs, hp, hc⟩
    refine ⟨hG, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
    obtain ⟨f, rfl⟩ := mem_cubeE.1 hx
    rw [cubeHom_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow,
      Subgroup.coe_pow]
    exact (((hs.pow_right _).mul_right (hp.pow_right _)).mul_right (hc.pow_right _)).symm.eq

theorem range_cubeSL2_le_cubeCent (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    (cubeSL2 K).range ≤ cubeCent ζ hζ := by
  obtain ⟨w⟩ := nativeFrame_exists (K := K)
  rintro _ ⟨M, rfl⟩
  refine mem_cubeCent_iff.2 ⟨a5Frame_mem_adjointGroup _, ?_, ?_, ?_⟩
  · rw [scalarWord_eq w ζ]
    exact (kronSL2_commute M (centralWord ζ)).map (a5Frame K)
  · rw [pairedWord_eq w ζ]
    exact ((kronSL2_commute M (diagonalWord ζ)).map (a5Frame K)).mul_right
      (a5Frame_commute_theta_two w _ _)
  · rw [cyclic_eq w]
    exact ((kronSL2_commute M cycleWord).map (a5Frame K)).mul_right
      (a5Frame_commute_theta_two w _ _)

theorem range_theta_two_le_normalizer (w : NativeFrame K) :
    (theta w 2).range ≤ Subgroup.normalizer ((a5Frame K).range : Set (ModGL .E7 K)) := by
  rintro _ ⟨B, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨A, rfl⟩
    refine ⟨A, ?_⟩
    rw [(a5Frame_commute_theta_two w A B).symm.eq, mul_inv_cancel_right]
  · rintro ⟨A, hA⟩
    refine ⟨A, ?_⟩
    rw [eq_mul_inv_iff_mul_eq, ← (a5Frame_commute_theta_two w A B).symm.eq] at hA
    exact mul_left_cancel hA

section Steinberg


theorem cubeCent_le_sup [IsAlgClosed K] {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) :
    cubeCent ζ hζ.pow_eq_one ≤ (cubeSL2 K).range ⊔ cubeE ζ hζ.pow_eq_one := by
  obtain ⟨w⟩ := nativeFrame_exists (K := K)
  have h3 := hζ.pow_eq_one
  intro g hg
  obtain ⟨hgG, hgs, hgp, hgc⟩ := mem_cubeCent_iff.1 hg
  have hgT : g ∈ toralCentralizer .E7 K (cubeChar ζ scalarExp) := by
    rw [mem_toralCentralizer, ← scalarWord_val ζ h3]
    exact ⟨hgG, by rw [← hgs.eq, mul_inv_cancel_right]⟩
  have hgR := toralCentralizer_scalar_le w ζ hζ hgT
  rw [← SetLike.mem_coe,
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ (range_theta_two_le_normalizer w)] at hgR
  obtain ⟨_, ⟨A, rfl⟩, _, ⟨B, rfl⟩, hAB⟩ := hgR
  dsimp only at hAB
  obtain ⟨z₁, hz₁, hB₁⟩ : ∃ z ∈ Subgroup.center SL(3, K),
      B * diagonalWord ζ = z * (diagonalWord ζ * B) := by
    have e := hgp.eq
    rw [← hAB, pairedWord_eq w ζ, frame_mul, frame_mul] at e
    exact exists_center_of_frame_eq w e
  obtain ⟨z₂, hz₂, hB₂⟩ : ∃ z ∈ Subgroup.center SL(3, K),
      B * cycleWord ^ 2 = z * (cycleWord ^ 2 * B) := by
    have e := hgc.eq
    rw [← hAB, cyclic_eq w, frame_mul, frame_mul] at e
    exact exists_center_of_frame_eq w e
  obtain ⟨a, b, z, hz, rfl⟩ := sl3_eq_center_mul hζ B hz₁ hz₂ hB₁ hB₂
  obtain ⟨m, rfl⟩ := exists_centralWord_pow hζ hz
  set e : adjointGroup .E7 K := pairedWord ζ ^ a * cyclic ^ (2 * b) with he
  have hC4 : (cycleWord (K := K) ^ 2) ^ (2 * b) = cycleWord ^ b := by
    rw [← pow_mul, show 2 * (2 * b) = 3 * b + b by ring, pow_add, pow_mul, cycleWord_pow_three,
      one_pow, one_mul]
  have he_eq : (e : ModGL .E7 K) = a5Frame K ((upperSL3 K (diagonalWord ζ) *
      lowerSL3 K (diagonalWord ζ)) ^ a * (upperSL3 K cycleWord * lowerSL3 K cycleWord) ^ (2 * b)) *
        theta w 2 (diagonalWord ζ ^ a * cycleWord ^ b) := by
    rw [he, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, pairedWord_eq w ζ, cyclic_eq w,
      frame_pow, frame_pow, frame_mul, hC4]
  have he_mem : (e : ModGL .E7 K) ∈ cubeE ζ h3 :=
    (cubeE ζ h3).mul_mem ((cubeE ζ h3).pow_mem (generators_mem_cubeE ζ h3 1) _)
      ((cubeE ζ h3).pow_mem (generators_mem_cubeE ζ h3 2) _)
  set A'' : SL(6, K) := A * ((upperSL3 K (diagonalWord ζ) * lowerSL3 K (diagonalWord ζ)) ^ a *
    (upperSL3 K cycleWord * lowerSL3 K cycleWord) ^ (2 * b))⁻¹ *
      (upperSL3 K (centralWord ζ) * lowerSL3 K (centralWord ζ)) ^ m with hA''
  have hg' : a5Frame K A * theta w 2 (centralWord ζ ^ m * (diagonalWord ζ ^ a * cycleWord ^ b)) *
      (e : ModGL .E7 K)⁻¹ = a5Frame K A'' := by
    rw [he_eq, frame_inv, frame_mul, mul_inv_cancel_right, map_pow, theta_two_centralWord w ζ h3,
      scalarWord_eq w ζ, ← map_pow, hA'']
    simp only [map_mul]
  have hA''mem : a5Frame K A'' ∈ cubeCent ζ h3 := by
    rw [← hg', hAB]
    exact (cubeCent ζ h3).mul_mem hg ((cubeCent ζ h3).inv_mem (cubeE_le_cubeCent ζ h3 he_mem))
  obtain ⟨-, -, hp', hc'⟩ := mem_cubeCent_iff.1 hA''mem
  have hXc : A'' * (upperSL3 K (diagonalWord ζ) * lowerSL3 K (diagonalWord ζ)) =
      upperSL3 K (diagonalWord ζ) * lowerSL3 K (diagonalWord ζ) * A'' := by
    have e1 := hp'.eq
    rw [pairedWord_eq w ζ, ← mul_one (a5Frame K A''), ← map_one (theta w 2), frame_mul,
      frame_mul, one_mul, mul_one] at e1
    exact a5Frame_injective hζ (mul_right_cancel e1)
  have hYc : A'' * (upperSL3 K cycleWord * lowerSL3 K cycleWord) =
      upperSL3 K cycleWord * lowerSL3 K cycleWord * A'' := by
    have e1 := hc'.eq
    rw [cyclic_eq w, ← mul_one (a5Frame K A''), ← map_one (theta w 2), frame_mul,
      frame_mul, one_mul, mul_one] at e1
    exact a5Frame_injective hζ (mul_right_cancel e1)
  obtain ⟨M, j, hMj⟩ := sl6_eq_kronSL2_mul hζ A'' hXc hYc
  have hg_eq : a5Frame K A * theta w 2 (centralWord ζ ^ m * (diagonalWord ζ ^ a * cycleWord ^ b)) =
      cubeSL2 K M * ((scalarWord ζ : ModGL .E7 K) ^ j * e) := by
    rw [← inv_mul_cancel_right (a5Frame K A * theta w 2 _) (e : ModGL .E7 K), hg', hMj, map_mul,
      map_pow, ← scalarWord_eq w ζ, mul_assoc]
    rfl
  rw [← hAB, hg_eq]
  refine mul_mem (Subgroup.mem_sup_left ⟨M, rfl⟩) (Subgroup.mem_sup_right ?_)
  exact (cubeE ζ h3).mul_mem ((cubeE ζ h3).pow_mem (generators_mem_cubeE ζ h3 0) _) he_mem

theorem cubeCent_eq_sup [IsAlgClosed K] {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) :
    cubeCent ζ hζ.pow_eq_one = (cubeSL2 K).range ⊔ cubeE ζ hζ.pow_eq_one :=
  le_antisymm (cubeCent_le_sup hζ)
    (sup_le (range_cubeSL2_le_cubeCent ζ _) (cubeE_le_cubeCent ζ _))

end Steinberg

theorem kronSL2_injective : Function.Injective (kronSL2 K) := by
  intro M M' h
  have h' := congrArg (fun A : SL(6, K) =>
    reindex e6.symm e6.symm (A : Matrix (Fin 6) (Fin 6) K)) h
  simp only [coe_kronSL2, reindex_symm, LinearEquiv.symm_apply_apply] at h'
  ext i j
  have := congrFun (congrFun h' (i, 0)) (j, 0)
  simpa [kroneckerMap_apply] using this

theorem cubeSL2_injective {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) : Function.Injective (cubeSL2 K) :=
  (a5Frame_injective hζ).comp kronSL2_injective

theorem center_sl2_eq_bot : Subgroup.center SL(2, K) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨r, hr, hzr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  rw [Fintype.card_fin] at hr
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hr1 : r = 1 := by
    have h : (r - 1) ^ 2 = 0 := by linear_combination hr - (r - 1) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hzr, hr1, map_one]
  rfl

theorem range_cubeSL2_inf_cubeE {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) :
    (cubeSL2 K).range ⊓ cubeE ζ hζ.pow_eq_one = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨M, rfl⟩, hM⟩
  have hc : M ∈ Subgroup.center SL(2, K) := by
    rw [Subgroup.mem_center_iff]
    intro M'
    apply cubeSL2_injective hζ
    rw [map_mul, map_mul]
    have := (range_cubeSL2_le_cubeCent ζ hζ.pow_eq_one ⟨M', rfl⟩).2
    exact (Subgroup.mem_centralizer_iff.1 this _ hM).symm
  rw [center_sl2_eq_bot, Subgroup.mem_bot] at hc
  rw [hc, map_one]
  exact Subgroup.one_mem _

end CFSG.LieType.Chevalley.E7Three.Centralizer
