module

public import CFSG.LieType.Chevalley.E7Three.Centralizer
public import CFSG.LieType.Chevalley.E7Three.HeisenbergPair

public noncomputable section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.Centralizer

open Matrix CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KA5L CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.WeakCT
  CFSG.LieType.Chevalley.E7Three.Weyl CFSG.LieType.Chevalley.E7Three.Cube
  CFSG.LieType.Chevalley.E7Three.PauliWords CFSG.LieType.Chevalley.E7Three.Product
  CFSG.LieType.Chevalley.E7Three.Frames CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Chevalley.E7Three.CentralizerMatrix CFSG.AGLEmbedding

open scoped MatrixGroups Kronecker

variable {K : Type} [Field K] [CharP K 2]

theorem exists_frame_of_commute_scalar [IsAlgClosed K]
    (w : NativeFrame K) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) {g : ModGL .E7 K}
    (hgG : g ∈ adjointGroup .E7 K) (hgs : g * scalarWord ζ = scalarWord ζ * g) :
    ∃ (A : SL(6, K)) (B : SL(3, K)), a5Frame K A * theta w 2 B = g := by
  have hgT : g ∈ toralCentralizer .E7 K (cubeChar ζ scalarExp) := by
    rw [mem_toralCentralizer, ← scalarWord_val ζ hζ.pow_eq_one]
    exact ⟨hgG, by rw [← hgs, mul_inv_cancel_right]⟩
  have hgR := toralCentralizer_scalar_le w ζ hζ hgT
  rw [← SetLike.mem_coe,
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ (range_theta_two_le_normalizer w)] at hgR
  obtain ⟨_, ⟨A, rfl⟩, _, ⟨B, rfl⟩, hAB⟩ := hgR
  exact ⟨A, B, hAB⟩

theorem exists_pow_of_frame_eq_one (w : NativeFrame K) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3)
    {A : SL(6, K)} {B : SL(3, K)} (h : a5Frame K A * theta w 2 B = 1) :
    ∃ m : ℕ, B = centralWord ζ ^ m ∧
      A * (upperSL3 K (centralWord ζ) * lowerSL3 K (centralWord ζ)) ^ m = 1 := by
  have h' : a5Frame K A * theta w 2 B = a5Frame K 1 * theta w 2 1 := by
    rw [h, map_one, map_one, one_mul]
  obtain ⟨z, hz, hB⟩ := exists_center_of_frame_eq w h'
  rw [mul_one] at hB
  subst hB
  obtain ⟨m, rfl⟩ := exists_centralWord_pow hζ hz
  refine ⟨m, rfl, a5Frame_injective hζ ?_⟩
  rw [map_mul, map_one, map_pow, ← scalarWord_eq w ζ, ← theta_two_centralWord w ζ hζ.pow_eq_one,
    ← map_pow, h]

theorem exists_frame_commutator (w : NativeFrame K) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3)
    {A₁ A₂ : SL(6, K)} {B₁ B₂ : SL(3, K)}
    (h : a5Frame K A₁ * theta w 2 B₁ * (a5Frame K A₂ * theta w 2 B₂) =
      a5Frame K A₂ * theta w 2 B₂ * (a5Frame K A₁ * theta w 2 B₁)) :
    ∃ m : ℕ, B₁ * B₂ = centralWord ζ ^ m * (B₂ * B₁) ∧
      A₁ * A₂ * (upperSL3 K (centralWord ζ) * lowerSL3 K (centralWord ζ)) ^ m = A₂ * A₁ := by
  rw [frame_mul, frame_mul] at h
  have h1 : a5Frame K (A₁ * A₂ * (A₂ * A₁)⁻¹) * theta w 2 (B₁ * B₂ * (B₂ * B₁)⁻¹) = 1 := by
    rw [← frame_mul, ← frame_inv, h, mul_inv_cancel]
  obtain ⟨m, hB, hA⟩ := exists_pow_of_frame_eq_one w hζ h1
  have hc : centralWord ζ ^ m * (B₂ * B₁) = (B₂ * B₁) * centralWord ζ ^ m :=
    ((centralWord_commute ζ hζ.pow_eq_one (B₂ * B₁)).pow_left m).eq
  refine ⟨m, ?_, ?_⟩
  · rw [← hB, inv_mul_cancel_right]
  · have hs : Commute (A₂ * A₁)
        ((upperSL3 K (centralWord ζ) * lowerSL3 K (centralWord ζ)) ^ m) := by
      refine Commute.pow_right ?_ m
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul (A₂ * A₁),
        Matrix.SpecialLinearGroup.coe_mul _ (A₂ * A₁), coe_scalar6 hζ.pow_eq_one, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    calc A₁ * A₂ * (upperSL3 K (centralWord ζ) * lowerSL3 K (centralWord ζ)) ^ m =
        A₁ * A₂ * (A₂ * A₁)⁻¹ * (upperSL3 K (centralWord ζ) * lowerSL3 K (centralWord ζ)) ^ m *
          (A₂ * A₁) := by
          rw [mul_assoc (A₁ * A₂ * (A₂ * A₁)⁻¹), ← hs.eq]; group
      _ = A₂ * A₁ := by rw [hA, one_mul]

theorem theta_two_diag_mem_torusGroup [IsAlgClosed K] (w : NativeFrame K) (B : SL(3, K))
    (hB : ∀ i j, i ≠ j → (B : Matrix (Fin 3) (Fin 3) K) i j = 0) :
    theta w 2 B ∈ torusGroup .E7 K := by
  have hdiag : ∀ i, (B : Matrix (Fin 3) (Fin 3) K) i i ≠ 0 := by
    intro i h0
    have hdet := B.2
    rw [Matrix.det_fin_three] at hdet
    fin_cases i <;> simp_all [hB 0 1 (by decide), hB 0 2 (by decide), hB 1 0 (by decide),
      hB 1 2 (by decide), hB 2 0 (by decide), hB 2 1 (by decide)]
  set d₀ : Kˣ := Units.mk0 _ (hdiag 0)
  set d₁ : Kˣ := Units.mk0 _ (hdiag 1)
  have hdet : (B : Matrix (Fin 3) (Fin 3) K) 0 0 * (B : Matrix (Fin 3) (Fin 3) K) 1 1 *
      (B : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    have h := B.2
    rw [Matrix.det_fin_three] at h
    simpa [hB 0 1 (by decide), hB 0 2 (by decide), hB 1 0 (by decide), hB 1 2 (by decide),
      hB 2 0 (by decide), hB 2 1 (by decide)] using h
  have hBeq : B = blockSL K 3 2 0 (by omega) (HSL d₀) * blockSL K 3 2 1 (by omega) (HSL (d₀ * d₁)) := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL_three_zero, coe_blockSL_three_one]
    have h2 : (B : Matrix (Fin 3) (Fin 3) K) 2 2 =
        ((B : Matrix (Fin 3) (Fin 3) K) 0 0 * (B : Matrix (Fin 3) (Fin 3) K) 1 1)⁻¹ := by
      exact eq_inv_of_mul_eq_one_right hdet
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [HSL, d₀, d₁, Matrix.mul_apply, Fin.sum_univ_three, hB 0 1 (by decide),
        hB 0 2 (by decide), hB 1 0 (by decide), hB 1 2 (by decide), hB 2 0 (by decide),
        hB 2 1 (by decide), h2, mul_inv, hdiag 0]
  rw [hBeq, map_mul]
  refine mul_mem ?_ ?_
  · have h0 := DFunLike.congr_fun (w.block0 2) (HSL d₀)
    simp only [MonoidHom.comp_apply] at h0
    change (w.rho 2) (conjDiag3Hom (w.diag 2) (blockSL K 3 2 0 (by omega) (HSL d₀))) ∈ _
    rw [h0]
    change rootSL2 .E7 K (e7ExtVec none) (HSL d₀) ∈ _
    rw [rootSL2_HSL_eq isRoot_e7ExtVec_none]
    exact rootDiagUnit_mem_torusGroup _
  · change theta w 2 (diagonalWord (d₀ * d₁)) ∈ _
    rw [Images.theta_diagonal_two w]
    exact Subgroup.subset_closure ⟨(_, _), rfl⟩

theorem exists_sl_conj_diag_of_commute [IsAlgClosed K] {n ι : Type} [Fintype n] [DecidableEq n]
    [Finite ι] {p : ℕ} [NeZero p] {η : K} (hη : IsPrimitiveRoot η p)
    (f : ι → Matrix.SpecialLinearGroup n K) (hcomm : ∀ i j, f i * f j = f j * f i)
    (hpow : ∀ i, f i ^ p = 1) :
    ∃ P : Matrix.SpecialLinearGroup n K, ∀ i a b, a ≠ b →
      ((P * f i * P⁻¹ : Matrix.SpecialLinearGroup n K) : Matrix n n K) a b = 0 := by
  classical
  obtain ⟨b, μ, hb⟩ := CFSG.RankThree.PartOne.exists_basis_common_eigenvectors_of_pow_eq_one hη
    (fun i => Matrix.toLinAlgEquiv' (f i : Matrix n n K))
    (fun i j => by
      change Commute (Matrix.toLinAlgEquiv' (f i : Matrix n n K))
        (Matrix.toLinAlgEquiv' (f j : Matrix n n K))
      refine Commute.map ?_ _
      change (f i : Matrix n n K) * f j = f j * f i
      rw [← Matrix.SpecialLinearGroup.coe_mul, hcomm, Matrix.SpecialLinearGroup.coe_mul])
    (fun i => by
      change Matrix.toLinAlgEquiv' (f i : Matrix n n K) ^ p = 1
      rw [← map_pow, ← Matrix.SpecialLinearGroup.coe_pow, hpow,
        Matrix.SpecialLinearGroup.coe_one, map_one])
  let e : Fin (Module.finrank K (n → K)) ≃ n :=
    (finCongr (Module.finrank_fintype_fun_eq_card K)).trans (Fintype.equivFin n).symm
  let b' : Module.Basis n K (n → K) := b.reindex e
  let Q : Matrix n n K := (Pi.basisFun K n).toMatrix b'
  have hQ : ∀ x y, Q x y = b' y x := by
    intro x y
    simp [Q, Module.Basis.toMatrix_apply]
  have hQu : IsUnit Q.det := by
    have := Module.Basis.invertibleToMatrix (Pi.basisFun K n) b'
    exact Matrix.isUnit_det_of_invertible Q
  obtain ⟨P, hP⟩ := HeisenbergPair.exists_sl_conj_eq hQu
  refine ⟨P, fun i a c hac => ?_⟩
  have hfQ : (f i : Matrix n n K) * Q = Q * diagonal fun y => μ i (e.symm y) := by
    ext x y
    have h := congrFun (hb i (e.symm y)) x
    have hb'y : b' y = b (e.symm y) := by simp [b', Module.Basis.reindex_apply]
    rw [Matrix.mul_diagonal, hQ, hb'y]
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [mul_comm, ← h]
    simp only [Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply, Matrix.mul_apply, Matrix.mulVec,
      dotProduct, hQ, hb'y]
  rw [hP, Matrix.mul_assoc, hfQ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQu, Matrix.one_mul,
    Matrix.diagonal_apply_ne _ hac]

theorem scalar6_pow_three {ζ : Kˣ} (hζ : ζ ^ 3 = 1) :
    (upperSL3 K (centralWord ζ) * lowerSL3 K (centralWord ζ)) ^ 3 = 1 := by
  have h3 : (ζ : K) ^ 3 = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg (fun u : Kˣ => (u : K)) hζ
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_scalar6 hζ, smul_pow, one_pow, h3, one_smul,
    Matrix.SpecialLinearGroup.coe_one]

theorem scalar6_pow_eq_one {ζ : Kˣ} (hζ : ζ ^ 3 = 1) {m : ℕ} (h : centralWord ζ ^ m = 1) :
    (upperSL3 K (centralWord ζ) * lowerSL3 K (centralWord ζ)) ^ m = 1 := by
  have hm : (ζ : K) ^ m = 1 := by
    have := congrArg (fun g : SL(3, K) => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_pow, centralWord_val ζ hζ, ← map_pow,
      Matrix.SpecialLinearGroup.coe_one] at this
    simpa [Matrix.scalar_apply] using this
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_scalar6 hζ, smul_pow, one_pow, hm, one_smul,
    Matrix.SpecialLinearGroup.coe_one]

theorem frame_pow_nine_of_pow_three (w : NativeFrame K) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3)
    {A : SL(6, K)} {B : SL(3, K)} (h : (a5Frame K A * theta w 2 B) ^ 3 = 1) :
    A ^ 9 = 1 ∧ B ^ 9 = 1 := by
  rw [frame_pow] at h
  obtain ⟨m, hB, hA⟩ := exists_pow_of_frame_eq_one w hζ h
  have h3 := hζ.pow_eq_one
  constructor
  · have hA' : A ^ 3 = ((upperSL3 K (centralWord ζ) * lowerSL3 K (centralWord ζ)) ^ m)⁻¹ :=
      eq_inv_of_mul_eq_one_left hA
    rw [show 9 = 3 * 3 by rfl, pow_mul, hA', inv_pow, ← pow_mul, mul_comm, pow_mul,
      scalar6_pow_three h3, one_pow, inv_one]
  · rw [show 9 = 3 * 3 by rfl, pow_mul, hB, ← pow_mul, mul_comm, pow_mul,
      centralWord_pow_three ζ h3, one_pow]

theorem exists_conj_torus_of_commute [IsAlgClosed K] (w : NativeFrame K) {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ 3) {E : Subgroup (ModGL .E7 K)} [Finite E]
    (A : ModGL .E7 K → SL(6, K)) (B : ModGL .E7 K → SL(3, K))
    (hAB : ∀ x ∈ E, a5Frame K (A x) * theta w 2 (B x) = x)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hB : ∀ x ∈ E, ∀ y ∈ E, B x * B y = B y * B x) :
    ∃ g ∈ adjointGroup .E7 K, ∀ x ∈ E, g * x * g⁻¹ ∈ torusGroup .E7 K := by
  classical
  have h3 := hζ.pow_eq_one
  have hA : ∀ x ∈ E, ∀ y ∈ E, A x * A y = A y * A x := by
    intro x hx y hy
    have hxy := hcomm x hx y hy
    rw [← hAB x hx, ← hAB y hy] at hxy
    obtain ⟨m, hBm, hAm⟩ := exists_frame_commutator w hζ hxy
    have hm : centralWord ζ ^ m = 1 := by
      rw [hB x hx y hy] at hBm
      exact (mul_eq_right.1 hBm.symm)
    rwa [scalar6_pow_eq_one h3 hm, mul_one] at hAm
  have h9 : ∀ x ∈ E, A x ^ 9 = 1 ∧ B x ^ 9 = 1 := by
    intro x hx
    apply frame_pow_nine_of_pow_three w hζ
    rw [hAB x hx]
    exact hexp x hx
  have : NeZero (9 : K) := ⟨by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have : (9 : K) = 1 + 4 * 2 := by norm_num
    rw [this, h2, mul_zero, add_zero]
    exact one_ne_zero⟩
  obtain ⟨η, hη⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K 9
  obtain ⟨P, hP⟩ := exists_sl_conj_diag_of_commute hη (fun x : E => A x)
    (fun x y => hA x x.2 y y.2) (fun x => (h9 x x.2).1)
  obtain ⟨Q, hQ⟩ := exists_sl_conj_diag_of_commute hη (fun x : E => B x)
    (fun x y => hB x x.2 y y.2) (fun x => (h9 x x.2).2)
  refine ⟨a5Frame K P * theta w 2 Q, (adjointGroup .E7 K).mul_mem (a5Frame_mem_adjointGroup P)
    (theta_mem_adjointGroup w 2 Q), fun x hx => ?_⟩
  rw [← hAB x hx, frame_inv, frame_mul, frame_mul]
  exact mul_mem (a5Frame_diag_mem_torusGroup _ (hP ⟨x, hx⟩))
    (theta_two_diag_mem_torusGroup w _ (hQ ⟨x, hx⟩))

@[expose] def flipWord : SL(3, K) :=
  ⟨(!![1, 0, 0; 0, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K), by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    rw [Matrix.det_fin_three]
    simp
    linear_combination -h2⟩

theorem coe_flipWord :
    ((flipWord : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      (!![1, 0, 0; 0, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K) := rfl

theorem flipWord_mul_self : (flipWord : SL(3, K)) * flipWord = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_flipWord, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem flipWord_inv : (flipWord : SL(3, K))⁻¹ = flipWord :=
  inv_eq_of_mul_eq_one_left flipWord_mul_self

theorem diagonalWord_pow_three {ζ : Kˣ} (hζ : ζ ^ 3 = 1) : diagonalWord ζ ^ 3 = 1 := by
  have h3 : (ζ : K) ^ 3 = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg (fun u : Kˣ => (u : K)) hζ
  have h6 : (ζ : K) ^ 6 = 1 := by rw [show 6 = 3 * 2 by rfl, pow_mul, h3, one_pow]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, diagonalWord_val ζ hζ, heisXMat_eq_diagonal,
    Matrix.diagonal_pow, Matrix.SpecialLinearGroup.coe_one, ← Matrix.diagonal_one]
  congr 1
  funext j
  fin_cases j <;> simp [← pow_mul, h3, h6]

theorem flipWord_conj_diagonalWord {ζ : Kˣ} (hζ : ζ ^ 3 = 1) :
    flipWord * diagonalWord ζ * flipWord⁻¹ = diagonalWord ζ ^ 2 := by
  have h3 : (ζ : K) ^ 3 = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg (fun u : Kˣ => (u : K)) hζ
  have h4 : (ζ : K) ^ 4 = ζ := by rw [pow_succ, h3, one_mul]
  rw [flipWord_inv]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_pow, coe_flipWord, diagonalWord_val ζ hζ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisXMat, Matrix.mul_apply, Fin.sum_univ_three, pow_two] <;>
    first
    | linear_combination (ζ : K) * h3
    | linear_combination -(ζ : K) * h3

theorem flipWord_conj_cycleWord :
    flipWord * cycleWord * flipWord⁻¹ = (cycleWord (K := K)) ^ 2 := by
  rw [flipWord_inv]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_pow, coe_flipWord, cycleWord_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heisYMat, Matrix.mul_apply, Fin.sum_univ_three, pow_two]

@[expose] def e3 : Fin 1 × Fin 3 ≃ Fin 3 := finProdFinEquiv.trans (finCongr (by norm_num))

theorem reindex_e3_one_kronecker (M : Matrix (Fin 3) (Fin 3) K) :
    reindex e3 e3 ((1 : Matrix (Fin 1) (Fin 1) K) ⊗ₖ M) = M := by
  ext a b
  have he : ∀ c : Fin 3, e3.symm c = (0, c) := by
    intro c
    apply e3.injective
    rw [Equiv.apply_symm_apply]
    apply Fin.ext
    change (c : ℕ) = ((finProdFinEquiv ((0 : Fin 1), c) : Fin (1 * 3)) : ℕ)
    rw [finProdFinEquiv_apply_val]
    simp
  have ha := he a
  have hb := he b
  rw [reindex_apply, submatrix_apply, ha, hb, kroneckerMap_apply, Matrix.one_apply_eq, one_mul]

theorem shift3_eq_heisYMat : HeisenbergPair.shift3 = (heisYMat : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [HeisenbergPair.shift3, heisYMat] <;> decide

theorem diagonal_pow_eq_diagonalWord {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (m : ℕ) :
    (diagonal fun j : Fin 3 => ((ζ : K) ^ m) ^ (j : ℕ)) =
      ((diagonalWord ζ ^ m : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) := by
  rw [Matrix.SpecialLinearGroup.coe_pow, diagonalWord_val ζ hζ, heisXMat_eq_diagonal,
    Matrix.diagonal_pow]
  congr 1
  funext j
  fin_cases j <;> simp [← pow_mul, mul_comm]

theorem exists_centralWord_smul {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) {c : K} (hc : c ^ 3 = 1)
    (M : SL(3, K)) :
    ∃ a : ℕ, c • (M : Matrix (Fin 3) (Fin 3) K) = ((centralWord ζ ^ a * M : SL(3, K)) :
      Matrix (Fin 3) (Fin 3) K) := by
  obtain ⟨a, -, ha⟩ := (IsPrimitiveRoot.coe_units_iff.2 hζ).eq_pow_of_pow_eq_one hc
  refine ⟨a, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow,
    centralWord_val ζ hζ.pow_eq_one, ← map_pow, ha, Matrix.scalar_apply, ← smul_one_eq_diagonal,
    Matrix.smul_mul, Matrix.one_mul]

theorem exists_scalar6_smul {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) {c : K} (hc : c ^ 3 = 1)
    (M : SL(6, K)) :
    ∃ a : ℕ, c • (M : Matrix (Fin 6) (Fin 6) K) =
      (((upperSL3 K (centralWord ζ) * lowerSL3 K (centralWord ζ)) ^ a * M : SL(6, K)) :
        Matrix (Fin 6) (Fin 6) K) := by
  obtain ⟨a, -, ha⟩ := (IsPrimitiveRoot.coe_units_iff.2 hζ).eq_pow_of_pow_eq_one hc
  refine ⟨a, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow,
    coe_scalar6 hζ.pow_eq_one, smul_pow, one_pow, ha, Matrix.smul_mul, Matrix.one_mul]

theorem pow_three_eq_one_of_pow_six {c : K} (hc : c ^ 6 = 1) : c ^ 3 = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h : (c ^ 3 - 1) ^ 2 = 0 := by linear_combination hc - (c ^ 3) * h2 + h2
  exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h)

variable (K) in
@[expose] def diagSL3 : SL(3, K) →* SL(6, K) where
  toFun W := ⟨reindexAlgEquiv K K e6 ((1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ
      (W : Matrix (Fin 3) (Fin 3) K)), by
    rw [det_reindexAlgEquiv, det_kronecker, det_one, W.2, one_pow, one_pow, mul_one]⟩
  map_one' := Subtype.ext (by
    simp only [Matrix.SpecialLinearGroup.coe_one, one_kronecker_one, map_one])
  map_mul' W W' := Subtype.ext (by
    change reindexAlgEquiv K K e6 ((1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ
        ((W * W' : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) =
      reindexAlgEquiv K K e6 ((1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ (W : Matrix (Fin 3) (Fin 3) K)) *
        reindexAlgEquiv K K e6 ((1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ (W' : Matrix (Fin 3) (Fin 3) K))
    rw [← map_mul, ← mul_kronecker_mul, Matrix.one_mul]
    rfl)

theorem coe_diagSL3 (W : SL(3, K)) : ((diagSL3 K W : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) =
    reindex e6 e6 ((1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ (W : Matrix (Fin 3) (Fin 3) K)) := rfl

theorem upper_mul_lower_eq_diagSL3 (W : SL(3, K)) :
    upperSL3 K W * lowerSL3 K W = diagSL3 K W :=
  Subtype.ext (coe_upper_mul_lower W)

theorem frame_cubes (w : NativeFrame K) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) {A : SL(6, K)}
    {B : SL(3, K)} (h : (a5Frame K A * theta w 2 B) ^ 3 = 1) :
    ∃ m : ℕ, (B : Matrix (Fin 3) (Fin 3) K) ^ 3 = ((ζ : K) ^ m) • 1 ∧
      (A : Matrix (Fin 6) (Fin 6) K) ^ 3 = ((ζ : K) ^ (2 * m)) • 1 := by
  have h3 := hζ.pow_eq_one
  have h3K : (ζ : K) ^ 3 = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg (fun u : Kˣ => (u : K)) h3
  rw [frame_pow] at h
  obtain ⟨m, hB, hA⟩ := exists_pow_of_frame_eq_one w hζ h
  refine ⟨m, ?_, ?_⟩
  · rw [← Matrix.SpecialLinearGroup.coe_pow, hB, Matrix.SpecialLinearGroup.coe_pow,
      centralWord_val ζ h3, ← map_pow, Matrix.scalar_apply, smul_one_eq_diagonal]
  · have hA' := congrArg (fun g : SL(6, K) => (g : Matrix (Fin 6) (Fin 6) K)) hA
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow,
      coe_scalar6 h3, Matrix.SpecialLinearGroup.coe_one, smul_pow, one_pow] at hA'
    rw [Matrix.mul_smul, Matrix.mul_one] at hA'
    have e : ((ζ : K) ^ (2 * m)) * ((ζ : K) ^ m) = 1 := by
      rw [← pow_add, show 2 * m + m = 3 * m by ring, pow_mul, h3K, one_pow]
    calc (A : Matrix (Fin 6) (Fin 6) K) ^ 3 =
        ((ζ : K) ^ (2 * m)) • (((ζ : K) ^ m) • (A : Matrix (Fin 6) (Fin 6) K) ^ 3) := by
          rw [smul_smul, e, one_smul]
      _ = ((ζ : K) ^ (2 * m)) • 1 := by rw [hA']

theorem cubeE_le_of_mem {ζ : Kˣ} (hζ : ζ ^ 3 = 1) {H : Subgroup (ModGL .E7 K)}
    (hs : (scalarWord ζ : ModGL .E7 K) ∈ H) (hp : (pairedWord ζ : ModGL .E7 K) ∈ H)
    (hc : (cyclic (K := K) : ModGL .E7 K) ∈ H) : cubeE ζ hζ ≤ H := by
  intro z hz
  obtain ⟨f, rfl⟩ := mem_cubeE.1 hz
  rw [cubeHom_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_pow]
  exact H.mul_mem (H.mul_mem (H.pow_mem hs _) (H.pow_mem hp _)) (H.pow_mem hc _)

theorem frame_conj (w : NativeFrame K) (P A : SL(6, K)) (Q B : SL(3, K)) :
    a5Frame K P * theta w 2 Q * (a5Frame K A * theta w 2 B) * (a5Frame K P * theta w 2 Q)⁻¹ =
      a5Frame K (P * A * P⁻¹) * theta w 2 (Q * B * Q⁻¹) := by
  rw [frame_inv, frame_mul, frame_mul]

theorem scalarWord_commute_frame (w : NativeFrame K) {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (P : SL(6, K))
    (Q : SL(3, K)) :
    (scalarWord ζ : ModGL .E7 K) * (a5Frame K P * theta w 2 Q) =
      a5Frame K P * theta w 2 Q * scalarWord ζ := by
  have hc : upperSL3 K (centralWord ζ) * lowerSL3 K (centralWord ζ) * P =
      P * (upperSL3 K (centralWord ζ) * lowerSL3 K (centralWord ζ)) := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul _ P, Matrix.SpecialLinearGroup.coe_mul P,
      coe_scalar6 hζ, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  rw [scalarWord_eq w ζ, ← mul_assoc, ← map_mul, hc, map_mul, mul_assoc, mul_assoc,
    (a5Frame_commute_theta_two w _ Q).eq]

theorem mem_map_conj_mul {E : Subgroup (ModGL .E7 K)} {f g z : ModGL .E7 K}
    (hz : z ∈ E.map (MulAut.conj g).toMonoidHom) :
    f * z * f⁻¹ ∈ E.map (MulAut.conj (f * g)).toMonoidHom := by
  obtain ⟨e, he, rfl⟩ := hz
  refine ⟨e, he, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, _root_.mul_inv_rev]
  group

theorem frame_mem_of_scalar_mem (w : NativeFrame K) {ζ : Kˣ} (hζ : ζ ^ 3 = 1)
    {H : Subgroup (ModGL .E7 K)} (hs : (scalarWord ζ : ModGL .E7 K) ∈ H) {D : SL(6, K)}
    {X : SL(3, K)} {a a' : ℕ}
    (h : a5Frame K ((upperSL3 K (centralWord ζ) * lowerSL3 K (centralWord ζ)) ^ a' * D) *
      theta w 2 (centralWord ζ ^ a * X) ∈ H) : a5Frame K D * theta w 2 X ∈ H := by
  have hc : (scalarWord ζ : ModGL .E7 K) ^ a * a5Frame K D = a5Frame K D * scalarWord ζ ^ a := by
    have h1 : Commute (scalarWord ζ : ModGL .E7 K) (a5Frame K D * theta w 2 1) :=
      scalarWord_commute_frame w hζ D 1
    have := h1.pow_left a
    rw [map_one, mul_one] at this
    exact this.eq
  have e : a5Frame K ((upperSL3 K (centralWord ζ) * lowerSL3 K (centralWord ζ)) ^ a' * D) *
      theta w 2 (centralWord ζ ^ a * X) =
        (scalarWord ζ : ModGL .E7 K) ^ a' * scalarWord ζ ^ a * (a5Frame K D * theta w 2 X) := by
    rw [map_mul, map_mul, map_pow, map_pow, ← scalarWord_eq w ζ, theta_two_centralWord w ζ hζ,
      mul_assoc, ← mul_assoc (a5Frame K D), ← hc]
    group
  rw [e] at h
  have := H.mul_mem (H.inv_mem (H.mul_mem (H.pow_mem hs a') (H.pow_mem hs a))) h
  rwa [← mul_assoc, inv_mul_cancel, one_mul] at this

theorem exists_conj_cubeE_le_of_heis [IsAlgClosed K] (w : NativeFrame K) {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ 3) {E : Subgroup (ModGL .E7 K)}
    (hs : (scalarWord ζ : ModGL .E7 K) ∈ E) {A₁ A₂ : SL(6, K)} {B₁ B₂ : SL(3, K)}
    (hx : a5Frame K A₁ * theta w 2 B₁ ∈ E) (hy : a5Frame K A₂ * theta w 2 B₂ ∈ E)
    (hx3 : (a5Frame K A₁ * theta w 2 B₁) ^ 3 = 1) (hy3 : (a5Frame K A₂ * theta w 2 B₂) ^ 3 = 1)
    {m : ℕ} (hm : m % 3 ≠ 0) (hB : B₁ * B₂ = centralWord ζ ^ m * (B₂ * B₁))
    (hA : A₁ * A₂ * (upperSL3 K (centralWord ζ) * lowerSL3 K (centralWord ζ)) ^ m = A₂ * A₁) :
    ∃ g ∈ adjointGroup .E7 K, cubeE ζ hζ.pow_eq_one ≤ E.map (MulAut.conj g).toMonoidHom := by
  classical
  have h3 := hζ.pow_eq_one
  have hζK : IsPrimitiveRoot (ζ : K) 3 := IsPrimitiveRoot.coe_units_iff.2 hζ
  have h3K : (ζ : K) ^ 3 = 1 := hζK.pow_eq_one
  have h3ne : (3 : K) ≠ 0 := by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    rw [show (3 : K) = 1 + 2 by norm_num, h2, add_zero]
    exact one_ne_zero
  have hcop : Nat.Coprime m 3 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three, Nat.dvd_iff_mod_eq_zero]
    exact hm
  have hω₃ : IsPrimitiveRoot ((ζ : K) ^ m) 3 := hζK.pow_of_coprime m hcop
  have hω₆ : IsPrimitiveRoot ((ζ : K) ^ (2 * m)) 3 :=
    hζK.pow_of_coprime (2 * m) (Nat.coprime_mul_iff_left.2 ⟨by norm_num, hcop⟩)
  have hBmat : (B₁ : Matrix (Fin 3) (Fin 3) K) * B₂ =
      ((ζ : K) ^ m) • ((B₂ : Matrix (Fin 3) (Fin 3) K) * B₁) := by
    have e := congrArg (fun g : SL(3, K) => (g : Matrix (Fin 3) (Fin 3) K)) hB
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow,
      centralWord_val ζ h3, Matrix.scalar_apply, ← smul_one_eq_diagonal, smul_pow, one_pow,
      Matrix.smul_mul, Matrix.one_mul] at e
    exact e
  have hAmat : (A₁ : Matrix (Fin 6) (Fin 6) K) * A₂ =
      ((ζ : K) ^ (2 * m)) • ((A₂ : Matrix (Fin 6) (Fin 6) K) * A₁) := by
    have e := congrArg (fun g : SL(6, K) => (g : Matrix (Fin 6) (Fin 6) K)) hA
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow,
      coe_scalar6 h3, smul_pow, one_pow, Matrix.mul_smul, Matrix.mul_one] at e
    rw [← e, smul_smul, ← pow_add, show 2 * m + m = 3 * m by ring, pow_mul, h3K, one_pow,
      one_smul]
  obtain ⟨m₁, hB₁3, hA₁3⟩ := frame_cubes w hζ hx3
  obtain ⟨m₂, hB₂3, hA₂3⟩ := frame_cubes w hζ hy3
  have hpow0 : ∀ k : ℕ, (ζ : K) ^ k ≠ 0 := fun k => pow_ne_zero k ζ.ne_zero
  obtain ⟨Q, c, d, -, -, hQ1, hQ2⟩ := HeisenbergPair.exists_sl_conj_heis e3 hω₃ h3ne B₁ B₂ hBmat
    (hpow0 m₁) (hpow0 m₂) hB₁3 hB₂3
  obtain ⟨P, c', d', -, -, hP1, hP2⟩ := HeisenbergPair.exists_sl_conj_heis e6 hω₆ h3ne A₁ A₂ hAmat
    (hpow0 (2 * m₁)) (hpow0 (2 * m₂)) hA₁3 hA₂3
  rw [reindex_e3_one_kronecker, diagonal_pow_eq_diagonalWord h3 m] at hQ1
  rw [reindex_e3_one_kronecker, shift3_eq_heisYMat, ← cycleWord_val] at hQ2
  rw [diagonal_pow_eq_diagonalWord h3 (2 * m), ← coe_diagSL3] at hP1
  rw [shift3_eq_heisYMat, ← cycleWord_val, ← coe_diagSL3] at hP2
  have hdet3 : ∀ {c : K} {M N : SL(3, K)},
      (M : Matrix (Fin 3) (Fin 3) K) = c • (N : Matrix (Fin 3) (Fin 3) K) → c ^ 3 = 1 := by
    intro c M N h
    have e := congrArg Matrix.det h
    rw [M.2, Matrix.det_smul, N.2, Fintype.card_fin, mul_one] at e
    exact e.symm
  have hdet6 : ∀ {c : K} {M N : SL(6, K)},
      (M : Matrix (Fin 6) (Fin 6) K) = c • (N : Matrix (Fin 6) (Fin 6) K) → c ^ 3 = 1 := by
    intro c M N h
    have e := congrArg Matrix.det h
    rw [M.2, Matrix.det_smul, N.2, Fintype.card_fin, mul_one] at e
    exact pow_three_eq_one_of_pow_six e.symm
  obtain ⟨a, ha⟩ := exists_centralWord_smul hζ (hdet3 hQ1) (diagonalWord ζ ^ m)
  obtain ⟨b, hb⟩ := exists_centralWord_smul hζ (hdet3 hQ2) cycleWord
  obtain ⟨a', ha'⟩ := exists_scalar6_smul hζ (hdet6 hP1) (diagSL3 K (diagonalWord ζ ^ (2 * m)))
  obtain ⟨b', hb'⟩ := exists_scalar6_smul hζ (hdet6 hP2) (diagSL3 K cycleWord)
  have eQ1 : Q * B₁ * Q⁻¹ = centralWord ζ ^ a * diagonalWord ζ ^ m := Subtype.ext (hQ1.trans ha)
  have eQ2 : Q * B₂ * Q⁻¹ = centralWord ζ ^ b * cycleWord := Subtype.ext (hQ2.trans hb)
  have eP1 : P * A₁ * P⁻¹ = (upperSL3 K (centralWord ζ) * lowerSL3 K (centralWord ζ)) ^ a' *
      diagSL3 K (diagonalWord ζ ^ (2 * m)) := Subtype.ext (hP1.trans ha')
  have eP2 : P * A₂ * P⁻¹ = (upperSL3 K (centralWord ζ) * lowerSL3 K (centralWord ζ)) ^ b' *
      diagSL3 K cycleWord := Subtype.ext (hP2.trans hb')
  set g₀ : ModGL .E7 K := a5Frame K P * theta w 2 Q with hg₀
  have hg₀G : g₀ ∈ adjointGroup .E7 K :=
    (adjointGroup .E7 K).mul_mem (a5Frame_mem_adjointGroup P) (theta_mem_adjointGroup w 2 Q)
  set H := E.map (MulAut.conj g₀).toMonoidHom with hH
  have hsH : (scalarWord ζ : ModGL .E7 K) ∈ H := by
    refine ⟨_, hs, ?_⟩
    change g₀ * scalarWord ζ * g₀⁻¹ = scalarWord ζ
    rw [hg₀, ← scalarWord_commute_frame w h3 P Q, mul_inv_cancel_right]
  have hx₀ : a5Frame K (diagSL3 K (diagonalWord ζ ^ (2 * m))) * theta w 2 (diagonalWord ζ ^ m) ∈ H := by
    refine frame_mem_of_scalar_mem w h3 hsH (a := a) (a' := a') ?_
    refine ⟨_, hx, ?_⟩
    change g₀ * (a5Frame K A₁ * theta w 2 B₁) * g₀⁻¹ = _
    rw [hg₀, frame_conj, eP1, eQ1]
  have hy₀ : a5Frame K (diagSL3 K cycleWord) * theta w 2 cycleWord ∈ H := by
    refine frame_mem_of_scalar_mem w h3 hsH (a := b) (a' := b') ?_
    refine ⟨_, hy, ?_⟩
    change g₀ * (a5Frame K A₂ * theta w 2 B₂) * g₀⁻¹ = _
    rw [hg₀, frame_conj, eP2, eQ2]
  have hX3 := diagonalWord_pow_three (K := K) h3
  have hY3 := cycleWord_pow_three (K := K)
  have hp : (pairedWord ζ : ModGL .E7 K) = a5Frame K (diagSL3 K (diagonalWord ζ)) *
      theta w 2 (diagonalWord ζ) := by
    rw [pairedWord_eq w ζ, upper_mul_lower_eq_diagSL3]
  have hc : (cyclic (K := K) : ModGL .E7 K) = a5Frame K (diagSL3 K cycleWord) *
      theta w 2 (cycleWord ^ 2) := by
    rw [cyclic_eq w, upper_mul_lower_eq_diagSL3]
  have hm3 : m % 3 = 1 ∨ m % 3 = 2 := by omega
  have hX4 : diagonalWord ζ ^ (2 * 2) = diagonalWord ζ := by
    rw [pow_eq_pow_mod (2 * 2) hX3]
    norm_num
  have hY4 : cycleWord (K := K) ^ (2 * 2) = cycleWord := by
    rw [pow_eq_pow_mod (2 * 2) hY3]
    norm_num
  rcases hm3 with h1 | h2
  ·
    have hXm : diagonalWord ζ ^ m = diagonalWord ζ := by
      rw [pow_eq_pow_mod m hX3, h1, pow_one]
    have hX2m : diagonalWord ζ ^ (2 * m) = diagonalWord ζ ^ 2 := by
      rw [pow_eq_pow_mod (2 * m) hX3, show 2 * m % 3 = 2 by omega]
    set f : ModGL .E7 K := a5Frame K (diagSL3 K flipWord) * theta w 2 1 with hf
    have hfG : f ∈ adjointGroup .E7 K :=
      (adjointGroup .E7 K).mul_mem (a5Frame_mem_adjointGroup _) (theta_mem_adjointGroup w 2 1)
    refine ⟨f * g₀, (adjointGroup .E7 K).mul_mem hfG hg₀G, cubeE_le_of_mem h3 ?_ ?_ ?_⟩
    · have := mem_map_conj_mul (f := f) hsH
      rwa [hf, ← scalarWord_commute_frame w h3, mul_inv_cancel_right] at this
    · have key : f * (a5Frame K (diagSL3 K (diagonalWord ζ ^ (2 * m))) *
          theta w 2 (diagonalWord ζ ^ m)) * f⁻¹ = (pairedWord ζ : ModGL .E7 K) := by
        rw [hf, frame_conj, hXm, hX2m, one_mul, inv_one, mul_one, ← map_inv, ← map_mul, ← map_mul,
          ← conj_pow, flipWord_conj_diagonalWord h3, ← pow_mul, hX4, hp]
      have := mem_map_conj_mul (f := f) hx₀
      rwa [key] at this
    · have key : f * (a5Frame K (diagSL3 K cycleWord) * theta w 2 cycleWord) * f⁻¹ =
          a5Frame K (diagSL3 K (cycleWord ^ 2)) * theta w 2 cycleWord := by
        rw [hf, frame_conj, one_mul, inv_one, mul_one, ← map_inv, ← map_mul, ← map_mul,
          flipWord_conj_cycleWord]
      have hc2 : (cyclic (K := K) : ModGL .E7 K) =
          (a5Frame K (diagSL3 K (cycleWord ^ 2)) * theta w 2 cycleWord) ^ 2 := by
        rw [frame_pow, ← map_pow, ← pow_mul, hY4]
        exact hc
      have := mem_map_conj_mul (f := f) hy₀
      rw [key] at this
      rw [hc2]
      exact Subgroup.pow_mem _ this 2
  ·
    have hXm : diagonalWord ζ ^ m = diagonalWord ζ ^ 2 := by
      rw [pow_eq_pow_mod m hX3, h2]
    have hX2m : diagonalWord ζ ^ (2 * m) = diagonalWord ζ := by
      rw [pow_eq_pow_mod (2 * m) hX3, show 2 * m % 3 = 1 by omega, pow_one]
    set f : ModGL .E7 K := a5Frame K 1 * theta w 2 flipWord with hf
    have hfG : f ∈ adjointGroup .E7 K :=
      (adjointGroup .E7 K).mul_mem (a5Frame_mem_adjointGroup 1) (theta_mem_adjointGroup w 2 _)
    refine ⟨f * g₀, (adjointGroup .E7 K).mul_mem hfG hg₀G, cubeE_le_of_mem h3 ?_ ?_ ?_⟩
    · have := mem_map_conj_mul (f := f) hsH
      rwa [hf, ← scalarWord_commute_frame w h3, mul_inv_cancel_right] at this
    · have key : f * (a5Frame K (diagSL3 K (diagonalWord ζ ^ (2 * m))) *
          theta w 2 (diagonalWord ζ ^ m)) * f⁻¹ = (pairedWord ζ : ModGL .E7 K) := by
        rw [hf, frame_conj, hXm, hX2m, one_mul, inv_one, mul_one, ← conj_pow,
          flipWord_conj_diagonalWord h3, ← pow_mul, hX4, hp]
      have := mem_map_conj_mul (f := f) hx₀
      rwa [key] at this
    · have key : f * (a5Frame K (diagSL3 K cycleWord) * theta w 2 cycleWord) * f⁻¹ =
          (cyclic (K := K) : ModGL .E7 K) := by
        rw [hf, frame_conj, one_mul, inv_one, mul_one, flipWord_conj_cycleWord, hc]
      have := mem_map_conj_mul (f := f) hy₀
      rwa [key] at this

theorem exists_conj_cubeE_le_of_scalar_mem [IsAlgClosed K]
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) {E : Subgroup (ModGL .E7 K)} [Finite E]
    (hEG : E ≤ adjointGroup .E7 K) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) (hs : (scalarWord ζ : ModGL .E7 K) ∈ E)
    (hnt : ¬ ∃ g ∈ adjointGroup .E7 K, ∀ x ∈ E, g * x * g⁻¹ ∈ torusGroup .E7 K) :
    ∃ g ∈ adjointGroup .E7 K, cubeE ζ hζ.pow_eq_one ≤ E.map (MulAut.conj g).toMonoidHom := by
  classical
  obtain ⟨w⟩ := nativeFrame_exists (K := K)
  have hframe : ∀ x ∈ E, ∃ (A : SL(6, K)) (B : SL(3, K)), a5Frame K A * theta w 2 B = x :=
    fun x hx => exists_frame_of_commute_scalar w hζ (hEG hx) (hcomm x hx _ hs)
  choose! A B hAB using hframe
  by_cases hBc : ∀ x ∈ E, ∀ y ∈ E, B x * B y = B y * B x
  · exact absurd (exists_conj_torus_of_commute w hζ A B hAB hcomm hexp hBc) hnt
  · obtain ⟨x, hx, y, hy, hxy⟩ : ∃ x ∈ E, ∃ y ∈ E, B x * B y ≠ B y * B x := by
      by_contra h
      exact hBc fun x hx y hy => by_contra fun h' => h ⟨x, hx, y, hy, h'⟩
    have hc := hcomm x hx y hy
    rw [← hAB x hx, ← hAB y hy] at hc
    obtain ⟨m, hBm, hAm⟩ := exists_frame_commutator w hζ hc
    have hm : m % 3 ≠ 0 := by
      intro h0
      apply hxy
      rw [hBm, pow_eq_pow_mod m (centralWord_pow_three ζ hζ.pow_eq_one), h0, pow_zero, one_mul]
    refine exists_conj_cubeE_le_of_heis w hζ hs ?_ ?_ ?_ ?_ hm hBm hAm
    · rw [hAB x hx]; exact hx
    · rw [hAB y hy]; exact hy
    · rw [hAB x hx]; exact hexp x hx
    · rw [hAB y hy]; exact hexp y hy

end CFSG.LieType.Chevalley.E7Three.Centralizer
