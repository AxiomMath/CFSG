module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7E6Base
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7E6Grp

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

namespace Cat7E6

open CatFactsSp4 Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag

variable {K : Type} [Field K]

theorem isUnit_det_of_similitude {X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K} {μ : K}
    (hμ : μ ≠ 0) (hX : Xᵀ * formJ 2 K * X = μ • formJ 2 K) : IsUnit X.det := by
  have h := congrArg Matrix.det hX
  rw [det_mul, det_mul, det_transpose, det_smul, Fintype.card_sum, Fintype.card_fin] at h
  refine isUnit_iff_ne_zero.mpr fun h0 => ?_
  rw [h0, zero_mul, zero_mul] at h
  exact mul_ne_zero (pow_ne_zero _ hμ) isUnit_det_formJ.ne_zero h.symm

@[expose] def gspOf (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (μ : Kˣ)
    (hX : Xᵀ * formJ 2 K * X = (μ : K) • formJ 2 K) : gsp 2 K :=
  ⟨nonsingInvUnit X (isUnit_det_of_similitude μ.ne_zero hX), ⟨μ, hX⟩⟩

@[simp] theorem coe_gspOf (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (μ : Kˣ)
    (hX : Xᵀ * formJ 2 K * X = (μ : K) • formJ 2 K) :
    (((gspOf X μ hX : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = X := rfl

theorem conjAut_eq_one_of_smul [Finite K] (A : gsp 2 K) {c : K}
    (h : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = c • 1) :
    conjAut 2 K A = 1 := by
  have hc : c ≠ 0 := by
    rintro rfl
    have := (A : GL (Fin 2 ⊕ Fin 2) K).isUnit.map (Matrix.detMonoidHom)
    rw [zero_smul] at h
    simp [Matrix.detMonoidHom, h] at this
  rw [conjAut_eq_one_iff]
  refine ⟨Units.mk0 c hc, Units.ext ?_⟩
  rw [h, GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.smul_one_eq_diagonal]
  rfl

theorem conjAut_eq_of_smul [Finite K] (A B : gsp 2 K) {c : K}
    (h : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      c • ((B : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) :
    conjAut 2 K A = conjAut 2 K B := by
  have h1 : conjAut 2 K (A * B⁻¹) = 1 := by
    apply conjAut_eq_one_of_smul _ (c := c)
    rw [Subgroup.coe_mul, Units.val_mul, h, Matrix.smul_mul, Subgroup.coe_inv,
      ← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

theorem fieldAut_comm_conjAut (σ : K ≃+* K) (A : gsp 2 K)
    (h : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map σ =
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) :
    conjAut 2 K A * fieldAut 2 K σ = fieldAut 2 K σ * conjAut 2 K A := by
  have h1 := fieldAut_mul_conjAut_mul_inv σ A
  have h2 : gspFieldMap σ A = A := Subtype.ext (Units.ext h)
  rw [h2, mul_inv_eq_iff_eq_mul] at h1
  exact h1.symm

@[expose] def dm : Matrix (Fin 2) (Fin 2) K := !![1, 0; 0, -1]

@[expose] def wm : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]

theorem dm_mul_dm : (dm : Matrix (Fin 2) (Fin 2) K) * dm = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [dm, Matrix.mul_apply, Fin.sum_univ_two]

theorem wm_mul_wm : (wm : Matrix (Fin 2) (Fin 2) K) * wm = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [wm, Matrix.mul_apply, Fin.sum_univ_two]

theorem dm_mul_wm : (dm : Matrix (Fin 2) (Fin 2) K) * wm = -(wm * dm) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [dm, wm, Matrix.mul_apply, Fin.sum_univ_two]

theorem dm_transpose_mul : (dm : Matrix (Fin 2) (Fin 2) K)ᵀ * dm = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [dm, Matrix.mul_apply, Fin.sum_univ_two]

theorem wm_transpose_mul : (wm : Matrix (Fin 2) (Fin 2) K)ᵀ * wm = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [wm, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_dm : (dm : Matrix (Fin 2) (Fin 2) K).det = -1 := by
  simp [dm, det_fin_two]

theorem det_wm : (wm : Matrix (Fin 2) (Fin 2) K).det = -1 := by
  simp [wm, det_fin_two]

theorem kron_similitude (g h : Matrix (Fin 2) (Fin 2) K) (hh : hᵀ * h = 1) :
    (kron g h)ᵀ * formJ 2 K * kron g h = g.det • formJ 2 K := by
  rw [formJ_eq_kron, kron_transpose, kron_mul, kron_mul, Matrix.mul_one,
    show gᵀ * J₁ * g = g.det • J₁ from transpose_mul_J₁_mul g, hh, kron_smul_left,
    kron_smul_right']

@[expose] def xD1 : gsp 2 K :=
  gspOf (kron dm 1) (-1) (by rw [kron_similitude _ _ (by simp), det_dm, Units.val_neg,
    Units.val_one])

@[expose] def xW1 : gsp 2 K :=
  gspOf (kron wm 1) (-1) (by rw [kron_similitude _ _ (by simp), det_wm, Units.val_neg,
    Units.val_one])

@[expose] def x1D : gsp 2 K :=
  gspOf (kron 1 dm) 1 (by rw [kron_similitude _ _ dm_transpose_mul, det_one, Units.val_one])

@[expose] def x1W : gsp 2 K :=
  gspOf (kron 1 wm) 1 (by rw [kron_similitude _ _ wm_transpose_mul, det_one, Units.val_one])

theorem coe_xD1 : (((xD1 : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = kron dm 1 := rfl

theorem coe_xW1 : (((xW1 : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = kron wm 1 := rfl

theorem coe_x1D : (((x1D : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = kron 1 dm := rfl

theorem coe_x1W : (((x1W : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = kron 1 wm := rfl

@[expose] def e1 : MulAut (StatedProj (StatedSp 2 K)) := conjAut 2 K xD1
@[expose] def e2 : MulAut (StatedProj (StatedSp 2 K)) := conjAut 2 K xW1
@[expose] def e3 : MulAut (StatedProj (StatedSp 2 K)) := conjAut 2 K x1D
@[expose] def e4 : MulAut (StatedProj (StatedSp 2 K)) := conjAut 2 K x1W

@[expose] def e16 (K : Type) [Field K] : Subgroup (MulAut (StatedProj (StatedSp 2 K))) :=
  closure ({e1, e2, e3, e4} : Set (MulAut (StatedProj (StatedSp 2 K))))

theorem conjAut_sq_eq_one [Finite K] (A : gsp 2 K)
    (h : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1) :
    conjAut 2 K A * conjAut 2 K A = 1 := by
  rw [← map_mul]
  apply conjAut_eq_one_of_smul _ (c := 1)
  rw [Subgroup.coe_mul, Units.val_mul, h, one_smul]

theorem conjAut_comm_of_sign [Finite K] (A B : gsp 2 K) {c : K}
    (h : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((B : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      c • (((B : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) :
    conjAut 2 K A * conjAut 2 K B = conjAut 2 K B * conjAut 2 K A := by
  rw [← map_mul, ← map_mul]
  apply conjAut_eq_of_smul _ _ (c := c)
  simp only [Subgroup.coe_mul, Units.val_mul]
  exact h

@[expose] def bmat {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K) (b : Bool) :
    Matrix ι ι K := if b then M else 1

theorem kron_neg_left (g h : Matrix (Fin 2) (Fin 2) K) : kron (-g) h = (-1 : K) • kron g h := by
  rw [show -g = (-1 : K) • g by simp, kron_smul_left, kron_smul_right']

theorem kron_neg_right (g h : Matrix (Fin 2) (Fin 2) K) : kron g (-h) = (-1 : K) • kron g h := by
  rw [show -h = (-1 : K) • h by simp, kron_smul_right']

theorem coe_prod4 (v : Bool × Bool × Bool × Bool) :
    (((prod4 xD1 xW1 x1D x1W v : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      kron (bmat dm v.1 * bmat wm v.2.1) (bmat dm v.2.2.1 * bmat wm v.2.2.2) := by
  obtain ⟨a, b, c, d⟩ := v
  simp only [prod4, Subgroup.coe_mul, Units.val_mul]
  have e : ∀ (x : gsp 2 K) (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
      (_ : ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = M)
      (t : Bool), (((bpow x t : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = bmat M t := by
    intro x M hM t
    cases t
    · simp [bpow, bmat]
    · simp [bpow, bmat, hM]
  rw [e xD1 _ (coe_gspOf _ _ _), e xW1 _ (coe_gspOf _ _ _), e x1D _ (coe_gspOf _ _ _),
    e x1W _ (coe_gspOf _ _ _)]
  have b1 : ∀ (g : Matrix (Fin 2) (Fin 2) K) (t : Bool), bmat (kron g 1) t = kron (bmat g t) 1 :=
    fun g t => by cases t <;> simp [bmat, kron_one_one]
  have b2 : ∀ (g : Matrix (Fin 2) (Fin 2) K) (t : Bool), bmat (kron 1 g) t = kron 1 (bmat g t) :=
    fun g t => by cases t <;> simp [bmat, kron_one_one]
  rw [b1, b1, b2, b2, kron_mul, kron_mul, kron_mul]
  simp only [Matrix.mul_one, Matrix.one_mul]

theorem scalar_of_kron_eq {g h : Matrix (Fin 2) (Fin 2) K} {c : K} (hg : g ≠ 0) (hh : h ≠ 0)
    (H : kron g h = c • 1) : (∃ s : K, g = s • 1) ∧ ∃ s : K, h = s • 1 := by
  have e : fromBlocks (g 0 0 • h) (g 0 1 • h) (g 1 0 • h) (g 1 1 • h) =
      fromBlocks (c • (1 : Matrix (Fin 2) (Fin 2) K)) 0 0 (c • 1) := by
    rw [← kron, H, ← fromBlocks_one, fromBlocks_smul, smul_zero]
  obtain ⟨e1, e2, e3, e4⟩ := fromBlocks_inj.mp e
  have g01 : g 0 1 = 0 := (smul_eq_zero.mp e2).resolve_right hh
  have g10 : g 1 0 = 0 := (smul_eq_zero.mp e3).resolve_right hh
  have g11 : g 1 1 = g 0 0 := by
    have h1 : (g 1 1 - g 0 0) • h = 0 := by rw [sub_smul, e4, e1, sub_self]
    exact (sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hh))
  have hgs : g = g 0 0 • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [g01, g10, g11]
  refine ⟨⟨g 0 0, hgs⟩, ?_⟩
  have hg0 : g 0 0 ≠ 0 := fun h0 => hg (by rw [hgs, h0, zero_smul])
  refine ⟨(g 0 0)⁻¹ * c, ?_⟩
  rw [mul_smul, ← e1, smul_smul, inv_mul_cancel₀ hg0, one_smul]

@[expose] def gm (a b : Bool) : Matrix (Fin 2) (Fin 2) K := bmat dm a * bmat wm b

theorem det_gm (a b : Bool) : (gm a b : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
  cases a <;> cases b <;> simp [gm, bmat, det_dm, det_wm]

theorem gm_ne_zero (a b : Bool) : (gm a b : Matrix (Fin 2) (Fin 2) K) ≠ 0 := fun h => by
  have := det_gm (K := K) a b
  rw [h, det_zero] at this
  exact this rfl

theorem eq_false_of_gm_scalar (h2 : (2 : K) ≠ 0) {a b : Bool}
    (h : ∃ s : K, (gm a b : Matrix (Fin 2) (Fin 2) K) = s • 1) : a = false ∧ b = false := by
  obtain ⟨s, hs⟩ := h
  have hne : (1 : K) ≠ -1 := fun h1 => h2 (by linear_combination h1)
  have e00 := congrFun (congrFun hs 0) 0
  have e01 := congrFun (congrFun hs 0) 1
  have e11 := congrFun (congrFun hs 1) 1
  cases a <;> cases b <;> simp [gm, bmat, dm, wm, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e11
  · exact ⟨rfl, rfl⟩
  · exact absurd (e00.trans e11.symm) hne

theorem prod4_eq_zero_of_scalar (h2 : (2 : K) ≠ 0) (v : Bool × Bool × Bool × Bool) {c : K}
    (h : kron (bmat dm v.1 * bmat wm v.2.1) (bmat dm v.2.2.1 * bmat wm v.2.2.2) =
      c • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) :
    v = (false, false, false, false) := by
  obtain ⟨a, b, d, e⟩ := v
  obtain ⟨hg, hh⟩ := scalar_of_kron_eq (gm_ne_zero a b) (gm_ne_zero d e) h
  obtain ⟨rfl, rfl⟩ := eq_false_of_gm_scalar h2 hg
  obtain ⟨rfl, rfl⟩ := eq_false_of_gm_scalar h2 hh
  rfl

theorem card_e16 [Finite K] (h2 : (2 : K) ≠ 0) :
    Nat.card (e16 K) = 16 ∧ ∀ y ∈ e16 K, y * y = 1 := by
  have hD1 := coe_xD1 (K := K)
  have hW1 := coe_xW1 (K := K)
  have h1D := coe_x1D (K := K)
  have h1W := coe_x1W (K := K)
  refine card_closure_four (conjAut_sq_eq_one _ ?_) (conjAut_sq_eq_one _ ?_)
    (conjAut_sq_eq_one _ ?_) (conjAut_sq_eq_one _ ?_) (conjAut_comm_of_sign _ _ (c := -1) ?_)
    (conjAut_comm_of_sign _ _ (c := 1) ?_) (conjAut_comm_of_sign _ _ (c := 1) ?_)
    (conjAut_comm_of_sign _ _ (c := 1) ?_) (conjAut_comm_of_sign _ _ (c := 1) ?_)
    (conjAut_comm_of_sign _ _ (c := -1) ?_) ?_
  · rw [hD1, kron_mul, dm_mul_dm, Matrix.one_mul, kron_one_one]
  · rw [hW1, kron_mul, wm_mul_wm, Matrix.one_mul, kron_one_one]
  · rw [h1D, kron_mul, dm_mul_dm, Matrix.one_mul, kron_one_one]
  · rw [h1W, kron_mul, wm_mul_wm, Matrix.one_mul, kron_one_one]
  · rw [hD1, hW1, kron_mul, kron_mul, dm_mul_wm, kron_neg_left]
  · rw [hD1, h1D, kron_mul, kron_mul, one_smul]
    simp
  · rw [hD1, h1W, kron_mul, kron_mul, one_smul]
    simp
  · rw [hW1, h1D, kron_mul, kron_mul, one_smul]
    simp
  · rw [hW1, h1W, kron_mul, kron_mul, one_smul]
    simp
  · rw [h1D, h1W, kron_mul, kron_mul, dm_mul_wm, kron_neg_right]
  · intro v hv
    have hv' : conjAut 2 K (prod4 xD1 xW1 x1D x1W v) = 1 := by
      rw [← hv]
      obtain ⟨a, b, c, d⟩ := v
      simp only [prod4, map_mul]
      have e : ∀ (x : gsp 2 K) (t : Bool), conjAut 2 K (bpow x t) = bpow (conjAut 2 K x) t :=
        fun x t => by cases t <;> simp [bpow]
      rw [e, e, e, e]
      rfl
    rw [conjAut_eq_one_iff] at hv'
    obtain ⟨u, hu⟩ := hv'
    apply prod4_eq_zero_of_scalar h2 v (c := u)
    rw [← coe_prod4, hu, GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal]
    rfl

theorem e16_le_range : e16 K ≤ (conjAut 2 K).range := by
  rw [e16, closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

theorem map_kron (σ : K ≃+* K) (g h : Matrix (Fin 2) (Fin 2) K) :
    (kron g h).map σ = kron (g.map σ) (h.map σ) := by
  simp only [kron, Matrix.fromBlocks_map]
  congr 1 <;> ext i j <;> simp [map_mul]

theorem map_dm (σ : K ≃+* K) : (dm : Matrix (Fin 2) (Fin 2) K).map σ = dm := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [dm]

theorem map_wm (σ : K ≃+* K) : (wm : Matrix (Fin 2) (Fin 2) K).map σ = wm := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [wm]

theorem map_one_two (σ : K ≃+* K) : (1 : Matrix (Fin 2) (Fin 2) K).map σ = 1 :=
  Matrix.map_one _ (map_zero σ) (map_one σ)

theorem comm_fieldAut_of_coe (σ : K ≃+* K) (A : gsp 2 K) {g h : Matrix (Fin 2) (Fin 2) K}
    (hA : (((A : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = kron g h)
    (hg : g.map σ = g) (hh : h.map σ = h) :
    fieldAut 2 K σ * conjAut 2 K A = conjAut 2 K A * fieldAut 2 K σ := by
  refine (fieldAut_comm_conjAut σ A ?_).symm
  rw [hA, map_kron, hg, hh]

theorem e16_le_centralizer (σ : K ≃+* K) :
    e16 K ≤ centralizer ({fieldAut 2 K σ} : Set (MulAut (StatedProj (StatedSp 2 K)))) := by
  rw [e16, closure_le]
  intro x hx
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact (comm_fieldAut_of_coe σ xD1 coe_xD1 (map_dm σ) (map_one_two σ)).symm
  · exact (comm_fieldAut_of_coe σ xW1 coe_xW1 (map_wm σ) (map_one_two σ)).symm
  · exact (comm_fieldAut_of_coe σ x1D coe_x1D (map_one_two σ) (map_dm σ)).symm
  · exact (comm_fieldAut_of_coe σ x1W coe_x1W (map_one_two σ) (map_wm σ)).symm

end Cat7E6

end CFSG.ComponentClassification.GSThmB
