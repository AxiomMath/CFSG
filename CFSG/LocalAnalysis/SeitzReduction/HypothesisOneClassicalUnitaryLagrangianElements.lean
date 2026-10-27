module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalUnitaryLagrangianFrame
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalLagrangian
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIsotropicRadical

public section

namespace CFSG.SeitzReduction

namespace UnitaryLagrangian

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f n : ℕ} {K : Type} [Field K]

section Frame

variable {h : UnitaryFieldData 2 f K} {G s : Matrix (Fin n) (Fin n) K} {l : ℕ}
  {e d : Fin l → Fin n → K}

theorem IsLagrangianFrame.matrix_ext (hF : IsLagrangianFrame h G s e d)
    {M M' : Matrix (Fin n) (Fin n) K} (he : ∀ k, M *ᵥ e k = M' *ᵥ e k)
    (hd : ∀ k, M *ᵥ d k = M' *ᵥ d k) : M = M' := by
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [hF.expand v]
  simp only [mulVec_add, mulVec_sum, mulVec_smul, he, hd]

theorem IsLagrangianFrame.mulVec_e (hF : IsLagrangianFrame h G s e d) (k : Fin l) :
    s *ᵥ e k = e k := by
  rw [hF.mulVec]
  simp [hF.ee]

theorem IsLagrangianFrame.mulVec_d (hF : IsLagrangianFrame h G s e d) (k : Fin l) :
    s *ᵥ d k = d k + e k := by
  rw [hF.mulVec]
  simp [hF.ed]

theorem IsLagrangianFrame.gramForm_d_sum (hF : IsLagrangianFrame h G s e d) (p : Fin l)
    (a : Fin l → K) : gramForm h G (d p) (∑ k, a k • e k) = a p := by
  simp [map_sum, hF.de]

theorem IsLagrangianFrame.sub_one_mul_self (hF : IsLagrangianFrame h G s e d) :
    (s - 1) * (s - 1) = 0 := by
  have h1 : ∀ k, (s - 1) *ᵥ e k = 0 := fun k => by
    rw [sub_mulVec, one_mulVec, hF.mulVec_e, sub_self]
  have h2 : ∀ k, (s - 1) *ᵥ d k = e k := fun k => by
    rw [sub_mulVec, one_mulVec, hF.mulVec_d, add_sub_cancel_left]
  refine hF.matrix_ext (fun k => ?_) fun k => ?_
  · rw [← mulVec_mulVec, h1, mulVec_zero, zero_mulVec]
  · rw [← mulVec_mulVec, h2, h1, zero_mulVec]

theorem IsLagrangianFrame.e_eq (hF : IsLagrangianFrame h G s e d) (k : Fin l) :
    e k = (s - 1) *ᵥ d k := by
  rw [sub_mulVec, one_mulVec, hF.mulVec_d, add_sub_cancel_left]

end Frame

section Radical

variable (h : UnitaryFieldData 2 f K) (G : Matrix (Fin n) (Fin n) K) {l : ℕ}
  (e : Fin l → Fin n → K)

@[expose] noncomputable def lagRad (c : K) (i j : Fin l) : Matrix (Fin n) (Fin n) K :=
  eichlerMatrix h G (e i) (c • e j) 0

variable {h G e} {s : Matrix (Fin n) (Fin n) K} {d : Fin l → Fin n → K}

theorem lagRad_mulVec (c : K) (i j : Fin l) (v : Fin n → K) :
    lagRad h G e c i j *ᵥ v =
      v + (c * gramForm h G (e i) v) • e j + (h.bar c * gramForm h G (e j) v) • e i := by
  have : CharP K 2 := h.charP
  rw [lagRad, eichlerMatrix_mulVec, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, zero_mul,
    zero_smul, add_zero, smul_smul, mul_comm (gramForm h G (e i) v) c, sub_eq_add_neg,
    ← neg_smul, CharTwo.neg_eq]

theorem lagRad_mulVec_e (hF : IsLagrangianFrame h G s e d) (c : K) (i j k : Fin l) :
    lagRad h G e c i j *ᵥ e k = e k := by
  rw [lagRad_mulVec, hF.ee, hF.ee]
  simp

theorem lagRad_mulVec_d (hF : IsLagrangianFrame h G s e d) (c : K) (i j k : Fin l) :
    lagRad h G e c i j *ᵥ d k =
      d k + (if i = k then c else 0) • e j + (if j = k then h.bar c else 0) • e i := by
  rw [lagRad_mulVec, hF.ed, hF.ed]
  simp only [mul_ite, mul_one, mul_zero]

theorem lagRad_mul (hF : IsLagrangianFrame h G s e d) (c c' : K) (i j : Fin l) :
    lagRad h G e c i j * lagRad h G e c' i j = lagRad h G e (c + c') i j := by
  refine hF.matrix_ext (fun k => ?_) fun k => ?_
  · rw [← mulVec_mulVec, lagRad_mulVec_e hF, lagRad_mulVec_e hF, lagRad_mulVec_e hF]
  · rw [← mulVec_mulVec, lagRad_mulVec_d hF, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul,
      lagRad_mulVec_e hF, lagRad_mulVec_e hF, lagRad_mulVec_d hF, lagRad_mulVec_d hF, map_add]
    split_ifs <;> module

theorem lagRad_zero (hF : IsLagrangianFrame h G s e d) (i j : Fin l) :
    lagRad h G e 0 i j = 1 := by
  refine hF.matrix_ext (fun k => ?_) fun k => ?_
  · rw [lagRad_mulVec_e hF, one_mulVec]
  · rw [lagRad_mulVec_d hF, one_mulVec, map_zero]
    simp

theorem lagRad_mul_self (hF : IsLagrangianFrame h G s e d) (c : K) (i j : Fin l) :
    lagRad h G e c i j * lagRad h G e c i j = 1 := by
  have : CharP K 2 := h.charP
  rw [lagRad_mul hF, CharTwo.add_self_eq_zero, lagRad_zero hF]

theorem lagRad_commute (hF : IsLagrangianFrame h G s e d) (c : K) (i j : Fin l) :
    s * lagRad h G e c i j = lagRad h G e c i j * s := by
  refine hF.matrix_ext (fun k => ?_) fun k => ?_
  · rw [← mulVec_mulVec, ← mulVec_mulVec, lagRad_mulVec_e hF, hF.mulVec_e, lagRad_mulVec_e hF]
  · rw [← mulVec_mulVec, ← mulVec_mulVec, lagRad_mulVec_d hF, hF.mulVec_d, mulVec_add,
      mulVec_add, mulVec_smul, mulVec_smul, hF.mulVec_e, hF.mulVec_e, hF.mulVec_d, mulVec_add,
      lagRad_mulVec_d hF, lagRad_mulVec_e hF]
    abel

theorem lagRad_sub_one_pow_three (hF : IsLagrangianFrame h G s e d)
    (hH : (gramForm h G).IsSymm) (c : K) (i j : Fin l) :
    (lagRad h G e c i j - 1) ^ 3 = 0 :=
  eichlerMatrix_sub_one_pow_three hH (hF.ee i i) (by rw [map_smul, hF.ee, smul_zero]) 0

@[expose] noncomputable def lagRadSU (hF : IsLagrangianFrame h G s e d)
    (hH : (gramForm h G).IsSymm) (c : K) (i j : Fin l) : gramSU h G :=
  ⟨unipotentGL (lagRad h G e c i j) (lagRad_sub_one_pow_three hF hH c i j),
    eichlerGL_mem hH (hF.ee i i) (by rw [map_smul, hF.ee, smul_zero])
      (by simp [hF.ee])⟩

theorem coe_lagRadSU (hF : IsLagrangianFrame h G s e d) (hH : (gramForm h G).IsSymm) (c : K)
    (i j : Fin l) :
    (((lagRadSU hF hH c i j : gramSU h G) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      lagRad h G e c i j :=
  rfl

end Radical

section Torus

variable (h : UnitaryFieldData 2 f K) (G : Matrix (Fin n) (Fin n) K) {l : ℕ}
  (e d : Fin l → Fin n → K)

@[expose] noncomputable def hypTorus (w x : Fin n → K) (a : K) : Matrix (Fin n) (Fin n) K :=
  (1 + a • vecMulVec x (gramRow h G w)) * (1 + a • vecMulVec w (gramRow h G x))

@[expose] noncomputable def lagTorus (τ σ : K) (i j : Fin l) : Matrix (Fin n) (Fin n) K :=
  hypTorus h G (e i) (d i) (τ - 1) * hypTorus h G (e j) (d j) (σ - 1)

variable {h G e d}

theorem hypTorus_mulVec {w x : Fin n → K} (hww : gramForm h G w w = 0) (a : K)
    (v : Fin n → K) :
    hypTorus h G w x a *ᵥ v = v + (a * gramForm h G w v) • x + (a * gramForm h G x v) • w := by
  rw [hypTorus, ← mulVec_mulVec]
  simp only [add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, gramRow_dotProduct,
    op_smul_eq_smul, smul_smul, map_add, map_smul, smul_eq_mul, hww, mul_zero, add_zero]
  abel

theorem det_one_add_smul_vecMulVec (a : K) (u r : Fin n → K) :
    (1 + a • vecMulVec u r).det = 1 + a * (r ⬝ᵥ u) := by
  rw [← smul_vecMulVec, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow,
    dotProduct_smul, smul_eq_mul]

theorem hypTorus_det {w x : Fin n → K} (hwx : gramForm h G w x = 1)
    (hxw : gramForm h G x w = 1) (a : K) : (hypTorus h G w x a).det = (1 + a) * (1 + a) := by
  rw [hypTorus, det_mul, det_one_add_smul_vecMulVec, det_one_add_smul_vecMulVec,
    gramRow_dotProduct, gramRow_dotProduct, hwx, hxw, mul_one]

theorem hypTorus_isometry (hH : (gramForm h G).IsSymm) {w x : Fin n → K}
    (hww : gramForm h G w w = 0) (hxx : gramForm h G x x = 0) (hwx : gramForm h G w x = 1)
    (hxw : gramForm h G x w = 1) {a : K} (ha : h.bar (1 + a) * (1 + a) = 1) (v v' : Fin n → K) :
    gramForm h G (hypTorus h G w x a *ᵥ v) (hypTorus h G w x a *ᵥ v') = gramForm h G v v' := by
  rw [hypTorus_mulVec hww, hypTorus_mulVec hww]
  have hvx : gramForm h G v x = h.bar (gramForm h G x v) := (hH.eq x v).symm
  have hvw : gramForm h G v w = h.bar (gramForm h G w v) := (hH.eq w v).symm
  simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hww, hxx, hwx, hxw, hvx, hvw, map_mul]
  rw [map_add, map_one] at ha
  linear_combination (h.bar (gramForm h G w v) * gramForm h G x v' +
    h.bar (gramForm h G x v) * gramForm h G w v') * ha

variable {s : Matrix (Fin n) (Fin n) K}

theorem hypTorus_mulVec_e (hF : IsLagrangianFrame h G s e d) (a : K) (i k : Fin l) :
    hypTorus h G (e i) (d i) a *ᵥ e k = e k + (if i = k then a else 0) • e i := by
  rw [hypTorus_mulVec (hF.ee i i), hF.ee, hF.de]
  simp only [mul_zero, zero_smul, add_zero, mul_ite, mul_one]

theorem hypTorus_mulVec_d (hF : IsLagrangianFrame h G s e d) (a : K) (i k : Fin l) :
    hypTorus h G (e i) (d i) a *ᵥ d k = d k + (if i = k then a else 0) • d i := by
  rw [hypTorus_mulVec (hF.ee i i), hF.ed, hF.dd]
  simp only [mul_zero, zero_smul, add_zero, mul_ite, mul_one]

theorem lagTorus_mulVec_e (hF : IsLagrangianFrame h G s e d) (τ σ : K) {i j : Fin l}
    (hij : i ≠ j) (k : Fin l) :
    lagTorus h G e d τ σ i j *ᵥ e k =
      e k + (if i = k then τ - 1 else 0) • e i + (if j = k then σ - 1 else 0) • e j := by
  rw [lagTorus, ← mulVec_mulVec, hypTorus_mulVec_e hF, mulVec_add, mulVec_smul,
    hypTorus_mulVec_e hF, hypTorus_mulVec_e hF, ite_eq_right hij]
  simp only [zero_smul, add_zero]

theorem lagTorus_mulVec_d (hF : IsLagrangianFrame h G s e d) (τ σ : K) {i j : Fin l}
    (hij : i ≠ j) (k : Fin l) :
    lagTorus h G e d τ σ i j *ᵥ d k =
      d k + (if i = k then τ - 1 else 0) • d i + (if j = k then σ - 1 else 0) • d j := by
  rw [lagTorus, ← mulVec_mulVec, hypTorus_mulVec_d hF, mulVec_add, mulVec_smul,
    hypTorus_mulVec_d hF, hypTorus_mulVec_d hF, ite_eq_right hij]
  simp only [zero_smul, add_zero]

theorem lagTorus_det (hF : IsLagrangianFrame h G s e d) {τ σ : K} (hτσ : τ * σ = 1)
    (i j : Fin l) : (lagTorus h G e d τ σ i j).det = 1 := by
  have hii : gramForm h G (e i) (d i) = 1 := by rw [hF.ed, ite_eq_left rfl]
  have hii' : gramForm h G (d i) (e i) = 1 := by rw [hF.de, ite_eq_left rfl]
  have hjj : gramForm h G (e j) (d j) = 1 := by rw [hF.ed, ite_eq_left rfl]
  have hjj' : gramForm h G (d j) (e j) = 1 := by rw [hF.de, ite_eq_left rfl]
  rw [lagTorus, det_mul, hypTorus_det hii hii', hypTorus_det hjj hjj']
  linear_combination (τ * σ + 1) * hτσ

theorem lagTorus_isometry (hF : IsLagrangianFrame h G s e d) (hH : (gramForm h G).IsSymm)
    {τ σ : K} (hτ : h.bar τ * τ = 1) (hσ : h.bar σ * σ = 1) (i j : Fin l) (v v' : Fin n → K) :
    gramForm h G (lagTorus h G e d τ σ i j *ᵥ v) (lagTorus h G e d τ σ i j *ᵥ v') =
      gramForm h G v v' := by
  have hii : gramForm h G (e i) (d i) = 1 := by rw [hF.ed, ite_eq_left rfl]
  have hii' : gramForm h G (d i) (e i) = 1 := by rw [hF.de, ite_eq_left rfl]
  have hjj : gramForm h G (e j) (d j) = 1 := by rw [hF.ed, ite_eq_left rfl]
  have hjj' : gramForm h G (d j) (e j) = 1 := by rw [hF.de, ite_eq_left rfl]
  rw [lagTorus, ← mulVec_mulVec, ← mulVec_mulVec,
    hypTorus_isometry hH (hF.ee i i) (hF.dd i i) hii hii' (by rwa [add_sub_cancel]),
    hypTorus_isometry hH (hF.ee j j) (hF.dd j j) hjj hjj' (by rwa [add_sub_cancel])]

theorem lagTorus_commute (hF : IsLagrangianFrame h G s e d) (τ σ : K) {i j : Fin l}
    (hij : i ≠ j) : s * lagTorus h G e d τ σ i j = lagTorus h G e d τ σ i j * s := by
  refine hF.matrix_ext (fun k => ?_) fun k => ?_
  · rw [← mulVec_mulVec, ← mulVec_mulVec, lagTorus_mulVec_e hF τ σ hij, hF.mulVec_e,
      mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, hF.mulVec_e, hF.mulVec_e, hF.mulVec_e,
      lagTorus_mulVec_e hF τ σ hij]
  · rw [← mulVec_mulVec, ← mulVec_mulVec, lagTorus_mulVec_d hF τ σ hij, hF.mulVec_d,
      mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, hF.mulVec_d, hF.mulVec_d, hF.mulVec_d,
      mulVec_add, lagTorus_mulVec_d hF τ σ hij, lagTorus_mulVec_e hF τ σ hij, smul_add,
      smul_add]
    abel

theorem lagTorus_mul_lagRad (hF : IsLagrangianFrame h G s e d) {τ σ : K} (hτσ : σ * τ = 1)
    (hστ : h.bar τ = σ) {i j : Fin l} (hij : i ≠ j) (c : K) :
    lagTorus h G e d τ σ i j * lagRad h G e c i j =
      lagRad h G e (c * σ * σ) i j * lagTorus h G e d τ σ i j := by
  have hbσ : h.bar σ = τ := by rw [← hστ, h.bar_bar]
  refine hF.matrix_ext (fun k => ?_) fun k => ?_
  · rw [← mulVec_mulVec, ← mulVec_mulVec, lagRad_mulVec_e hF, lagTorus_mulVec_e hF τ σ hij,
      mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, lagRad_mulVec_e hF, lagRad_mulVec_e hF,
      lagRad_mulVec_e hF]
  · rw [← mulVec_mulVec, ← mulVec_mulVec, lagRad_mulVec_d hF, lagTorus_mulVec_d hF τ σ hij,
      mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, lagTorus_mulVec_d hF τ σ hij,
      lagTorus_mulVec_e hF τ σ hij, lagTorus_mulVec_e hF τ σ hij, mulVec_add, mulVec_add,
      mulVec_smul, mulVec_smul, lagRad_mulVec_d hF, lagRad_mulVec_d hF, lagRad_mulVec_d hF,
      map_mul, map_mul, hbσ]
    have hji : j ≠ i := hij.symm
    by_cases hik : i = k
    · subst hik
      simp only [ite_true, hji, hij, ite_false, zero_smul, add_zero, smul_add, smul_smul]
      funext m
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(c * σ * e j m)) * hτσ
    · by_cases hjk : j = k
      · subst hjk
        simp only [ite_true, hij, hji, ite_false, zero_smul, add_zero, smul_add, smul_smul]
        funext m
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linear_combination (-(h.bar c * τ * e i m)) * hτσ
      · simp only [hik, hjk, ite_false, zero_smul, add_zero]

@[expose] noncomputable def lagTorusSU (hF : IsLagrangianFrame h G s e d)
    (hH : (gramForm h G).IsSymm) {τ σ : K} (hτσ : τ * σ = 1) (hτ : h.bar τ * τ = 1)
    (hσ : h.bar σ * σ = 1) (i j : Fin l) : gramSU h G :=
  ⟨Matrix.nonsingInvUnit (lagTorus h G e d τ σ i j) (by rw [lagTorus_det hF hτσ]; exact isUnit_one),
    mem_gramSU_iff_isometry.mpr ⟨lagTorus_isometry hF hH hτ hσ i j, lagTorus_det hF hτσ i j⟩⟩

theorem coe_lagTorusSU (hF : IsLagrangianFrame h G s e d) (hH : (gramForm h G).IsSymm)
    {τ σ : K} (hτσ : τ * σ = 1) (hτ : h.bar τ * τ = 1) (hσ : h.bar σ * σ = 1) (i j : Fin l) :
    (((lagTorusSU hF hH hτσ hτ hσ i j : gramSU h G) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = lagTorus h G e d τ σ i j :=
  rfl

end Torus

section Rigidity

variable {h : UnitaryFieldData 2 f K} {G s : Matrix (Fin n) (Fin n) K} {l : ℕ}
  {e d : Fin l → Fin n → K}

theorem rigidity_of_commute (hF : IsLagrangianFrame h G s e d) (hl : 3 ≤ l) (A : GL (Fin n) K)
    (φ : K ≃+* K) (hAs : (A : Matrix (Fin n) (Fin n) K) * s.map φ = s * A)
    (hAu : ∀ (c : K) (i j : Fin l), i ≠ j →
      (A : Matrix (Fin n) (Fin n) K) * (lagRad h G e c i j).map φ =
        lagRad h G e c i j * A) :
    φ = RingEquiv.refl K ∧ ∃ μ : K,
      (A : Matrix (Fin n) (Fin n) K) * A = (μ * μ) • (1 : Matrix (Fin n) (Fin n) K) := by
  classical
  have : CharP K 2 := h.charP
  set Am := (A : Matrix (Fin n) (Fin n) K) with hAm
  set T : (Fin n → K) → Fin n → K := fun v => Am *ᵥ fun k => φ (v k) with hT
  have hφv : ∀ (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K),
      (fun k => φ ((M *ᵥ v) k)) = M.map φ *ᵥ fun k => φ (v k) := fun M v =>
    funext fun k => RingHom.map_mulVec (φ : K →+* K) M v k
  have hTM : ∀ M : Matrix (Fin n) (Fin n) K, Am * M.map φ = M * Am →
      ∀ v, T (M *ᵥ v) = M *ᵥ T v := by
    intro M hM v
    simp only [hT]
    rw [hφv, mulVec_mulVec, hM, ← mulVec_mulVec]
  have hTadd : ∀ v w, T (v + w) = T v + T w := fun v w => by
    simp only [hT]
    rw [show (fun k => φ ((v + w) k)) = (fun k => φ (v k)) + fun k => φ (w k) from
      funext fun k => map_add φ _ _, mulVec_add]
  have hTsmul : ∀ (a : K) v, T (a • v) = φ a • T v := fun a v => by
    simp only [hT]
    rw [show (fun k => φ ((a • v) k)) = φ a • fun k => φ (v k) from
      funext fun k => by simp only [Pi.smul_apply, smul_eq_mul, map_mul], mulVec_smul]
  have hTinj : ∀ v, T v = 0 → v = 0 := by
    intro v hv
    have h1 : (fun k => φ (v k)) = 0 := by
      have := congrArg (fun w => ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) hv
      simp only [hT, mulVec_mulVec, hAm, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        one_mulVec, mulVec_zero] at this
      exact this
    funext k
    have := congrFun h1 k
    simpa using this
  set a : Fin l → Fin l → K := fun k m => gramForm h G (e k) (T (d m)) with ha
  have hTe : ∀ m, T (e m) = ∑ k, a k m • e k := by
    intro m
    have h1 := hTM s hAs (d m)
    rw [hF.mulVec_d, hTadd, hF.mulVec] at h1
    exact add_left_cancel h1
  have hdTe : ∀ p m, gramForm h G (d p) (T (e m)) = a p m := fun p m => by
    rw [hTe, hF.gramForm_d_sum]
  have hrel : ∀ (c : K) (i j p : Fin l), i ≠ j →
      φ c * a p j = (if p = j then c * a i i else 0) +
        (if p = i then h.bar c * a j i else 0) := by
    intro c i j p hij
    have h1 := hTM _ (hAu c i j hij) (d i)
    rw [lagRad_mulVec_d hF, ite_eq_left rfl, ite_eq_right hij.symm, zero_smul, add_zero, hTadd, hTsmul,
      lagRad_mulVec] at h1
    have h2 := congrArg (gramForm h G (d p)) h1
    simp only [map_add, map_smul, smul_eq_mul] at h2
    rw [hdTe, hF.de, hF.de] at h2
    have h3 : gramForm h G (e i) (T (d i)) = a i i := rfl
    have h4 : gramForm h G (e j) (T (d i)) = a j i := rfl
    rw [h3, h4] at h2
    split_ifs at h2 ⊢ with h5 h6 h6 <;> linear_combination h2
  have hthird : ∀ p j : Fin l, ∃ i, i ≠ p ∧ i ≠ j := by
    intro p j
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (Fin l)) ⊆ {p, j} := fun i _ => by
      by_cases hip : i = p
      · simp [hip]
      · simp [hcon i hip]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at this
    have h2 := Finset.card_le_two (a := p) (b := j)
    omega
  have hoff : ∀ p j, p ≠ j → a p j = 0 := by
    intro p j hpj
    obtain ⟨i, hip, hij⟩ := hthird p j
    have h1 := hrel 1 i j p hij
    rw [ite_eq_right hpj, ite_eq_right hip.symm, map_one, one_mul, add_zero] at h1
    exact h1
  set i₀ : Fin l := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin l := ⟨1, by omega⟩ with hi₁
  have h01 : i₀ ≠ i₁ := by simp [hi₀, hi₁, Fin.ext_iff]
  set μ := a i₀ i₀ with hμ
  have hdiag : ∀ j, a j j = μ := by
    intro j
    by_cases hj : j = i₀
    · rw [hj]
    · have h1 := hrel 1 i₀ j j (Ne.symm hj)
      rw [ite_eq_left rfl, ite_eq_right hj, map_one, one_mul, one_mul, add_zero] at h1
      exact h1
  have hTe' : ∀ m, T (e m) = μ • e m := by
    intro m
    rw [hTe]
    rw [Finset.sum_eq_single m (fun k _ hkm => by rw [hoff k m hkm, zero_smul])
      (fun hm => absurd (Finset.mem_univ m) hm), hdiag]
  have hμ0 : μ ≠ 0 := by
    intro h0
    have h1 := hTe' i₀
    rw [h0, zero_smul] at h1
    have h2 := hTinj _ h1
    have h3 := hF.ed i₀ i₀
    rw [h2, ite_eq_left rfl, map_zero, LinearMap.zero_apply] at h3
    exact zero_ne_one h3
  have hφ : ∀ c, φ c = c := by
    intro c
    have h1 := hrel c i₀ i₁ i₁ h01
    rw [ite_eq_left rfl, ite_eq_right h01.symm, add_zero, hdiag, hdiag] at h1
    exact mul_right_cancel₀ hμ0 h1
  have hφ1 : φ = RingEquiv.refl K := RingEquiv.ext hφ
  refine ⟨hφ1, μ, ?_⟩
  have hTA : ∀ v, T v = Am *ᵥ v := fun v => by
    simp only [hT, hφ]
  have hAe : ∀ m, Am *ᵥ e m = μ • e m := fun m => by rw [← hTA, hTe']
  have hAd : ∀ m, Am *ᵥ d m - μ • d m = ∑ k, gramForm h G (d k) (Am *ᵥ d m - μ • d m) • e k := by
    intro m
    conv_lhs => rw [hF.expand (Am *ᵥ d m - μ • d m)]
    have h1 : ∀ k, gramForm h G (e k) (Am *ᵥ d m - μ • d m) = 0 := by
      intro k
      rw [map_sub, map_smul, ← hTA, hF.ed, smul_eq_mul]
      by_cases hkm : k = m
      · rw [hkm, ite_eq_left rfl, mul_one]
        exact sub_eq_zero.mpr (hdiag m)
      · rw [ite_eq_right hkm, mul_zero, sub_zero]
        exact hoff k m hkm
    simp only [h1, zero_smul, Finset.sum_const_zero, add_zero]
  set X := Am - μ • (1 : Matrix (Fin n) (Fin n) K) with hX
  have hXv : ∀ v, X *ᵥ v = Am *ᵥ v - μ • v := fun v => by
    rw [hX, sub_mulVec, smul_mulVec, one_mulVec]
  have hXe : ∀ k, X *ᵥ e k = 0 := fun k => by rw [hXv, hAe, sub_self]
  have hXd : ∀ k, ∃ w, X *ᵥ d k = (s - 1) *ᵥ w := fun k =>
    ⟨∑ p, gramForm h G (d p) (X *ᵥ d k) • d p, by
      rw [mulVec_sum]
      simp only [mulVec_smul, ← hF.e_eq]
      rw [hXv]
      exact hAd k⟩
  choose w hw using hXd
  have hW : ∀ v, ∃ w, Am *ᵥ v - μ • v = (s - 1) *ᵥ w := by
    intro v
    refine ⟨∑ k, gramForm h G (e k) v • w k, ?_⟩
    rw [← hXv]
    conv_lhs => rw [hF.expand v]
    simp only [mulVec_add, mulVec_sum, mulVec_smul, hXe, smul_zero, Finset.sum_const_zero,
      zero_add, hw]
  have hsφ : s.map φ = s := by
    rw [hφ1]
    exact Matrix.ext fun _ _ => rfl
  have hAs' : Am * s = s * Am := by
    have := hAs
    rwa [hsφ] at this
  exact ClassicalLagrangian.matrix_mul_self_eq_smul_one hAs' hF.sub_one_mul_self hW

end Rigidity

end UnitaryLagrangian

end CFSG.SeitzReduction
