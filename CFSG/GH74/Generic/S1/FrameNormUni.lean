module

public import CFSG.GH74.Generic.S1.FrameNorm
public import CFSG.GH74.Generic.S1.FrameMono
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianMatrix
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarCommutantSpace

public section

namespace CFSG.GH74.Generic.S1.FrameUni

open Matrix Module CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.Universal.Unitary
  CFSG.ComponentClassification.CatalogueBHermitian CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalGroups.Unitary

variable {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F)

@[expose] noncomputable def frameBar : F ≃+* F where
  toFun := h.bar
  invFun := h.bar
  left_inv := h.bar_bar
  right_inv := h.bar_bar
  map_mul' := map_mul h.bar
  map_add' := map_add h.bar

theorem frameBar_apply (c : F) : frameBar h c = h.bar c := rfl

theorem frameBar_sq : frameBar h ^ 2 = 1 := by
  ext c
  change frameBar h (frameBar h c) = c
  exact h.bar_bar c

theorem frameBar_ne_one : frameBar h ≠ 1 := by
  intro h1
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  apply hc
  have := congrArg (fun e : F ≃+* F => e c) h1
  exact this

theorem conjTr_eq (A : Matrix (Fin 4) (Fin 4) F) : conjTr (frameBar h) A = (A.map h.bar)ᵀ := rfl

theorem conjTr_conjTr (A : Matrix (Fin 4) (Fin 4) F) :
    conjTr (frameBar h) (conjTr (frameBar h) A) = A := by
  ext i j
  simp [conjTr, frameBar_apply, h.bar_bar]

theorem mem_S_iff {A : GL (Fin 4) F} :
    A ∈ StatedSU 4 (p ^ f) F ↔ (A : Matrix (Fin 4) (Fin 4) F).det = 1 ∧
      conjTr (frameBar h) (A : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F) = 1 :=
  mem_unitarySU_iff h

theorem det_conj_val (P k : GL (Fin 4) F) :
    ((P⁻¹ * k * P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det =
      (k : Matrix (Fin 4) (Fin 4) F).det := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul]
  have h1 : (P⁻¹ : GL (Fin 4) F).val.det * (P : Matrix (Fin 4) (Fin 4) F).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  calc (P⁻¹ : GL (Fin 4) F).val.det * (k : Matrix (Fin 4) (Fin 4) F).det *
        (P : Matrix (Fin 4) (Fin 4) F).det
      = ((P⁻¹ : GL (Fin 4) F).val.det * (P : Matrix (Fin 4) (Fin 4) F).det) *
          (k : Matrix (Fin 4) (Fin 4) F).det := by ring
    _ = _ := by rw [h1, one_mul]

theorem unitary_conj_mem {U : GL (Fin 4) F}
    (hU : conjTr (frameBar h) (U : Matrix (Fin 4) (Fin 4) F) * (U : Matrix (Fin 4) (Fin 4) F) = 1)
    {k : GL (Fin 4) F} (hk : k ∈ StatedSU 4 (p ^ f) F) : U⁻¹ * k * U ∈ StatedSU 4 (p ^ f) F := by
  rw [mem_S_iff h] at hk ⊢
  obtain ⟨hdet, hu⟩ := hk
  have hUU : (U : Matrix (Fin 4) (Fin 4) F) * conjTr (frameBar h) (U : Matrix (Fin 4) (Fin 4) F) = 1 :=
    mul_eq_one_comm.1 hU
  have hUinv : ((U⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      conjTr (frameBar h) (U : Matrix (Fin 4) (Fin 4) F) := Units.inv_eq_of_mul_eq_one_left hU
  refine ⟨by rw [det_conj_val, hdet], ?_⟩
  rw [Units.val_mul, Units.val_mul, conjTr_mul, conjTr_mul, hUinv, conjTr_conjTr]
  calc (conjTr (frameBar h) (U : Matrix (Fin 4) (Fin 4) F) *
          (conjTr (frameBar h) (k : Matrix (Fin 4) (Fin 4) F) * (U : Matrix (Fin 4) (Fin 4) F))) *
        (conjTr (frameBar h) (U : Matrix (Fin 4) (Fin 4) F) * (k : Matrix (Fin 4) (Fin 4) F) *
          (U : Matrix (Fin 4) (Fin 4) F))
      = conjTr (frameBar h) (U : Matrix (Fin 4) (Fin 4) F) *
          conjTr (frameBar h) (k : Matrix (Fin 4) (Fin 4) F) *
          ((U : Matrix (Fin 4) (Fin 4) F) * conjTr (frameBar h) (U : Matrix (Fin 4) (Fin 4) F)) *
          (k : Matrix (Fin 4) (Fin 4) F) * (U : Matrix (Fin 4) (Fin 4) F) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hUU, Matrix.mul_one, Matrix.mul_assoc (conjTr (frameBar h) (U : Matrix (Fin 4) (Fin 4) F)),
          hu, Matrix.mul_one, hU]

theorem commute_of_normalizes {ρ : GL (Fin 4) F}
    (hρ : ∀ k ∈ StatedSU 4 (p ^ f) F, ρ * k * ρ⁻¹ ∈ StatedSU 4 (p ^ f) F)
    {A : GL (Fin 4) F} (hA : A ∈ StatedSU 4 (p ^ f) F) :
    (conjTr (frameBar h) (ρ : Matrix (Fin 4) (Fin 4) F) * (ρ : Matrix (Fin 4) (Fin 4) F)) *
        (A : Matrix (Fin 4) (Fin 4) F) =
      (A : Matrix (Fin 4) (Fin 4) F) *
        (conjTr (frameBar h) (ρ : Matrix (Fin 4) (Fin 4) F) * (ρ : Matrix (Fin 4) (Fin 4) F)) := by
  have hB := ((mem_S_iff h).1 (hρ A hA)).2
  obtain ⟨-, hAu⟩ := (mem_S_iff h).1 hA
  have hAA : (A : Matrix (Fin 4) (Fin 4) F) * conjTr (frameBar h) (A : Matrix (Fin 4) (Fin 4) F) = 1 :=
    mul_eq_one_comm.1 hAu
  set a := conjTr (frameBar h) (ρ : Matrix (Fin 4) (Fin 4) F) with ha
  set ai := conjTr (frameBar h) ((ρ⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hai
  set R := (ρ : Matrix (Fin 4) (Fin 4) F) with hR
  set Ri := ((ρ⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hRi
  set At := conjTr (frameBar h) (A : Matrix (Fin 4) (Fin 4) F) with hAt
  set Am := (A : Matrix (Fin 4) (Fin 4) F) with hAm
  have haai : a * ai = 1 := by
    rw [ha, hai, ← conjTr_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, conjTr_one]
  have hρρ : Ri * R = 1 := by
    rw [hRi, hR, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [Units.val_mul, Units.val_mul, conjTr_mul, conjTr_mul, ← ha, ← hai, ← hR, ← hRi, ← hAm,
    ← hAt] at hB
  have key : At * (a * R) * Am = a * R := by
    calc At * (a * R) * Am = (a * ai) * (At * a) * R * Am * (Ri * R) := by
          rw [haai, hρρ]; simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
      _ = a * (ai * (At * a) * (R * Am * Ri)) * R := by simp only [Matrix.mul_assoc]
      _ = a * R := by rw [hB, Matrix.mul_one]
  calc a * R * Am = (Am * At) * (a * R) * Am := by rw [hAA, Matrix.one_mul]
    _ = Am * (At * (a * R) * Am) := by simp only [Matrix.mul_assoc]
    _ = Am * (a * R) := by rw [key]


theorem conjTr_diagonal (d : Fin 4 → F) :
    conjTr (frameBar h) (Matrix.diagonal d) = Matrix.diagonal (fun a => h.bar (d a)) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [conjTr, frameBar_apply]
  · simp [conjTr, hij, Ne.symm hij]

theorem trace_conjTr (A : Matrix (Fin 4) (Fin 4) F) :
    Matrix.trace (conjTr (frameBar h) A) = h.bar (Matrix.trace A) := by
  simp [Matrix.trace, conjTr, frameBar_apply, map_sum]

theorem conjTr_smul (c : F) (A : Matrix (Fin 4) (Fin 4) F) :
    conjTr (frameBar h) (c • A) = h.bar c • conjTr (frameBar h) A := by
  ext i j
  simp [conjTr, frameBar_apply]

@[expose] def torusVec (i j : Fin 4) (lam : F) : Fin 4 → F :=
  fun a => if a = i then lam else if a = j then lam⁻¹ else 1

@[expose] noncomputable def torusGL (i j : Fin 4) (lam : F) (hlam : lam ≠ 0) : GL (Fin 4) F :=
  ⟨Matrix.diagonal (torusVec i j lam), Matrix.diagonal (torusVec i j lam⁻¹), by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    by_cases h1 : a = i
    · simp [torusVec, h1, hlam]
    · by_cases h2 : a = j
      · subst h2; simp [torusVec, h1, hlam]
      · simp [torusVec, h1, h2], by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    by_cases h1 : a = i
    · simp [torusVec, h1, hlam]
    · by_cases h2 : a = j
      · subst h2; simp [torusVec, h1, hlam]
      · simp [torusVec, h1, h2]⟩

theorem torusGL_val (i j : Fin 4) (lam : F) (hlam : lam ≠ 0) :
    ((torusGL i j lam hlam : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal (torusVec i j lam) := rfl

theorem torusGL_mem {i j : Fin 4} (hij : i ≠ j) {lam : F} (hlam : lam ≠ 0)
    (hnorm : h.bar lam * lam = 1) : torusGL i j lam hlam ∈ StatedSU 4 (p ^ f) F := by
  rw [mem_S_iff h, torusGL_val]
  constructor
  · rw [Matrix.det_diagonal, Fintype.prod_eq_mul i j hij (fun a ha => by simp [torusVec, ha.1, ha.2])]
    simp [torusVec, hij.symm, hlam]
  · rw [conjTr_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    by_cases h1 : a = i
    · simp [torusVec, h1, hnorm]
    · by_cases h2 : a = j
      · subst h2
        simp only [torusVec, h1, ite_false, ite_true]
        rw [map_inv₀, ← mul_inv, hnorm, inv_one]
      · simp [torusVec, h1, h2]


theorem mul_apply_of_offdiag {M : Matrix (Fin 4) (Fin 4) F} (hoff : ∀ i j, i ≠ j → M i j = 0)
    (A : Matrix (Fin 4) (Fin 4) F) (a b : Fin 4) :
    (M * A) a b = M a a * A a b ∧ (A * M) a b = A a b * M b b := by
  constructor
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · intro c _ hc
      rw [hoff a c (Ne.symm hc), zero_mul]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  · rw [Matrix.mul_apply, Finset.sum_eq_single b]
    · intro c _ hc
      rw [hoff c b hc, mul_zero]
    · intro hb
      exact absurd (Finset.mem_univ b) hb

include h in
theorem eq_scalar_of_commute (hp2 : p ≠ 2) {M : Matrix (Fin 4) (Fin 4) F}
    (hM : ∀ A : GL (Fin 4) F, A ∈ StatedSU 4 (p ^ f) F →
      M * (A : Matrix (Fin 4) (Fin 4) F) = (A : Matrix (Fin 4) (Fin 4) F) * M) :
    ∃ c : F, M = c • (1 : Matrix (Fin 4) (Fin 4) F) := by
  obtain ⟨lam, hnorm, hnf⟩ := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.exists_norm_one_not_fixed h hp2
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hnorm
    exact zero_ne_one hnorm
  have hbar : h.bar lam = lam⁻¹ := eq_inv_of_mul_eq_one_left hnorm
  have hne : lam⁻¹ - lam ≠ 0 := by
    intro h0
    apply hnf
    rw [UnitaryFieldData.mem_fixedField, hbar]
    exact sub_eq_zero.1 h0
  have hoff : ∀ i j, i ≠ j → M i j = 0 := by
    intro i j hij
    have h1 := congrFun (congrFun (hM (torusGL i j lam hlam0) (torusGL_mem h hij hlam0 hnorm)) i) j
    rw [torusGL_val, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    simp only [torusVec, hij.symm, ite_true, ite_false] at h1
    have h3 : M i j * (lam⁻¹ - lam) = 0 := by linear_combination h1
    exact (mul_eq_zero.1 h3).resolve_right hne
  have hodd : Odd (p ^ f) := by
    have := h.prime.eq_two_or_odd'
    rcases this with h2 | h2
    · exact absurd h2 hp2
    · exact h2.pow
  have hdiag : ∀ i : Fin 4, i ≠ 3 → M i i = M 3 3 := by
    intro i hi
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by
      fin_cases i <;> simp_all
    have h1 := congrFun (congrFun (hM (monoGL F i) (monoGL_mem_statedSU F hodd i)) 3) i
    change (M * monoMat F i) 3 i = (monoMat F i * M) 3 i at h1
    rw [(mul_apply_of_offdiag hoff _ 3 i).1, (mul_apply_of_offdiag hoff _ 3 i).2] at h1
    have hm : monoMat F i 3 i = 1 := by
      rcases hi' with rfl | rfl | rfl <;> simp [monoMat]
    rw [hm] at h1
    linear_combination -h1
  refine ⟨M 3 3, ?_⟩
  ext a b
  by_cases hab : a = b
  · subst hab
    by_cases ha : a = 3
    · subst ha; simp
    · rw [hdiag a ha]; simp
  · simp [hoff a b hab, hab]


theorem scalar_eq_one_of_trace (h2 : (2 : F) ≠ 0) {R : Matrix (Fin 4) (Fin 4) F} (hR : R * R = 1)
    (htr : Matrix.trace R = 2) {c : F}
    (hc : conjTr (frameBar h) R * R = c • (1 : Matrix (Fin 4) (Fin 4) F)) : c = 1 := by
  have h1 : conjTr (frameBar h) R = c • R := by
    calc conjTr (frameBar h) R = conjTr (frameBar h) R * (R * R) := by rw [hR, Matrix.mul_one]
      _ = (conjTr (frameBar h) R * R) * R := (Matrix.mul_assoc _ _ _).symm
      _ = c • R := by rw [hc, Matrix.smul_mul, Matrix.one_mul]
  have h2' := congrArg Matrix.trace h1
  rw [trace_conjTr, Matrix.trace_smul, htr, smul_eq_mul, map_ofNat] at h2'
  have h3 : (2 : F) * (1 - c) = 0 := by linear_combination h2'
  have := (mul_eq_zero.1 h3).resolve_left h2
  linear_combination -this


theorem isSymm_restrict {σ : F ≃+* F} {B : (Fin 4 → F) →ₛₗ[σ.toRingHom] (Fin 4 → F) →ₗ[F] F}
    (hB : B.IsSymm) (W : Submodule F (Fin 4 → F)) : (B.domRestrict₁₂ W W).IsSymm :=
  ⟨fun x y => hB.eq (x : Fin 4 → F) (y : Fin 4 → F)⟩

theorem nondeg_restrict {σ : F ≃+* F} {B : (Fin 4 → F) →ₛₗ[σ.toRingHom] (Fin 4 → F) →ₗ[F] F}
    (hBnd : B.Nondegenerate) {W W' : Submodule F (Fin 4 → F)} (hc : IsCompl W W')
    (h1 : ∀ x ∈ W, ∀ y ∈ W', B x y = 0) (h2 : ∀ x ∈ W', ∀ y ∈ W, B x y = 0) :
    (B.domRestrict₁₂ W W).Nondegenerate := by
  have hsplit : ∀ z : Fin 4 → F, ∃ a ∈ W, ∃ b ∈ W', z = a + b := fun z => by
    have : z ∈ W ⊔ W' := by rw [hc.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 this
    exact ⟨a, ha, b, hb, hab.symm⟩
  constructor
  · intro x hx
    apply Subtype.ext
    apply hBnd.1 x
    intro z
    obtain ⟨a, ha, b, hb, rfl⟩ := hsplit z
    rw [map_add, h1 x x.2 b hb, add_zero]
    exact hx ⟨a, ha⟩
  · intro y hy
    apply Subtype.ext
    apply hBnd.2 y
    intro z
    obtain ⟨a, ha, b, hb, rfl⟩ := hsplit z
    rw [map_add, LinearMap.add_apply, h2 b hb y y.2, add_zero]
    exact hy ⟨a, ha⟩


theorem exists_unitary_diag [Finite F] (hp2 : p ≠ 2) {ρ : GL (Fin 4) F}
    (hρ : (ρ : Matrix (Fin 4) (Fin 4) F) * ρ = 1)
    (hu : conjTr (frameBar h) (ρ : Matrix (Fin 4) (Fin 4) F) * (ρ : Matrix (Fin 4) (Fin 4) F) = 1)
    (hdim : finrank F (LinearMap.ker (toLin' (ρ : Matrix (Fin 4) (Fin 4) F) - 1)) = 3) :
    ∃ G : GL (Fin 4) F,
      conjTr (frameBar h) (G : Matrix (Fin 4) (Fin 4) F) * (G : Matrix (Fin 4) (Fin 4) F) = 1 ∧
        G⁻¹ * ρ * G = reflDiag F 3 := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP F p := h.charP
  have hchar : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
  set σ := frameBar h with hσ
  set R := (ρ : Matrix (Fin 4) (Fin 4) F) with hR
  set Vp := LinearMap.ker (toLin' R - 1) with hVp
  set Vm := LinearMap.ker (toLin' R + 1) with hVm
  have hc : IsCompl Vp Vm := isCompl_eigenspaces hchar hρ
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  rw [finrank_fin_fun] at hsum
  have hdimm : finrank F Vm = 1 := by omega
  have memp : ∀ x, x ∈ Vp ↔ R *ᵥ x = x := by
    intro x
    simp [hVp, LinearMap.mem_ker, toLin'_apply, sub_eq_zero]
  have memm : ∀ x, x ∈ Vm ↔ R *ᵥ x = -x := by
    intro x
    simp [hVm, LinearMap.mem_ker, toLin'_apply, add_eq_zero_iff_eq_neg]
  set B := matrixForm σ ((1 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hB
  have hBapp : ∀ x y, B x y = herm σ x y := by
    intro x y
    rw [hB, matrixForm_apply, Units.val_one, Matrix.one_mulVec]
  have hsq : σ ^ 2 = 1 := frameBar_sq h
  have hne : σ ≠ 1 := frameBar_ne_one h
  have hBsymm : B.IsSymm := matrixForm_isSymm σ hsq _ (by rw [Units.val_one]; exact conjTr_one σ)
  have hBnd : B.Nondegenerate := matrixForm_nondegenerate σ 1
  have hadj : ∀ x y, herm σ (R *ᵥ x) (R *ᵥ y) = herm σ x y := by
    intro x y
    rw [herm_matrix_adjoint σ R x (R *ᵥ y), mulVec_mulVec, hu, one_mulVec]
  have hortho1 : ∀ x ∈ Vp, ∀ y ∈ Vm, B x y = 0 := by
    intro x hx y hy
    have := hadj x y
    rw [(memp x).1 hx, (memm y).1 hy, herm_neg_right] at this
    rw [hBapp]
    have h3 : (2 : F) * herm σ x y = 0 := by linear_combination -this
    exact (mul_eq_zero.1 h3).resolve_left h2
  have hortho2 : ∀ x ∈ Vm, ∀ y ∈ Vp, B x y = 0 := by
    intro x hx y hy
    have := hadj x y
    rw [(memp y).1 hy, (memm x).1 hx, herm_neg_left] at this
    rw [hBapp]
    have h3 : (2 : F) * herm σ x y = 0 := by linear_combination -this
    exact (mul_eq_zero.1 h3).resolve_left h2
  have hBp := nondeg_restrict hBnd hc hortho1 hortho2
  have hBm := nondeg_restrict hBnd hc.symm hortho2 hortho1
  obtain ⟨bp, hbp⟩ := exists_orthonormal_basis (B.domRestrict₁₂ Vp Vp) (isSymm_restrict hBsymm Vp) hBp
    hsq hne
  obtain ⟨bm, hbm⟩ := exists_orthonormal_basis (B.domRestrict₁₂ Vm Vm) (isSymm_restrict hBsymm Vm) hBm
    hsq hne
  have hbp' : ∀ i j, B (bp i : Fin 4 → F) (bp j : Fin 4 → F) = if i = j then 1 else 0 :=
    fun i j => hbp i j
  have hbm' : ∀ i j, B (bm i : Fin 4 → F) (bm j : Fin 4 → F) = if i = j then 1 else 0 :=
    fun i j => hbm i j
  set bp3 : Basis (Fin 3) F Vp := bp.reindex (finCongr hdim) with hbp3
  set bm1 : Basis (Fin 1) F Vm := bm.reindex (finCongr hdimm) with hbm1
  have hbp3o : ∀ i j, B (bp3 i : Fin 4 → F) (bp3 j : Fin 4 → F) = if i = j then 1 else 0 := by
    intro i j
    have := hbp' ((finCongr hdim).symm i) ((finCongr hdim).symm j)
    simpa [hbp3, Basis.reindex_apply, (finCongr hdim).symm.injective.eq_iff] using this
  have hbm1o : ∀ i j, B (bm1 i : Fin 4 → F) (bm1 j : Fin 4 → F) = if i = j then 1 else 0 := by
    intro i j
    have := hbm' ((finCongr hdimm).symm i) ((finCongr hdimm).symm j)
    simpa [hbm1, Basis.reindex_apply, (finCongr hdimm).symm.injective.eq_iff] using this
  let colV : Fin 4 → (Fin 4 → F) := fun j =>
    if hj : j.val < 3 then ((bp3 ⟨j.val, hj⟩ : Vp) : Fin 4 → F) else ((bm1 0 : Vm) : Fin 4 → F)
  have hcolp : ∀ j : Fin 4, j.val < 3 → colV j ∈ Vp := by
    intro j hj
    simp only [colV, hj, dite_true]
    exact (bp3 ⟨j.val, hj⟩).2
  have hcolm : ∀ j : Fin 4, ¬ j.val < 3 → colV j ∈ Vm := by
    intro j hj
    simp only [colV, hj, dite_false]
    exact (bm1 0).2
  set g : Matrix (Fin 4) (Fin 4) F := Matrix.of fun i j => colV j i with hg
  have hgram : ∀ a b, (conjTr σ g * g) a b = herm σ (colV a) (colV b) := by
    intro a b
    simp [conjTr, Matrix.mul_apply, herm, hg]
  have hg1 : conjTr σ g * g = 1 := by
    ext a b
    rw [hgram, Matrix.one_apply]
    by_cases ha : a.val < 3
    · by_cases hb : b.val < 3
      · have e1 : colV a = (bp3 ⟨a.val, ha⟩ : Fin 4 → F) := by simp [colV, ha]
        have e2 : colV b = (bp3 ⟨b.val, hb⟩ : Fin 4 → F) := by simp [colV, hb]
        rw [e1, e2, ← hBapp, hbp3o]
        by_cases hab : a = b
        · subst hab; simp
        · have : (⟨a.val, ha⟩ : Fin 3) ≠ ⟨b.val, hb⟩ := fun e =>
            hab (Fin.ext (by simpa using congrArg Fin.val e))
          simp [hab, this]
      · rw [← hBapp, hortho1 _ (hcolp a ha) _ (hcolm b hb)]
        have : a ≠ b := fun e => hb (e ▸ ha)
        simp [this]
    · by_cases hb : b.val < 3
      · rw [← hBapp, hortho2 _ (hcolm a ha) _ (hcolp b hb)]
        have : a ≠ b := fun e => ha (e ▸ hb)
        simp [this]
      · have e1 : colV a = (bm1 0 : Fin 4 → F) := by simp [colV, ha]
        have e2 : colV b = (bm1 0 : Fin 4 → F) := by simp [colV, hb]
        have hab : a = b := by
          apply Fin.ext
          have := a.2
          have := b.2
          omega
        subst hab
        rw [e1, ← hBapp, hbm1o]
        simp
  set d : Fin 4 → F := fun j => if j = 3 then -1 else 1 with hd
  have hRcol : ∀ j, R *ᵥ colV j = d j • colV j := by
    intro j
    by_cases hj : j.val < 3
    · have hj3 : j ≠ 3 := fun e => by subst e; simp at hj
      rw [(memp _).1 (hcolp j hj)]
      simp [hd, hj3]
    · have hj3 : j = 3 := by
        apply Fin.ext
        have := j.2
        simp
        omega
      rw [(memm _).1 (hcolm j hj)]
      simp [hd, hj3]
  have hg2 : R * g = g * Matrix.diagonal d := by
    ext i j
    have h1 : (R * g) i j = (R *ᵥ colV j) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hg]
    rw [h1, hRcol j, Matrix.mul_diagonal, Pi.smul_apply, smul_eq_mul, mul_comm]
    rfl
  have hgg : g * conjTr σ g = 1 := mul_eq_one_comm.1 hg1
  refine ⟨⟨g, conjTr σ g, hgg, hg1⟩, hg1, ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  change conjTr σ g * R * g = reflDiagMat F 3
  rw [Matrix.mul_assoc, hg2, ← Matrix.mul_assoc, hg1, Matrix.one_mul]
  rfl


theorem exists_unitaryFieldData {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2)
    (hq : q % 4 = 1) : ∃ p f : ℕ, UnitaryFieldData p f F ∧ q = p ^ f ∧ p ≠ 2 := by
  obtain ⟨p, f, hp, hchar, rfl⟩ := exists_prime_pow_of_card_eq_sq hF
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (Nat.odd_iff.2 (by omega : p ^ f % 2 = 1)).pow
  have hp2 : p ≠ 2 := prime_ne_two_of_odd_card (F := F) (p := p) hodd
  have hf : 1 ≤ f := by
    by_contra hf0
    have hf0' : f = 0 := by omega
    subst hf0'
    simp at hF
    have : 1 < Nat.card F := Finite.one_lt_card
    omega
  exact ⟨p, f, ⟨hp.out, hf, by rw [hF, ← pow_mul, mul_comm]⟩, rfl, hp2⟩

theorem exists_refl_conj_uni [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2) (hq : q % 4 = 1)
    {ρ : GL (Fin 4) F} (hρ : ρ * ρ = 1) (hdet : (ρ : Matrix (Fin 4) (Fin 4) F).det = -1)
    (hnorm : ∀ k ∈ StatedSU 4 q F, ρ * k * ρ⁻¹ ∈ StatedSU 4 q F) :
    ∃ (ρ' P : GL (Fin 4) F), (ρ' = ρ ∨ ρ' = -ρ) ∧ P⁻¹ * ρ' * P = reflDiag F 3 ∧
      (∀ k ∈ StatedSU 4 q F, P⁻¹ * k * P ∈ StatedSU 4 q F) ∧
      (∀ k ∈ StatedSU 4 q F, P * k * P⁻¹ ∈ StatedSU 4 q F) := by
  obtain ⟨p, f, h, rfl, hp2⟩ := exists_unitaryFieldData hF hq
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP F p := h.charP
  have hchar : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
  obtain ⟨ρ', P, hρ', hP, hdim⟩ := exists_refl_conj hchar hρ hdet
  have hnorm' : ∀ k ∈ StatedSU 4 (p ^ f) F, ρ' * k * ρ'⁻¹ ∈ StatedSU 4 (p ^ f) F := by
    intro k hk
    rcases hρ' with rfl | rfl
    · exact hnorm k hk
    · rw [neg_conj_eq]
      exact hnorm k hk
  have hρ'2 : ρ' * ρ' = 1 := by
    rcases hρ' with rfl | rfl
    · exact hρ
    · rw [neg_mul_neg]
      exact hρ
  have hρ'm : (ρ' : Matrix (Fin 4) (Fin 4) F) * ρ' = 1 := by
    rw [← Units.val_mul, hρ'2, Units.val_one]
  have htr : Matrix.trace (ρ' : Matrix (Fin 4) (Fin 4) F) = 2 := by
    have h1 : Matrix.trace ((P⁻¹ * ρ' * P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 2 := by
      rw [hP]
      change Matrix.trace (reflDiagMat F 3) = 2
      simp [Matrix.trace, reflDiagMat, Fin.sum_univ_four]
      norm_num
    rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.one_mul] at h1
    exact h1
  obtain ⟨c, hc⟩ := eq_scalar_of_commute h hp2 (fun A hA => commute_of_normalizes h hnorm' hA)
  have hc1 : c = 1 := scalar_eq_one_of_trace h h2 hρ'm htr hc
  have hu : conjTr (frameBar h) (ρ' : Matrix (Fin 4) (Fin 4) F) * (ρ' : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [hc, hc1, one_smul]
  obtain ⟨G, hG1, hG2⟩ := exists_unitary_diag h hp2 hρ'm hu hdim
  refine ⟨ρ', G, hρ', hG2, fun k hk => unitary_conj_mem h hG1 hk, fun k hk => ?_⟩
  have hGinv : ((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      conjTr (frameBar h) (G : Matrix (Fin 4) (Fin 4) F) := Units.inv_eq_of_mul_eq_one_left hG1
  have hG1' : conjTr (frameBar h) ((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      ((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [hGinv, conjTr_conjTr]
    exact mul_eq_one_comm.1 hG1
  have := unitary_conj_mem h hG1' hk
  rwa [inv_inv] at this

theorem exists_refl_unitary [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2) (hq : q % 4 = 1)
    {ρ : GL (Fin 4) F} (hρ : ρ * ρ = 1) (hdet : (ρ : Matrix (Fin 4) (Fin 4) F).det = -1)
    (hnorm : ∀ k ∈ StatedSU 4 q F, ρ * k * ρ⁻¹ ∈ StatedSU 4 q F) :
    ∃ ρ' : GL (Fin 4) F, (ρ' = ρ ∨ ρ' = -ρ) ∧
      (((ρ' : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map (fun x : F => x ^ q))ᵀ *
        ((ρ' : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
  obtain ⟨p, f, h, rfl, hp2⟩ := exists_unitaryFieldData hF hq
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP F p := h.charP
  have hchar : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
  obtain ⟨ρ', P, hρ', hP, hdim⟩ := exists_refl_conj hchar hρ hdet
  have hnorm' : ∀ k ∈ StatedSU 4 (p ^ f) F, ρ' * k * ρ'⁻¹ ∈ StatedSU 4 (p ^ f) F := by
    intro k hk
    rcases hρ' with rfl | rfl
    · exact hnorm k hk
    · rw [neg_conj_eq]
      exact hnorm k hk
  have hρ'2 : ρ' * ρ' = 1 := by
    rcases hρ' with rfl | rfl
    · exact hρ
    · rw [neg_mul_neg]
      exact hρ
  have hρ'm : (ρ' : Matrix (Fin 4) (Fin 4) F) * ρ' = 1 := by
    rw [← Units.val_mul, hρ'2, Units.val_one]
  have htr : Matrix.trace (ρ' : Matrix (Fin 4) (Fin 4) F) = 2 := by
    have h1 : Matrix.trace ((P⁻¹ * ρ' * P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 2 := by
      rw [hP]
      change Matrix.trace (reflDiagMat F 3) = 2
      simp [Matrix.trace, reflDiagMat, Fin.sum_univ_four]
      norm_num
    rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.one_mul] at h1
    exact h1
  obtain ⟨c, hc⟩ := eq_scalar_of_commute h hp2 (fun A hA => commute_of_normalizes h hnorm' hA)
  have hc1 : c = 1 := scalar_eq_one_of_trace h h2 hρ'm htr hc
  refine ⟨ρ', hρ', ?_⟩
  have hu : conjTr (frameBar h) (ρ' : Matrix (Fin 4) (Fin 4) F) * (ρ' : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [hc, hc1, one_smul]
  exact hu

end CFSG.GH74.Generic.S1.FrameUni
