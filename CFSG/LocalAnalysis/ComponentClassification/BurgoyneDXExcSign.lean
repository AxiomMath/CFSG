module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXExcEig
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOPairNorm
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOThree

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX

open Module Matrix CFSG
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat reflGL compInd
  commute_compInd_iff)
open scoped commutatorElement

variable {K : Type} [Field K] {d : ℕ}

theorem finrank_negE_signMat (h2 : (2 : K) ≠ 0) (T : Finset (Fin d)) :
    finrank K (negE (signMat K T)) = T.card := by
  have hmem : ∀ v : Fin d → K, v ∈ negE (signMat K T) ↔ ∀ i, i ∉ T → v i = 0 := by
    intro v
    rw [mem_negE]
    constructor
    · intro h i hi
      have e := congrFun h i
      simp only [signMat, mulVec_diagonal, hi, ↓reduceIte, one_mul, Pi.neg_apply] at e
      have h2v : (2 : K) * v i = 0 := by linear_combination e
      exact (mul_eq_zero.1 h2v).resolve_left h2
    · intro h
      funext i
      simp only [signMat, mulVec_diagonal, Pi.neg_apply]
      by_cases hi : i ∈ T
      · simp [hi]
      · simp [hi, h i hi]
  let e : negE (signMat K T) ≃ₗ[K] (T → K) :=
    { toFun := fun v t => (v : Fin d → K) t
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun f => ⟨fun i => if h : i ∈ T then f ⟨i, h⟩ else 0,
        (hmem _).2 fun i hi => by simp [hi]⟩
      left_inv := fun v => by
        apply Subtype.ext
        funext i
        by_cases hi : i ∈ T
        · simp [hi]
        · simp [hi, (hmem _).1 v.2 i hi]
      right_inv := fun f => by
        funext t
        simp [t.2] }
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]

theorem finrank_negE_conj (P : GL (Fin d) K) (X : Matrix (Fin d) (Fin d) K) :
    finrank K (negE ((P : Matrix (Fin d) (Fin d) K) * X * ((P⁻¹ : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K))) = finrank K (negE X) := by
  set Pm := (P : Matrix (Fin d) (Fin d) K) with hPm
  set Pi := ((P⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) with hPi
  have hPPi : Pm * Pi = 1 := by rw [hPm, hPi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPiP : Pi * Pm = 1 := by rw [hPm, hPi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hinj : Function.Injective (Matrix.toLin' Pm) := by
    intro x y h
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply] at h
    have := congrArg (fun z => Pi *ᵥ z) h
    simpa [mulVec_mulVec, hPiP] using this
  have hmap : negE (Pm * X * Pi) = (negE X).map (Matrix.toLin' Pm) := by
    ext v
    rw [Submodule.mem_map]
    constructor
    · intro hv
      refine ⟨Pi *ᵥ v, ?_, ?_⟩
      · rw [mem_negE] at hv ⊢
        have := congrArg (fun z => Pi *ᵥ z) hv
        simp only [mulVec_mulVec, mulVec_neg] at this
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPiP, Matrix.one_mul] at this
        rw [mulVec_mulVec]
        exact this
      · rw [Matrix.toLin'_apply, mulVec_mulVec, hPPi, one_mulVec]
    · rintro ⟨x, hx, rfl⟩
      rw [mem_negE] at hx ⊢
      rw [Matrix.toLin'_apply, mulVec_mulVec, Matrix.mul_assoc (Pm * X), hPiP, Matrix.mul_one,
        ← mulVec_mulVec, hx, mulVec_neg]
  rw [hmap]
  exact (Submodule.equivMapOfInjective _ hinj (negE X)).finrank_eq.symm

theorem det_blkEquiv_diagonal (n : ℕ) (f : Fin n → Matrix (Fin 2) (Fin 2) K) :
    (blkEquiv K n (diagonal f)).det = ∏ i, (f i).det := by
  have e : blkEquiv K n (diagonal f) = reindex (pairEquiv n) (pairEquiv n)
      (reindex (Equiv.prodComm (Fin 2) (Fin n)) (Equiv.prodComm (Fin 2) (Fin n))
        (blockDiagonal f)) := by
    ext p q
    obtain ⟨⟨i, j⟩, rfl⟩ := (pairEquiv n).surjective p
    obtain ⟨⟨k, l⟩, rfl⟩ := (pairEquiv n).surjective q
    rw [blkEquiv_apply, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply, reindex_apply, submatrix_apply, Equiv.prodComm_symm,
      Equiv.prodComm_apply, Equiv.prodComm_apply, Prod.swap_prod_mk, Prod.swap_prod_mk,
      blockDiagonal_apply, diagonal_apply]
    by_cases hik : i = k
    · subst hik
      simp
    · simp [hik]
  rw [e, det_reindex_self, det_reindex_self, det_blockDiagonal]

theorem isSquare_prod_of_skew [Finite K] (hK : ringChar K ≠ 2) {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0) {I : Finset (Fin d)} (hI : I.card = 4) {A : Matrix (Fin d) (Fin d) K}
    (hAc : compInd K I * A = A * compInd K I) (hAR : Aᵀ * diagonal w = -(diagonal w * A))
    {a₀ : K} (ha₀ : a₀ ≠ 0) (hA2 : A * A = a₀ • 1) : IsSquare (∏ i ∈ I, w i) := by
  have hblk := (commute_compInd_iff I A).1 hAc
  set e : Fin (2 * 2) ≃ I := (I.equivFinOfCardEq hI).symm with he
  set ι : Fin (2 * 2) → Fin d := fun x => (e x : Fin d) with hι
  have hιI : ∀ x, ι x ∈ I := fun x => (e x).2
  have hιinj : Function.Injective ι := fun x y h => e.injective (Subtype.ext h)
  set A₄ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K := Matrix.of fun x y => A (ι x) (ι y) with hA₄
  set w₄ : Fin (2 * 2) → K := fun x => w (ι x) with hw₄
  have hw₄0 : ∀ x, w₄ x ≠ 0 := fun x => hw _
  have hsum : ∀ x y, ∑ z, A (ι x) (ι z) * A (ι z) (ι y) = (A * A) (ι x) (ι y) := by
    intro x y
    have hzero : ∀ k ∈ (Finset.univ : Finset (Fin d)), k ∉ I → A (ι x) k * A k (ι y) = 0 := by
      intro k _ hk
      rw [hblk (ι x) k (by simp [hιI x, hk]), zero_mul]
    rw [Matrix.mul_apply]
    calc ∑ z, A (ι x) (ι z) * A (ι z) (ι y) = ∑ k : I, A (ι x) k * A k (ι y) :=
          Equiv.sum_comp e (fun k : I => A (ι x) (k : Fin d) * A (k : Fin d) (ι y))
      _ = ∑ k ∈ I, A (ι x) k * A k (ι y) :=
          Finset.sum_coe_sort I (fun k => A (ι x) k * A k (ι y))
      _ = ∑ k, A (ι x) k * A k (ι y) := Finset.sum_subset (Finset.subset_univ I) hzero
  have hprod : ∏ x, w₄ x = ∏ i ∈ I, w i := by
    calc ∏ x, w₄ x = ∏ k : I, w k := Equiv.prod_comp e (fun k : I => w (k : Fin d))
      _ = ∏ i ∈ I, w i := Finset.prod_coe_sort I w
  have hA₄2 : A₄ * A₄ = a₀ • (1 : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K) := by
    ext x y
    rw [Matrix.mul_apply]
    simp only [hA₄, Matrix.of_apply]
    rw [hsum x y, hA2, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
    by_cases hxy : x = y
    · subst hxy
      simp
    · simp [hxy, hιinj.ne hxy]
  have hA₄R : A₄ᵀ * ((diagGL hw₄0 : GL (Fin (2 * 2)) K) : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K) =
      (-1 : K) • (((diagGL hw₄0 : GL (Fin (2 * 2)) K) : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K) *
        A₄) := by
    rw [coe_diagGL]
    ext x y
    have h := congrFun (congrFun hAR (ι x)) (ι y)
    simp only [mul_diagonal, diagonal_mul, transpose_apply, Matrix.neg_apply] at h
    simp only [mul_diagonal, diagonal_mul, transpose_apply, Matrix.smul_apply, hA₄,
      Matrix.of_apply, smul_eq_mul, hw₄]
    linear_combination h
  obtain ⟨H, hH, -⟩ := exists_pc_basis hK (R := diagGL hw₄0) (diagGL_transpose hw₄0) ha₀ hA₄2
    hA₄R (fun _ => (1 : K)) (fun _ => one_ne_zero)
  have hdet := congrArg Matrix.det hH
  rw [det_mul, det_mul, det_transpose, coe_diagGL, det_diagonal, det_blkEquiv_diagonal] at hdet
  have hwdet : ((1 : K) • wMat 1 (-a₀)).det = -a₀ := by
    rw [one_smul, wMat, det_diagonal, Fin.prod_univ_two]
    simp
  simp only [Fin.prod_univ_two] at hdet
  rw [hwdet] at hdet
  have hHd : (H : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K).det ≠ 0 :=
    (Matrix.isUnits_det_units H).ne_zero
  refine ⟨a₀ / (H : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K).det, ?_⟩
  rw [← hprod]
  field_simp
  linear_combination hdet

theorem signGL_pair_mem_oBlock_sq {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {J : Finset (Fin d)}
    {i j : Fin d} (hi : i ∈ J) (hj : j ∈ J) (hij : i ≠ j) {r : K} (hr : r ≠ 0)
    (hwr : w j = r ^ 2 * w i) : signGL K {i, j} ∈ oBlock K hw J := by
  set σ : Equiv.Perm (Fin d) := Equiv.swap i j with hσ
  have hσσ : ∀ x, σ (σ x) = x := fun x => Equiv.swap_apply_self i j x
  have hσeq : ∀ x y, σ x = y ↔ x = σ y := fun x y =>
    ⟨fun h => by rw [← h, hσσ], fun h => by rw [h, hσσ]⟩
  set dv : Fin d → K := fun k => (if k = i then r⁻¹ else 1) * (if k = j then -r else 1) with hdv
  set f : Matrix (Fin d) (Fin d) K := (diagonal dv).submatrix σ id with hf
  have hfa : ∀ x y, f x y = if σ x = y then dv (σ x) else 0 := by
    intro x y
    rw [hf, submatrix_apply, diagonal_apply]
    rfl
  have hdet : f.det = 1 := by
    rw [hf, det_permute, det_diagonal, hσ, Equiv.Perm.sign_swap hij, hdv,
      Finset.prod_mul_distrib, Fintype.prod_ite_eq', Fintype.prod_ite_eq']
    field_simp
    simp
  set fGL : GL (Fin d) K := Matrix.nonsingInvUnit f (isUnit_iff_ne_zero.2 (by
    rw [hdet]
    exact one_ne_zero)) with hfGL
  have hfGLv : ((fGL : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = f := rfl
  have hiso : fGL ∈ CatalogueBGraphForm.isometryGroup d K (diagGL hw) := by
    rw [CatalogueBGraphForm.mem_isometryGroup, hfGLv, coe_diagGL]
    ext x y
    rw [Matrix.mul_apply]
    simp only [mul_diagonal, transpose_apply]
    rw [Finset.sum_eq_single (σ x)]
    · rw [hfa, hfa, hσσ, diagonal_apply]
      simp only [↓reduceIte]
      by_cases hxy : x = y
      · subst hxy
        simp only [↓reduceIte, hdv]
        by_cases hxi : x = i
        · subst hxi
          simp [hσ, Equiv.swap_apply_left, hij, hwr]
          field_simp
        · by_cases hxj : x = j
          · subst hxj
            simp [hσ, Equiv.swap_apply_right, hxi, hwr]
            ring
          · simp [hσ, Equiv.swap_apply_of_ne_of_ne hxi hxj, hxi, hxj]
      · simp [hxy]
    · intro k _ hk
      rw [hfa k x]
      have : σ k ≠ x := fun h => hk ((hσeq k x).1 h)
      simp [this]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hfJ : fGL ∈ oIsoBlock K hw J := by
    rw [mem_oIsoBlock_iff]
    refine ⟨hiso, fun x y hxy => ?_⟩
    rw [hfGLv, hfa]
    have hgen : ∀ z, z ∉ J → σ z = z ∧ dv z = 1 := by
      intro z hz
      have hzi : z ≠ i := fun h => hz (h ▸ hi)
      have hzj : z ≠ j := fun h => hz (h ▸ hj)
      exact ⟨Equiv.swap_apply_of_ne_of_ne hzi hzj, by simp [hdv, hzi, hzj]⟩
    rcases hxy with hx | hy
    · obtain ⟨h1, h2⟩ := hgen x hx
      rw [h1, h2]
    · obtain ⟨h1, h2⟩ := hgen y hy
      by_cases hxy : σ x = y
      · have hxy' : x = y := by rw [(hσeq x y).1 hxy, h1]
        rw [ite_eq_left hxy, ite_eq_left hxy', hxy, h2]
      · have hxy' : x ≠ y := fun h => hxy (by rw [h, h1])
        rw [ite_eq_right hxy, ite_eq_right hxy']
  have hfr : f * signMat K {i} = signMat K {j} * f := by
    ext x y
    rw [signMat, signMat, mul_diagonal, diagonal_mul, hfa]
    by_cases hxy : σ x = y
    · rw [ite_eq_left hxy, ← hxy]
      have hc : σ x ∈ ({i} : Finset (Fin d)) ↔ x ∈ ({j} : Finset (Fin d)) := by
        rw [Finset.mem_singleton, Finset.mem_singleton, hσeq, hσ, Equiv.swap_apply_left]
      by_cases hx : x ∈ ({j} : Finset (Fin d))
      · rw [ite_eq_left (hc.2 hx), ite_eq_left hx]
        ring
      · rw [ite_eq_right (fun h => hx (hc.1 h)), ite_eq_right hx]
        ring
    · simp [hxy]
  have hcomm : ⁅reflGL (K := K) i, fGL⁆ = signGL K {i, j} := by
    apply Units.ext
    have hri : ((reflGL (K := K) i)⁻¹ : GL (Fin d) K) = reflGL i :=
      inv_eq_of_mul_eq_one_right (Units.ext (PSL.signMat_mul_self _))
    have hff : (f * ((fGL⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) = 1 := by
      rw [← hfGLv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [commutatorElement_def, hri, Units.val_mul, Units.val_mul, Units.val_mul, hfGLv]
    change signMat K {i} * f * signMat K {i} * ((fGL⁻¹ : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = signMat K {i, j}
    rw [Matrix.mul_assoc (signMat K {i}) f, hfr, ← Matrix.mul_assoc, Matrix.mul_assoc _ f, hff,
      Matrix.mul_one, signMat_mul_of_disjoint (Finset.disjoint_singleton.2 hij)]
    rfl
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator (reflGL_mem_oIsoBlock hw hi) hfJ

end CFSG.ComponentClassification.Burgoyne.DX
