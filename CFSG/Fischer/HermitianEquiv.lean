module

public import CFSG.Fischer.HermitianBasis
public import CFSG.Fischer.UnitaryTransport
public import CFSG.Fischer.Pairs
import all CFSG.Fischer.F4

public section

namespace CFSG.Fischer

open Matrix Blueprint.Fischer

theorem K_pow_four (c : K) : c ^ 4 = c := by
  obtain ⟨c0, rfl⟩ := ψ.surjective c
  rw [← map_pow]
  congr 1
  revert c0
  decide

theorem K_sq_add (a b : K) : (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
  obtain ⟨a0, rfl⟩ := ψ.surjective a
  obtain ⟨b0, rfl⟩ := ψ.surjective b
  rw [← map_add, ← map_pow, ← map_pow, ← map_pow, ← map_add]
  congr 1
  revert a0 b0
  decide

theorem K_sq_sum {ι : Type*} (s : Finset ι) (f : ι → K) :
    (∑ i ∈ s, f i) ^ 2 = ∑ i ∈ s, f i ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, K_sq_add, ih]

theorem hermitian_add_left (H : Matrix (Fin 6) (Fin 6) K) (x x' y : V) :
    hermitian H (x + x') y = hermitian H x y + hermitian H x' y := by
  simp only [hermitian, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem hermitian_smul_left (H : Matrix (Fin 6) (Fin 6) K) (c : K) (x y : V) :
    hermitian H (c • x) y = c * hermitian H x y := by
  simp only [hermitian, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem hermitian_swap {H : Matrix (Fin 6) (Fin 6) K} (hH : IsNondegenerateHermitian H)
    (x y : V) : hermitian H y x = (hermitian H x y) ^ 2 := by
  unfold hermitian
  rw [K_sq_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [K_sq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow, mul_pow, ← hH.1, ← pow_mul, K_pow_four]
  ring

@[expose] noncomputable def formOf (H : Matrix (Fin 6) (Fin 6) K) (x y : W) : F4 :=
  ψ.symm (hermitian H (ψV x) (ψV y))

theorem hform_formOf {H : Matrix (Fin 6) (Fin 6) K} (hH : IsNondegenerateHermitian H) :
    HForm (formOf H) where
  add_left x x' y := by
    unfold formOf
    rw [show ψV (x + x') = ψV x + ψV x' by funext i; simp [ψV], hermitian_add_left, map_add]
  smul_left c x y := by
    unfold formOf
    rw [show ψV (c • x) = ψ c • ψV x by funext i; simp [ψV], hermitian_smul_left, map_mul,
      RingEquiv.symm_apply_apply]
  swap x y := by
    unfold formOf
    rw [hermitian_swap hH, map_pow]
  nondeg x hx := by
    apply ψV_injective
    rw [show ψV 0 = 0 by funext i; simp [ψV]]
    apply hH.2
    intro y
    obtain ⟨y0, rfl⟩ := ψV_surjective y
    have := hx y0
    unfold formOf at this
    rw [← map_zero ψ.symm] at this
    exact ψ.symm.injective this

@[expose] def colMat (b : Fin 6 → W) : Matrix (Fin 6) (Fin 6) F4 := Matrix.of fun i j => b j i

theorem colMat_mulVec (b : Fin 6 → W) (x : W) : (colMat b).mulVec x = ∑ j, x j • b j := by
  funext i
  simp only [colMat, mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, mul_comm]

theorem hermStd_single (v : W) (j : Fin 6) : hermStd v (Pi.single j 1) = v j := by
  unfold hermStd
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij; simp [hij]
  · simp

section Basis

variable {H : Matrix (Fin 6) (Fin 6) K} (hH : IsNondegenerateHermitian H) {b : Fin 6 → W}
  (hb : ∀ i j, formOf H (b i) (b j) = if i = j then 1 else 0)
include hH hb

theorem formOf_colMat (x y : W) :
    formOf H ((colMat b).mulVec x) ((colMat b).mulVec y) = hermStd x y := by
  have hf := hform_formOf hH
  rw [colMat_mulVec, colMat_mulVec, hf.sum_left]
  simp only [hf.sum_right, hb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, hermStd]

theorem colMat_det_ne_zero : (colMat b).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  apply hv0
  funext j
  have := formOf_colMat hH hb v (Pi.single j 1)
  rw [hv, (hform_formOf hH).zero_left, hermStd_single] at this
  exact this.symm

end Basis

theorem exists_isometry {H : Matrix (Fin 6) (Fin 6) K} (hH : IsNondegenerateHermitian H) :
    ∃ A : GL (Fin 6) K, ∀ x y : V,
      hermitian H ((A : Matrix (Fin 6) (Fin 6) K).mulVec x)
        ((A : Matrix (Fin 6) (Fin 6) K).mulVec y) = hermitian 1 x y := by
  obtain ⟨b, hb⟩ := (hform_formOf hH).exists_orthonormal
  refine ⟨ψGL (Matrix.GeneralLinearGroup.mkOfDetNeZero (colMat b) (colMat_det_ne_zero hH hb)),
    fun x y => ?_⟩
  obtain ⟨x0, rfl⟩ := ψV_surjective x
  obtain ⟨y0, rfl⟩ := ψV_surjective y
  rw [ψGL_val, mulVec_ψ, mulVec_ψ, hermitian_ψ, herm_eq_std]
  have := formOf_colMat hH hb x0 y0
  unfold formOf at this
  rw [← this, RingEquiv.apply_symm_apply]
  rfl

section Conj

variable {H : Matrix (Fin 6) (Fin 6) K} {A : GL (Fin 6) K}
  (hA : ∀ x y : V, hermitian H ((A : Matrix (Fin 6) (Fin 6) K).mulVec x)
    ((A : Matrix (Fin 6) (Fin 6) K).mulVec y) = hermitian 1 x y)
include hA

omit hA in
theorem mulVec_inv_mulVec_K (g : GL (Fin 6) K) (x : V) :
    (g : Matrix (Fin 6) (Fin 6) K).mulVec (((g⁻¹ : GL (Fin 6) K) : Matrix _ _ K).mulVec x) = x := by
  rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

omit hA in
theorem inv_mulVec_mulVec_K (g : GL (Fin 6) K) (x : V) :
    (((g⁻¹ : GL (Fin 6) K) : Matrix _ _ K)).mulVec
      ((g : Matrix (Fin 6) (Fin 6) K).mulVec x) = x := by
  rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

theorem hermitian_inv (x y : V) :
    hermitian 1 (((A⁻¹ : GL (Fin 6) K) : Matrix _ _ K).mulVec x)
      (((A⁻¹ : GL (Fin 6) K) : Matrix _ _ K).mulVec y) = hermitian H x y := by
  have := hA (((A⁻¹ : GL (Fin 6) K) : Matrix _ _ K).mulVec x)
    (((A⁻¹ : GL (Fin 6) K) : Matrix _ _ K).mulVec y)
  rw [mulVec_inv_mulVec_K, mulVec_inv_mulVec_K] at this
  exact this.symm

theorem conj_image_gen :
    (MulAut.conj A) '' {g : GL (Fin 6) K | Matrix.GeneralLinearGroup.det g = 1 ∧
      ∀ x y : V, hermitian 1 ((g : Matrix (Fin 6) (Fin 6) K).mulVec x)
        ((g : Matrix (Fin 6) (Fin 6) K).mulVec y) = hermitian 1 x y} =
    {g : GL (Fin 6) K | Matrix.GeneralLinearGroup.det g = 1 ∧
      ∀ x y : V, hermitian H ((g : Matrix (Fin 6) (Fin 6) K).mulVec x)
        ((g : Matrix (Fin 6) (Fin 6) K).mulVec y) = hermitian H x y} := by
  ext g
  constructor
  · rintro ⟨g0, ⟨hdet, hiso⟩, rfl⟩
    refine ⟨by simp [MulAut.conj_apply, hdet], fun x y => ?_⟩
    simp only [MulAut.conj_apply, Units.val_mul, ← mulVec_mulVec]
    rw [hA, hiso, hermitian_inv hA]
  · rintro ⟨hdet, hiso⟩
    refine ⟨A⁻¹ * g * A, ⟨by simp [hdet], fun x y => ?_⟩, by simp [MulAut.conj_apply, mul_assoc]⟩
    simp only [Units.val_mul, ← mulVec_mulVec]
    rw [hermitian_inv hA, hiso, hA]

theorem map_SU : (SU (1 : Matrix (Fin 6) (Fin 6) K)).map (MulAut.conj A).toMonoidHom = SU H := by
  unfold SU
  rw [MonoidHom.map_closure]
  congr 1
  exact conj_image_gen hA

@[expose] noncomputable def suEquivOf : SU (1 : Matrix (Fin 6) (Fin 6) K) ≃* SU H :=
  ((SU 1).equivMapOfInjective (MulAut.conj A).toMonoidHom (MulAut.conj A).injective).trans
    (MulEquiv.subgroupCongr (map_SU hA))

theorem suEquivOf_val (u : SU (1 : Matrix (Fin 6) (Fin 6) K)) :
    ((suEquivOf hA u : SU H) : GL (Fin 6) K) = A * u * A⁻¹ := rfl

noncomputable def psuEquivOf : PSU (1 : Matrix (Fin 6) (Fin 6) K) ≃* PSU H :=
  quotientCenterCongr (suEquivOf hA)

theorem psuEquivOf_mk (u : SU (1 : Matrix (Fin 6) (Fin 6) K)) :
    psuEquivOf hA (QuotientGroup.mk u) = QuotientGroup.mk (suEquivOf hA u) :=
  quotientCenterCongr_mk _ _

theorem conj_tv {u : GL (Fin 6) K} {v : V}
    (hu : ∀ x, (u : Matrix (Fin 6) (Fin 6) K).mulVec x = x + hermitian 1 x v • v) (x : V) :
    ((A * u * A⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).mulVec x =
      x + hermitian H x ((A : Matrix (Fin 6) (Fin 6) K).mulVec v) •
        (A : Matrix (Fin 6) (Fin 6) K).mulVec v := by
  simp only [Units.val_mul, ← mulVec_mulVec]
  rw [hu, mulVec_add, mulVec_smul, mulVec_inv_mulVec_K]
  congr 2
  have := hA (((A⁻¹ : GL (Fin 6) K) : Matrix _ _ K).mulVec x) v
  rw [mulVec_inv_mulVec_K] at this
  exact this.symm

omit hA in
theorem mulVec_ne_zero_K (g : GL (Fin 6) K) {v : V} (hv : v ≠ 0) :
    (g : Matrix (Fin 6) (Fin 6) K).mulVec v ≠ 0 := by
  intro h
  apply hv
  rw [← inv_mulVec_mulVec_K g v, h, mulVec_zero]

set_option maxHeartbeats 2000000 in
theorem image_transvections : psuEquivOf hA '' Transvections 1 = Transvections H := by
  ext q
  constructor
  · rintro ⟨q0, ⟨u, hu0, v, hv0, hviso, hact⟩, hq⟩
    refine ⟨suEquivOf hA u, ?_, (A : Matrix _ _ K).mulVec v, mulVec_ne_zero_K A hv0, ?_, ?_⟩
    · rw [← hq, ← hu0, psuEquivOf_mk]
    · rw [hA]; exact hviso
    · intro x
      rw [suEquivOf_val]
      exact conj_tv hA hact x
  · rintro ⟨u', rfl, v', hv0, hviso, hact⟩
    set u := (suEquivOf hA).symm u' with hu
    have hu' : suEquivOf hA u = u' := by rw [hu, MulEquiv.apply_symm_apply]
    refine ⟨QuotientGroup.mk u, ⟨u, rfl, ((A⁻¹ : GL (Fin 6) K) : Matrix _ _ K).mulVec v',
      mulVec_ne_zero_K A⁻¹ hv0, by rw [hermitian_inv hA]; exact hviso, fun x => ?_⟩,
      by rw [psuEquivOf_mk, hu']⟩
    have hval : ((u : SU (1 : Matrix (Fin 6) (Fin 6) K)) : GL (Fin 6) K) =
        A⁻¹ * (u' : GL (Fin 6) K) * A := by
      rw [← hu', suEquivOf_val]; group
    rw [hval]
    simp only [Units.val_mul, ← mulVec_mulVec]
    rw [hact, mulVec_add, mulVec_smul, inv_mulVec_mulVec_K]
    congr 2
    have := hA x (((A⁻¹ : GL (Fin 6) K) : Matrix _ _ K).mulVec v')
    rw [mulVec_inv_mulVec_K] at this
    exact this

end Conj

theorem exists_psu_equiv {H : Matrix (Fin 6) (Fin 6) K} (hH : IsNondegenerateHermitian H) :
    ∃ iso : PSU (1 : Matrix (Fin 6) (Fin 6) K) ≃* PSU H,
      iso '' Transvections 1 = Transvections H := by
  obtain ⟨A, hA⟩ := exists_isometry hH
  exact ⟨psuEquivOf hA, image_transvections hA⟩

end CFSG.Fischer
