module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarCommutant

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Module Matrix CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V] {m : ℕ}

@[expose] noncomputable def basisGL (e : Basis (Fin m) E V) (M : GL (Fin m) E) :
    LinearMap.GeneralLinearGroup E V where
  val := e.equivFun.symm.toLinearMap ∘ₗ (M : Matrix (Fin m) (Fin m) E).mulVecLin ∘ₗ
    e.equivFun.toLinearMap
  inv := e.equivFun.symm.toLinearMap ∘ₗ
    ((M⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E).mulVecLin ∘ₗ e.equivFun.toLinearMap
  val_inv := LinearMap.ext fun v => by
    change e.equivFun.symm ((M : Matrix (Fin m) (Fin m) E) *ᵥ e.equivFun (e.equivFun.symm
      (((M⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ e.equivFun v))) = v
    rw [LinearEquiv.apply_symm_apply, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, one_mulVec, LinearEquiv.symm_apply_apply]
  inv_val := LinearMap.ext fun v => by
    change e.equivFun.symm (((M⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ
      e.equivFun (e.equivFun.symm ((M : Matrix (Fin m) (Fin m) E) *ᵥ e.equivFun v))) = v
    rw [LinearEquiv.apply_symm_apply, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, one_mulVec, LinearEquiv.symm_apply_apply]

theorem basisGL_apply (e : Basis (Fin m) E V) (M : GL (Fin m) E) (v : V) :
    (basisGL e M : V →ₗ[E] V) v = e.equivFun.symm ((M : Matrix (Fin m) (Fin m) E) *ᵥ
      e.equivFun v) :=
  rfl

variable (h : UnitaryFieldData p f E)

theorem hermForm_eq_gramForm_one {Hf : V →ₛₗ[h.bar] V →ₗ[E] E} (e : Basis (Fin m) E V)
    (he : ∀ i j, Hf (e i) (e j) = if i = j then 1 else 0) (x y : V) :
    Hf x y = gramForm h (1 : Matrix (Fin m) (Fin m) E) (e.equivFun x) (e.equivFun y) := by
  conv_lhs => rw [← e.sum_equivFun x, ← e.sum_equivFun y]
  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, he]
  rw [gramForm_apply, one_mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

theorem basisGL_mem {Hf : V →ₛₗ[h.bar] V →ₗ[E] E} (e : Basis (Fin m) E V)
    (he : ∀ i j, Hf (e i) (e j) = if i = j then 1 else 0) {M : GL (Fin m) E}
    (hM : M ∈ gramSU h (1 : Matrix (Fin m) (Fin m) E)) :
    basisGL e M ∈ sesqSpecialUnitaryGroup Hf := by
  refine mem_sesqSpecialUnitaryGroup.mpr ⟨mem_sesqUnitaryGroup.mpr fun x y => ?_, ?_⟩
  · rw [hermForm_eq_gramForm_one h e he, hermForm_eq_gramForm_one h e he x y, basisGL_apply,
      basisGL_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact (mem_gramSU_iff_isometry.mp hM).1 _ _
  · change LinearMap.det (e.equivFun.symm.toLinearMap ∘ₗ
      (M : Matrix (Fin m) (Fin m) E).mulVecLin ∘ₗ e.equivFun.symm.symm.toLinearMap) = 1
    rw [LinearMap.det_conj, ← Matrix.toLin'_apply', LinearMap.det_toLin']
    exact (mem_gramSU_iff_isometry.mp hM).2

theorem exists_norm_one_not_fixed (hp : p ≠ 2) : ∃ c : E, h.bar c * c = 1 ∧ c ∉ h.fixedField := by
  by_contra hall
  push Not at hall
  have hle : (Units.map h.normHom).ker ≤ rootsOfUnity 2 E := by
    intro u hu
    have hN : h.norm (u : E) = 1 := h.mem_ker_normUnits.mp hu
    have hk : h.bar (u : E) = u := h.mem_fixedField.mp
      (hall u (by rw [mul_comm]; exact hN))
    rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, sq]
    rw [UnitaryFieldData.norm, hk] at hN
    exact hN
  have h1 := Subgroup.card_le_of_le hle
  rw [h.card_ker_normUnits_and_surjective.1] at h1
  have h2 := card_rootsOfUnity E 2
  have h3 : 3 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by
      have := h.prime.two_le
      omega
    exact le_trans hp3 (Nat.le_self_pow (by have := h.one_le; omega) p)
  omega

theorem commutant_eq_scalar (hp : p ≠ 2) [FiniteDimensional E V] (hm : 3 ≤ finrank E V)
    {Hf : V →ₛₗ[h.bar] V →ₗ[E] E} (hH : Hf.IsSymm) (hnd : Hf.SeparatingLeft)
    (X : V →ₗ[h.fixedField] V)
    (hX : ∀ g ∈ sesqSpecialUnitaryGroup Hf, ∀ v,
      X ((g : V →ₗ[E] V) v) = (g : V →ₗ[E] V) (X v)) :
    ∃ a : E, ∀ v, X v = a • v := by
  have : CharP E p := h.charP
  have h2 : (2 : E) ≠ 0 := by
    intro h0
    have h3 : ((2 : ℕ) : E) = 0 := by exact_mod_cast h0
    have h4 := Nat.le_of_dvd two_pos ((CharP.cast_eq_zero_iff E p 2).mp h3)
    have := h.prime.two_le
    omega
  obtain ⟨e, he⟩ := h.exists_orthonormal_basis hH hnd
  obtain ⟨c, hcN, hck⟩ := exists_norm_one_not_fixed h hp
  set C := e.equivFun.toLinearMap.restrictScalars h.fixedField
  set Ci := e.equivFun.symm.toLinearMap.restrictScalars h.fixedField
  have hCCi : ∀ u, C (Ci u) = u := fun u => e.equivFun.apply_symm_apply u
  have hCiC : ∀ v, Ci (C v) = v := fun v => e.equivFun.symm_apply_apply v
  have hcomm : ∀ M : GL (Fin (finrank E V)) E, M ∈ gramSU h 1 → ∀ u,
      (C ∘ₗ X ∘ₗ Ci) ((M : Matrix (Fin (finrank E V)) (Fin (finrank E V)) E) *ᵥ u) =
        (M : Matrix (Fin (finrank E V)) (Fin (finrank E V)) E) *ᵥ (C ∘ₗ X ∘ₗ Ci) u := by
    intro M hM u
    have h3 := hX _ (basisGL_mem h e he hM) (Ci u)
    rw [basisGL_apply, basisGL_apply] at h3
    change C (X (Ci (_ *ᵥ u))) = _
    have h4 : e.equivFun (Ci u) = u := hCCi u
    rw [h4] at h3
    change X (Ci _) = Ci _ at h3
    rw [h3, hCCi]
    rfl
  obtain ⟨a, ha⟩ := coordinate_commutant_scalar h h2 hm hcN hck (C ∘ₗ X ∘ₗ Ci)
    (fun i l hil u => by
      obtain ⟨M, hM, hMmem⟩ := unitSignDiag_mem h hil
      have := hcomm M hMmem u
      rwa [hM] at this)
    (fun i j hij u => by
      obtain ⟨M, hM, hMmem⟩ := unitLambdaDiag_mem h hcN hij
      have := hcomm M hMmem u
      rwa [hM] at this)
    (fun i j hij u => by
      obtain ⟨M, hM, hMmem⟩ := unitSignedSwapMatrix_mem h hij
      have := hcomm M hMmem u
      rwa [hM] at this)
  refine ⟨a, fun v => ?_⟩
  have h3 := ha (C v)
  change C (X (Ci (C v))) = a • C v at h3
  rw [hCiC] at h3
  calc X v = Ci (C (X v)) := (hCiC _).symm
    _ = Ci (a • C v) := by rw [h3]
    _ = a • v := by
      change e.equivFun.symm (a • e.equivFun v) = a • v
      rw [map_smul, LinearEquiv.symm_apply_apply]

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
