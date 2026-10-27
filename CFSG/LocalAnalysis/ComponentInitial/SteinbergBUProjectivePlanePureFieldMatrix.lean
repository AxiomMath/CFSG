module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open Matrix LinearFlag

variable {K : Type*} [Field K] {n : ℕ}

@[expose] def twistedProd (σ : K ≃+* K) (M : GL (Fin n) K) : ℕ → GL (Fin n) K
  | 0 => 1
  | k + 1 => twistedProd σ M k * GeneralLinearGroup.map ((σ ^ k : K ≃+* K) : K →+* K) M

theorem twistedProd_zero (σ : K ≃+* K) (M : GL (Fin n) K) : twistedProd σ M 0 = 1 :=
  rfl

theorem twistedProd_succ (σ : K ≃+* K) (M : GL (Fin n) K) (k : ℕ) :
    twistedProd σ M (k + 1) =
      twistedProd σ M k * GeneralLinearGroup.map ((σ ^ k : K ≃+* K) : K →+* K) M :=
  rfl

theorem conjAut_mul_fieldAut_pow (σ : K ≃+* K) (M : GL (Fin n) K) (k : ℕ) :
    (conjAut n K M * fieldAut n K σ) ^ k =
      conjAut n K (twistedProd σ M k) * fieldAut n K (σ ^ k) := by
  induction k with
  | zero => rw [pow_zero, twistedProd_zero, pow_zero, map_one, map_one, mul_one]
  | succ k ih =>
    rw [pow_succ, ih, conjAut_mul_fieldAut_mul, twistedProd_succ, ← pow_succ]

theorem map_map_ringEquiv (σ τ : K ≃+* K) (A : GL (Fin n) K) :
    GeneralLinearGroup.map (σ : K →+* K) (GeneralLinearGroup.map (τ : K →+* K) A) =
      GeneralLinearGroup.map ((σ * τ : K ≃+* K) : K →+* K) A :=
  Units.ext (Matrix.ext fun _ _ => rfl)

theorem twistedProd_frame (σ : K ≃+* K) (P T : GL (Fin n) K) (k : ℕ) :
    twistedProd σ (P * T * (GeneralLinearGroup.map (σ : K →+* K) P)⁻¹) k =
      P * twistedProd σ T k * (GeneralLinearGroup.map ((σ ^ k : K ≃+* K) : K →+* K) P)⁻¹ := by
  induction k with
  | zero =>
    rw [twistedProd_zero, twistedProd_zero, pow_zero, mul_one]
    exact (mul_inv_cancel P).symm.trans (by rfl)
  | succ k ih =>
    rw [twistedProd_succ, twistedProd_succ, ih, map_mul, map_mul, map_inv, map_map_ringEquiv,
      ← pow_succ]
    group

theorem twistedProd_diagGL (σ : K ≃+* K) (t : Fin n → Kˣ) (k : ℕ) :
    twistedProd σ (TauCeti.diagGL t) k =
      TauCeti.diagGL (fun i => ∏ j ∈ Finset.range k,
        Units.map ((σ ^ j : K ≃+* K) : K →* K) (t i)) := by
  induction k with
  | zero =>
    rw [twistedProd_zero]
    refine (map_one TauCeti.diagGL).symm.trans ?_
    congr 1
  | succ k ih =>
    have hmap : GeneralLinearGroup.map ((σ ^ k : K ≃+* K) : K →+* K) (TauCeti.diagGL t) =
        TauCeti.diagGL (fun i => Units.map ((σ ^ k : K ≃+* K) : K →* K) (t i)) := by
      apply Units.ext
      ext a b
      rw [GeneralLinearGroup.map_apply, TauCeti.diagGL_coe, TauCeti.diagGL_coe]
      by_cases hab : a = b
      · subst hab
        rw [diagonal_apply_eq, diagonal_apply_eq, Units.coe_map]
        rfl
      · rw [diagonal_apply_ne _ hab, diagonal_apply_ne _ hab, map_zero]
    rw [twistedProd_succ, ih, hmap, ← map_mul]
    congr 1
    funext i
    rw [Finset.prod_range_succ]
    rfl

theorem exists_diagGL_of_commute {d : Fin n → K} (hd : Function.Injective d) (X : GL (Fin n) K)
    (h : (X : Matrix (Fin n) (Fin n) K) * diagonal d = diagonal d * X) :
    ∃ x : Fin n → Kˣ, X = TauCeti.diagGL x := by
  have hoff : ∀ i j, i ≠ j → (X : Matrix (Fin n) (Fin n) K) i j = 0 := by
    intro i j hij
    have hij' := congrFun (congrFun h i) j
    rw [mul_diagonal, diagonal_mul] at hij'
    have h1 : (X : Matrix (Fin n) (Fin n) K) i j * (d j - d i) = 0 := by
      rw [mul_sub, hij', mul_comm (d i)]
      ring
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact h2
    · exact absurd (hd (sub_eq_zero.1 h2)).symm hij
  have hX : (X : Matrix (Fin n) (Fin n) K) =
      diagonal (fun i => (X : Matrix (Fin n) (Fin n) K) i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hij, hoff i j hij]
  have hne : ∀ i, (X : Matrix (Fin n) (Fin n) K) i i ≠ 0 := by
    intro i h0
    have hdet := X.isUnit.map Matrix.detMonoidHom
    rw [Matrix.coe_detMonoidHom, hX, det_diagonal] at hdet
    exact hdet.ne_zero (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  refine ⟨fun i => Units.mk0 _ (hne i), Units.ext ?_⟩
  rw [TauCeti.diagGL_coe]
  conv_lhs => rw [hX]
  simp only [Units.val_mk0]

@[expose] def lastFixedPerm (p : ℕ) (τ : Equiv.Perm (Fin (p - 1))) : Equiv.Perm (Fin p) :=
  τ.extendDomain (Fin.castLEquiv (Nat.sub_le p 1))

@[expose] def signedPermMatrixInt (p : ℕ) (τ : Equiv.Perm (Fin (p - 1))) :
    Matrix (Fin p) (Fin p) ℤ :=
  (lastFixedPerm p τ).permMatrix ℤ *
    diagonal (fun i : Fin p => if (i : ℕ) = p - 1 then ((Equiv.Perm.sign τ : ℤˣ) : ℤ) else 1)

variable (K) in
@[expose] def signedPermMatrix (p : ℕ) (τ : Equiv.Perm (Fin (p - 1))) : Matrix (Fin p) (Fin p) K :=
  (signedPermMatrixInt p τ).map (Int.castRingHom K)

theorem det_signedPermMatrixInt {p : ℕ} (hp : 1 ≤ p) (τ : Equiv.Perm (Fin (p - 1))) :
    (signedPermMatrixInt p τ).det = 1 := by
  classical
  rw [signedPermMatrixInt, det_mul, det_permutation, lastFixedPerm, Equiv.Perm.sign_extendDomain,
    det_diagonal]
  have hlast : (Finset.univ.filter fun i : Fin p => (i : ℕ) = p - 1) = {⟨p - 1, by omega⟩} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => Fin.ext h, fun h => by rw [h]⟩
  rw [Finset.prod_ite, hlast, Finset.prod_singleton, Finset.prod_const_one, mul_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]

theorem det_signedPermMatrix {p : ℕ} (hp : 1 ≤ p) (τ : Equiv.Perm (Fin (p - 1))) :
    (signedPermMatrix K p τ).det = 1 := by
  rw [signedPermMatrix, ← RingHom.mapMatrix_apply, ← RingHom.map_det, det_signedPermMatrixInt hp,
    map_one]

theorem map_signedPermMatrix (σ : K ≃+* K) (p : ℕ) (τ : Equiv.Perm (Fin (p - 1))) :
    (signedPermMatrix K p τ).map σ = signedPermMatrix K p τ := by
  rw [signedPermMatrix, Matrix.map_map]
  congr 1
  funext z
  exact congrFun (congrArg DFunLike.coe (RingHom.ext_int ((σ : K →+* K).comp
    (Int.castRingHom K)) (Int.castRingHom K))) z

end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
