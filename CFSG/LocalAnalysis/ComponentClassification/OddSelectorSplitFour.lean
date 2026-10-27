module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddQuadraticIsotropy
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitAction
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocleField
public import CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices

public noncomputable section

namespace CFSG.ComponentClassification.OddSelector

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

theorem not_isStandardSubgroup_of_witness {G : Type*} [Group G] {L : Subgroup G} {t g : G}
    (ht : orderOf t = 2) (htL : ∀ x ∈ L, x * t = t * x) (hgt : g * t = t * g)
    (hg : g ∉ normalizer (L : Set G)) : ¬ IsStandardSubgroup L := by
  rintro ⟨-, -, hodd, hN, -⟩
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_iff.mpr fun x hx => htL x hx
  have htCg : t ∈ conjugate (centralizer (L : Set G)) g := by
    refine ⟨t, htC, ?_⟩
    change g⁻¹ * t * g⁻¹⁻¹ = t
    rw [inv_inv, mul_assoc, ← hgt, ← mul_assoc, inv_mul_cancel, one_mul]
  have h := hodd g (by rwa [hN])
  set x : ↥(centralizer (L : Set G) ⊓ conjugate (centralizer (L : Set G)) g) :=
    ⟨t, htC, htCg⟩ with hx
  have h3 : orderOf x = 2 :=
    (orderOf_injective (Subgroup.subtype _) (Subgroup.subtype_injective _) x).symm.trans ht
  have h2 := orderOf_dvd_natCard x
  rw [h3] at h2
  exact (Nat.not_even_iff_odd.mpr h) (even_iff_two_dvd.mpr h2)

section Transport

variable {k : Type*} [Field k] {n : ℕ} {V : Type*} [AddCommGroup V] [Module k V]

@[expose] def linearConj (ψ : (Fin n → k) ≃ₗ[k] V) :
    (V ≃ₗ[k] V) →* ((Fin n → k) ≃ₗ[k] (Fin n → k)) where
  toFun f := (ψ.trans f).trans ψ.symm
  map_one' := LinearEquiv.ext fun x => by simp
  map_mul' f g := LinearEquiv.ext fun x => by simp

@[expose] def linearConjGL (ψ : (Fin n → k) ≃ₗ[k] V) : (V ≃ₗ[k] V) →* GL (Fin n) k :=
  (CatalogueBAlternatingIsometry.basisMatrixEquiv (Pi.basisFun k (Fin n))).toMonoidHom.comp
    (linearConj ψ)

theorem linearConjGL_mulVec (ψ : (Fin n → k) ≃ₗ[k] V) (f : V ≃ₗ[k] V) (v : Fin n → k) :
    ((linearConjGL ψ f : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ v = ψ.symm (f (ψ v)) := by
  have h := CatalogueBAlternatingIsometry.basisMatrixEquiv_mulVec (Pi.basisFun k (Fin n))
    (linearConj ψ f) v
  rw [Pi.basisFun_equivFun] at h
  exact h

theorem linearConjGL_injective (ψ : (Fin n → k) ≃ₗ[k] V) :
    Function.Injective (linearConjGL ψ) := by
  intro f g h
  apply LinearEquiv.ext
  intro X
  have := congrArg (fun A : GL (Fin n) k => (A : Matrix (Fin n) (Fin n) k) *ᵥ ψ.symm X) h
  simp only [linearConjGL_mulVec, LinearEquiv.apply_symm_apply] at this
  exact ψ.symm.injective this

theorem eq_of_mulVec_eq {A B : GL (Fin n) k}
    (h : ∀ v : Fin n → k,
      (A : Matrix (Fin n) (Fin n) k) *ᵥ v = (B : Matrix (Fin n) (Fin n) k) *ᵥ v) :
    A = B :=
  Units.ext (Matrix.toLin'.injective (LinearMap.ext fun v => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h v]))

theorem linearConjGL_eq_scalar_iff (ψ : (Fin n → k) ≃ₗ[k] V) (f : V ≃ₗ[k] V) (c : kˣ) :
    linearConjGL ψ f = GeneralLinearGroup.scalar (Fin n) c ↔ ∀ X, f X = (c : k) • X := by
  have hdiag : ∀ v : Fin n → k, (diagonal fun _ => (c : k)) *ᵥ v = (c : k) • v := fun v => by
    ext i
    simp [mulVec_diagonal]
  constructor
  · intro h X
    have := congrArg (fun A : GL (Fin n) k => (A : Matrix (Fin n) (Fin n) k) *ᵥ ψ.symm X) h
    simp only [linearConjGL_mulVec, LinearEquiv.apply_symm_apply,
      GeneralLinearGroup.coe_scalar, scalar_apply, hdiag] at this
    apply ψ.symm.injective
    rw [this, map_smul]
  · intro h
    apply eq_of_mulVec_eq
    intro v
    rw [linearConjGL_mulVec, h, map_smul, LinearEquiv.symm_apply_apply,
      GeneralLinearGroup.coe_scalar, scalar_apply, hdiag]

theorem det_eq_one_of_pow_char {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ] {x : GL (Fin n) k}
    (hx : x ^ ℓ = 1) : (x : Matrix (Fin n) (Fin n) k).det = 1 := by
  have h1 : (x : Matrix (Fin n) (Fin n) k).det ^ ℓ = 1 := by
    rw [← det_pow, ← Units.val_pow_eq_pow_val, hx, Units.val_one, det_one]
  have h2 : ((x : Matrix (Fin n) (Fin n) k).det - 1) ^ ℓ = 0 := by
    rw [sub_pow_char, h1, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (Fact.out : ℓ.Prime).ne_zero |>.mp h2)

end Transport

section Model

variable {k : Type*} [Field k]

theorem single01_mul_single01 :
    (single (0 : Fin 2) (1 : Fin 2) (1 : k)) * single 0 1 1 = 0 :=
  single_mul_single_of_ne (1 : k) (0 : Fin 2) (1 : Fin 2) (0 : Fin 2) (by decide) (1 : k)

@[expose] def splitShear (Y : Matrix (Fin 2) (Fin 2) k) :
    Matrix (Fin 2) (Fin 2) k ≃ₗ[k] Matrix (Fin 2) (Fin 2) k where
  toFun X := X + single 0 1 1 * X * Y
  invFun X := X - single 0 1 1 * X * Y
  map_add' X X' := by rw [Matrix.mul_add, Matrix.add_mul]; abel
  map_smul' c X := by simp [smul_add]
  left_inv X := by
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, single01_mul_single01,
      Matrix.zero_mul, add_zero, add_sub_cancel_right]
  right_inv X := by
    simp only [Matrix.mul_sub, ← Matrix.mul_assoc, single01_mul_single01,
      Matrix.zero_mul, sub_zero, sub_add_cancel]

theorem splitShear_apply (Y X : Matrix (Fin 2) (Fin 2) k) :
    splitShear Y X = X + single 0 1 1 * X * Y := rfl

theorem splitShear_symm_apply (Y X : Matrix (Fin 2) (Fin 2) k) :
    (splitShear Y).symm X = X - single 0 1 1 * X * Y := rfl

theorem splitShear_mul_right {Y W : Matrix (Fin 2) (Fin 2) k} (h : W * Y = Y * W)
    (X : Matrix (Fin 2) (Fin 2) k) : splitShear Y (X * W) = splitShear Y X * W := by
  rw [splitShear_apply, splitShear_apply, Matrix.add_mul]
  simp only [Matrix.mul_assoc, h]

theorem splitShear_conj {Y : Matrix (Fin 2) (Fin 2) k} (hY : Y * Y = -1)
    (h X : Matrix (Fin 2) (Fin 2) k) :
    splitShear Y (h * (splitShear Y).symm X) =
      (h + single 0 1 1 * h * single 0 1 1) * X +
        (single 0 1 1 * h - h * single 0 1 1) * X * Y := by
  rw [splitShear_apply, splitShear_symm_apply]
  have hYY : single 0 1 1 * h * single 0 1 1 * X * Y * Y =
      -(single (0 : Fin 2) (1 : Fin 2) (1 : k) * h * single 0 1 1 * X) := by
    rw [Matrix.mul_assoc _ Y Y, hY, Matrix.mul_neg, Matrix.mul_one]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.add_mul, ← Matrix.mul_assoc, hYY]
  abel

theorem not_forall_commute_of_sq_eq_neg_one (h2 : (2 : k) ≠ 0) {Z : Matrix (Fin 2) (Fin 2) k}
    (hZ : Z * Z = -1) (hdet : Z.det = 1) : ¬ ∀ X : Matrix (Fin 2) (Fin 2) k, X * Z = Z * X := by
  intro h
  have h1 := congrFun (congrFun (h (single 0 1 1)) 0) 0
  have h2' := congrFun (congrFun (h (single 1 0 1)) 0) 0
  have h3 := congrFun (congrFun (h (single 0 1 1)) 0) 1
  have h4 := congrFun (congrFun hZ 0) 0
  simp only [mul_apply, Fin.sum_univ_two, single_apply, Fin.isValue] at h1 h2' h3
  simp [mul_apply, Fin.sum_univ_two] at h4
  norm_num at h1 h2' h3
  have e2 : Z 0 1 = 0 := h2'.symm
  rw [det_fin_two, h1, e2, h3] at hdet
  rw [h1, e2] at h4
  apply h2
  linear_combination h4 - hdet

@[expose] def splitLower (k : Type*) [Field k] : Matrix (Fin 2) (Fin 2) k := !![1, 0; 1, 1]

theorem splitShear_not_normalizes (h2 : (2 : k) ≠ 0) {Z : Matrix (Fin 2) (Fin 2) k}
    (hZ : Z * Z = -1) (hdet : Z.det = 1) (c : k) (U : Matrix (Fin 2) (Fin 2) k)
    (h : ∀ X, splitShear Z (splitLower k * (splitShear Z).symm X) = c • (U * X)) : False := by
  set E : Matrix (Fin 2) (Fin 2) k := single 0 1 1 with hE
  set D : Matrix (Fin 2) (Fin 2) k := E * splitLower k - splitLower k * E with hD
  set A : Matrix (Fin 2) (Fin 2) k := splitLower k + E * splitLower k * E with hA
  have hX : ∀ X, A * X + D * X * Z = c • (U * X) := fun X => by
    rw [← h X, splitShear_conj hZ]
  have hDval : D = !![1, 0; 0, -1] := by
    rw [hD, hE, splitLower]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mul_apply, single_apply, Matrix.vecMul, dotProduct]
  have hDD : D * D = 1 := by
    rw [hDval]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]
  clear_value A D E
  have h1 := hX 1
  rw [Matrix.mul_one, Matrix.mul_one, Matrix.mul_one] at h1
  have hDX : ∀ X, D * X * Z = D * Z * X := by
    intro X
    have h3 : A * X + D * X * Z = A * X + D * Z * X := by
      rw [hX X, ← Matrix.smul_mul, ← h1, Matrix.add_mul]
    exact add_left_cancel h3
  apply not_forall_commute_of_sq_eq_neg_one h2 hZ hdet
  intro X
  have := congrArg (D * ·) (hDX X)
  simpa only [← Matrix.mul_assoc, hDD, Matrix.one_mul] using this

theorem splitShear_pow_apply (Y X : Matrix (Fin 2) (Fin 2) k) (n : ℕ) :
    (splitShear Y ^ n) X = X + n • (single 0 1 1 * X * Y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, splitShear_apply]
    simp only [Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc, single01_mul_single01,
      Matrix.zero_mul, smul_zero, add_zero, succ_nsmul]
    abel

theorem splitShear_pow_char {ℓ : ℕ} [CharP k ℓ] (Y : Matrix (Fin 2) (Fin 2) k) :
    splitShear Y ^ ℓ = 1 := by
  apply LinearEquiv.ext
  intro X
  rw [splitShear_pow_apply, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul, add_zero]
  rfl

end Model

section Factors

variable {k : Type*} [Field k] (ψ : (Fin 4 → k) ≃ₗ[k] Matrix (Fin 2) (Fin 2) k)

@[expose] def splitLeftHom : SpecialLinearGroup (Fin 2) k →* GL (Fin 4) k :=
  (linearConjGL ψ).comp ((DeterminantIsometries k).subtype.comp
    ((specialRho (K := k)).comp (MonoidHom.inl _ _)))

@[expose] def splitRightHom : SpecialLinearGroup (Fin 2) k →* GL (Fin 4) k :=
  (linearConjGL ψ).comp ((DeterminantIsometries k).subtype.comp
    ((specialRho (K := k)).comp (MonoidHom.inr _ _)))

theorem splitLeftHom_mulVec (U : SpecialLinearGroup (Fin 2) k) (v : Fin 4 → k) :
    ((splitLeftHom ψ U : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) *ᵥ v =
      ψ.symm ((U : Matrix (Fin 2) (Fin 2) k) * ψ v) := by
  rw [splitLeftHom, MonoidHom.comp_apply, linearConjGL_mulVec]
  congr 1
  change (specialRho (U, 1)).val (ψ v) = _
  rw [specialRho_apply]
  simp

theorem splitRightHom_mulVec (W : SpecialLinearGroup (Fin 2) k) (v : Fin 4 → k) :
    ((splitRightHom ψ W : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) *ᵥ v =
      ψ.symm (ψ v * ((W⁻¹ : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) := by
  rw [splitRightHom, MonoidHom.comp_apply, linearConjGL_mulVec]
  congr 1
  change (specialRho (1, W)).val (ψ v) = _
  rw [specialRho_apply]
  simp

theorem splitLeftHom_commute (U W : SpecialLinearGroup (Fin 2) k) :
    splitLeftHom ψ U * splitRightHom ψ W = splitRightHom ψ W * splitLeftHom ψ U := by
  apply eq_of_mulVec_eq
  intro v
  simp only [Units.val_mul, ← Matrix.mulVec_mulVec, splitLeftHom_mulVec, splitRightHom_mulVec,
    LinearEquiv.apply_symm_apply, Matrix.mul_assoc]

theorem splitLeftHom_eq_scalar_iff (U : SpecialLinearGroup (Fin 2) k) (c : kˣ) :
    splitLeftHom ψ U = GeneralLinearGroup.scalar (Fin 4) c ↔
      (U : Matrix (Fin 2) (Fin 2) k) = (c : k) • 1 := by
  rw [splitLeftHom, MonoidHom.comp_apply, linearConjGL_eq_scalar_iff]
  change (∀ X, (specialRho (U, 1)).val X = (c : k) • X) ↔ _
  simp only [specialRho_apply, inv_one]
  constructor
  · intro h
    simpa using h 1
  · intro h X
    simp [h]

theorem splitRightHom_eq_scalar {W : SpecialLinearGroup (Fin 2) k} {c : kˣ}
    (h : splitRightHom ψ W = GeneralLinearGroup.scalar (Fin 4) c) (X : Matrix (Fin 2) (Fin 2) k) :
    X * W = W * X := by
  rw [splitRightHom, MonoidHom.comp_apply, linearConjGL_eq_scalar_iff] at h
  change ∀ X, (specialRho (1, W)).val X = (c : k) • X at h
  simp only [specialRho_apply] at h
  set N : Matrix (Fin 2) (Fin 2) k := ((W⁻¹ : SpecialLinearGroup (Fin 2) k) :
    Matrix (Fin 2) (Fin 2) k) with hN
  set M : Matrix (Fin 2) (Fin 2) k := (W : Matrix (Fin 2) (Fin 2) k) with hM
  have hMN : M * N = 1 := congrArg Subtype.val (mul_inv_cancel W)
  have hNM : N * M = 1 := congrArg Subtype.val (inv_mul_cancel W)
  have hN1 : N = (c : k) • 1 := by simpa using h 1
  have hNX : ∀ Y : Matrix (Fin 2) (Fin 2) k, Y * N = N * Y := fun Y => by
    rw [hN1, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  calc X * M = M * N * X * M := by rw [hMN, Matrix.one_mul]
    _ = M * (X * N) * M := by rw [hNX X, Matrix.mul_assoc M N X]
    _ = M * X := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hNM, Matrix.mul_one]

variable [Finite k]

theorem det_splitLeftHom (hq : 5 ≤ Nat.card k) (U : SpecialLinearGroup (Fin 2) k) :
    ((splitLeftHom ψ U : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k).det = 1 := by
  have : Group.IsPerfect (SpecialLinearGroup (Fin 2) k) :=
    CatalogueBGeneralLinear.specialLinear_perfect 2 k le_rfl (Or.inr (by omega))
      (Or.inr (by omega))
  have hU : U ∈ (GeneralLinearGroup.det.comp (splitLeftHom ψ)).ker :=
    Abelianization.commutator_subset_ker _ Group.IsPerfect.mem_commutator
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hU
  have := congrArg Units.val hU
  rwa [GeneralLinearGroup.val_det_apply, Units.val_one] at this

theorem det_splitRightHom (hq : 5 ≤ Nat.card k) (W : SpecialLinearGroup (Fin 2) k) :
    ((splitRightHom ψ W : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k).det = 1 := by
  have : Group.IsPerfect (SpecialLinearGroup (Fin 2) k) :=
    CatalogueBGeneralLinear.specialLinear_perfect 2 k le_rfl (Or.inr (by omega))
      (Or.inr (by omega))
  have hW : W ∈ (GeneralLinearGroup.det.comp (splitRightHom ψ)).ker :=
    Abelianization.commutator_subset_ker _ Group.IsPerfect.mem_commutator
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hW
  have := congrArg Units.val hW
  rwa [GeneralLinearGroup.val_det_apply, Units.val_one] at this

@[expose] def splitLeftSL (hq : 5 ≤ Nat.card k) :
    SpecialLinearGroup (Fin 2) k →* SpecialLinearGroup (Fin 4) k where
  toFun U := ⟨splitLeftHom ψ U, det_splitLeftHom ψ hq U⟩
  map_one' := Subtype.ext (show ((splitLeftHom ψ 1 : GL (Fin 4) k) :
    Matrix (Fin 4) (Fin 4) k) = 1 by rw [map_one]; rfl)
  map_mul' U W := Subtype.ext (show ((splitLeftHom ψ (U * W) : GL (Fin 4) k) :
    Matrix (Fin 4) (Fin 4) k) = (splitLeftHom ψ U : Matrix (Fin 4) (Fin 4) k) *
      (splitLeftHom ψ W : Matrix (Fin 4) (Fin 4) k) by rw [map_mul]; rfl)

@[expose] def splitRightSL (hq : 5 ≤ Nat.card k) :
    SpecialLinearGroup (Fin 2) k →* SpecialLinearGroup (Fin 4) k where
  toFun W := ⟨splitRightHom ψ W, det_splitRightHom ψ hq W⟩
  map_one' := Subtype.ext (show ((splitRightHom ψ 1 : GL (Fin 4) k) :
    Matrix (Fin 4) (Fin 4) k) = 1 by rw [map_one]; rfl)
  map_mul' U W := Subtype.ext (show ((splitRightHom ψ (U * W) : GL (Fin 4) k) :
    Matrix (Fin 4) (Fin 4) k) = (splitRightHom ψ U : Matrix (Fin 4) (Fin 4) k) *
      (splitRightHom ψ W : Matrix (Fin 4) (Fin 4) k) by rw [map_mul]; rfl)

end Factors

section Theorem

variable {k : Type} [Field k] [Finite k]

theorem center_projectiveSL_eq_bot {n : ℕ} (hn : 3 ≤ n) : center (projectiveSL n k) = ⊥ := by
  have := OutcomeLocal.isSimpleGroup_projectiveSL (k := k) hn
  have : Group.IsPerfect (SpecialLinearGroup (Fin n) k) :=
    CatalogueBGeneralLinear.specialLinear_perfect n k (by omega) (Or.inl (by omega))
      (Or.inl (by omega))
  have : Group.IsPerfect (projectiveSL n k) := Group.IsPerfect.ofSurjective (proj_surjective n k)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (projectiveSL n k)) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : projectiveSL n k, a * b = b * a := fun a b =>
      mem_center_iff.mp (h ▸ mem_top b) a
    exact Group.IsPerfect.not_isSolvable _ (Group.isSolvable_of_comm hcomm)

theorem conj_injective_projectiveSL {n : ℕ} (hn : 3 ≤ n) :
    Function.Injective (MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [← center_projectiveSL_eq_bot (k := k) hn, mem_center_iff]
  intro z
  have := congrArg (fun φ : MulAut (projectiveSL n k) => φ z) (MonoidHom.mem_ker.mp hx)
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  calc z * x = x * z * x⁻¹ * x := by rw [this]
    _ = x * z := by group

theorem mem_conj_map_iff {n : ℕ} (hn : 3 ≤ n) (J : Subgroup (projectiveSL n k))
    (x : projectiveSL n k) :
    MulAut.conj x ∈ J.map MulAut.conj ↔ x ∈ J := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    rwa [← conj_injective_projectiveSL hn hxy]
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem not_isStandardSubgroup_conj_map {n : ℕ} (hn : 3 ≤ n) (J : Subgroup (projectiveSL n k))
    {t g : projectiveSL n k} (ht : orderOf t = 2) (htJ : ∀ x ∈ J, x * t = t * x)
    (hgt : g * t = t * g) (hg : g ∉ normalizer (J : Set (projectiveSL n k)))
    (A : Subgroup (MulAut (projectiveSL n k)))
    (hA : OuterAutomorphisms.inner (projectiveSL n k) ≤ A) :
    ¬ IsStandardSubgroup ((J.map MulAut.conj).subgroupOf A) := by
  have hinj := conj_injective_projectiveSL (k := k) hn
  have hmem : ∀ x : projectiveSL n k, MulAut.conj x ∈ A := fun x => hA ⟨x, rfl⟩
  set t' : A := ⟨MulAut.conj t, hmem t⟩
  set g' : A := ⟨MulAut.conj g, hmem g⟩
  refine not_isStandardSubgroup_of_witness (t := t') (g := g') ?_ ?_ ?_ ?_
  · have h1 : orderOf t' = orderOf (MulAut.conj t) :=
      (orderOf_injective A.subtype A.subtype_injective t').symm
    rw [h1, orderOf_injective _ hinj t, ht]
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := mem_subgroupOf.mp hx
    apply Subtype.ext
    simp only [Subgroup.coe_mul, t', ← hyx, ← map_mul, htJ y hy]
  · exact Subtype.ext (by simp only [t', g', Subgroup.coe_mul, ← map_mul, hgt])
  · intro hN
    apply hg
    rw [mem_normalizer_iff] at hN ⊢
    intro x
    have h1 := hN ⟨MulAut.conj x, hmem x⟩
    simp only [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, g', ← map_inv,
      ← map_mul, mem_conj_map_iff hn] at h1
    exact h1

variable (ψ : (Fin 4 → k) ≃ₗ[k] Matrix (Fin 2) (Fin 2) k)

@[expose] def splitShearSL (Z : Matrix (Fin 2) (Fin 2) k) {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ] :
    SpecialLinearGroup (Fin 4) k :=
  ⟨((linearConjGL ψ (splitShear Z) : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k),
    det_eq_one_of_pow_char (ℓ := ℓ) (by rw [← map_pow, splitShear_pow_char, map_one])⟩

omit [Finite k] in
theorem splitShearSL_mulVec (Z : Matrix (Fin 2) (Fin 2) k) {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ]
    (v : Fin 4 → k) :
    ((splitShearSL ψ Z (ℓ := ℓ) : SpecialLinearGroup (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) *ᵥ v =
      ψ.symm (splitShear Z (ψ v)) := by
  change ((linearConjGL ψ (splitShear Z) : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) *ᵥ v = _
  rw [linearConjGL_mulVec]

theorem not_isStandardSubgroup_of_conj_witness {n : ℕ} (hn : 3 ≤ n)
    (J : Subgroup (projectiveSL n k)) {t g : projectiveSL n k} (ht : orderOf t = 2)
    (htJ : ∀ x ∈ J, x * t = t * x) (hgt : g * t = t * g)
    (hg : g ∉ normalizer (J : Set (projectiveSL n k))) {A : Type*} [Group A]
    {ρ : A →* MulAut (projectiveSL n k)} (hinj : Function.Injective ρ)
    (hinn : OuterAutomorphisms.inner (projectiveSL n k) ≤ ρ.range) {L : Subgroup A}
    (hL : L.map ρ = J.map MulAut.conj) : ¬ IsStandardSubgroup L := by
  have hcj := conj_injective_projectiveSL (k := k) hn
  obtain ⟨tA, htA⟩ := hinn ⟨t, rfl⟩
  obtain ⟨gA, hgA⟩ := hinn ⟨g, rfl⟩
  have hmemL : ∀ y ∈ J, ∃ x ∈ L, ρ x = MulAut.conj y := fun y hy => by
    have : MulAut.conj y ∈ L.map ρ := hL ▸ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy⟩ := this
    exact ⟨x, hx, hxy⟩
  have hmemJ : ∀ x ∈ L, ∃ y ∈ J, ρ x = MulAut.conj y := fun x hx => by
    have : ρ x ∈ J.map MulAut.conj := hL ▸ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := this
    exact ⟨y, hy, hxy.symm⟩
  refine not_isStandardSubgroup_of_witness (t := tA) (g := gA) ?_ ?_ ?_ ?_
  · rw [← orderOf_injective ρ hinj tA, htA, orderOf_injective _ hcj t, ht]
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hmemJ x hx
    apply hinj
    rw [map_mul, map_mul, hxy, htA, ← map_mul, ← map_mul, htJ y hy]
  · apply hinj
    rw [map_mul, map_mul, htA, hgA, ← map_mul, ← map_mul, hgt]
  · intro hN
    apply hg
    rw [mem_normalizer_iff] at hN ⊢
    intro y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := hmemL y hy
      obtain ⟨y', hy', hxy'⟩ := hmemJ _ ((hN x).mp hx)
      rw [map_mul, map_mul, map_inv, hgA, hxy, ← map_inv, ← map_mul, ← map_mul] at hxy'
      rwa [hcj hxy']
    · intro hy
      obtain ⟨x, hx, hxy⟩ := hmemL _ hy
      have hx' : gA⁻¹ * x * gA ∈ L := by
        rw [hN]
        simpa [mul_assoc] using hx
      obtain ⟨y', hy', hxy'⟩ := hmemJ _ hx'
      rw [map_mul, map_mul, map_inv, hgA, hxy, ← map_inv, ← map_mul, ← map_mul] at hxy'
      have : y = y' := hcj (by rw [← hxy']; group)
      rwa [this]

variable (ψ : (Fin 4 → k) ≃ₗ[k] Matrix (Fin 2) (Fin 2) k)

@[expose] def splitQuatI : SpecialLinearGroup (Fin 2) k :=
  ⟨QuaternionMatrices.quatI k, QuaternionMatrices.det_quatI⟩

omit [Finite k] in
theorem splitQuatI_mul_self :
    ((splitQuatI : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
      ((splitQuatI : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = -1 :=
  QuaternionMatrices.quatI_mul_self

@[expose] def splitLowerSL : SpecialLinearGroup (Fin 2) k :=
  ⟨splitLower k, by simp [splitLower, det_fin_two]⟩

@[expose] def splitLeftP (hq : 5 ≤ Nat.card k) :
    SpecialLinearGroup (Fin 2) k →* projectiveSL 4 k :=
  (proj 4 k).comp (splitLeftSL ψ hq)

@[expose] def splitRightP (hq : 5 ≤ Nat.card k) :
    SpecialLinearGroup (Fin 2) k →* projectiveSL 4 k :=
  (proj 4 k).comp (splitRightSL ψ hq)

omit [Finite k] in
theorem scalar_eq_smul_one {n : ℕ} (c : k) :
    Matrix.scalar (Fin n) c = c • (1 : Matrix (Fin n) (Fin n) k) := by
  rw [smul_one_eq_diagonal]
  rfl

omit [Finite k] in
theorem mem_scalars_two_of_eq_smul {U : SpecialLinearGroup (Fin 2) k} {c : kˣ}
    (hU : (U : Matrix (Fin 2) (Fin 2) k) = (c : k) • 1) : U ∈ scalars 2 k := by
  have hdet : (c : k) ^ 2 = 1 := by
    have h := U.2
    change (U : Matrix (Fin 2) (Fin 2) k).det = 1 at h
    rwa [hU, det_smul, det_one, mul_one, Fintype.card_fin] at h
  refine ⟨c, Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one]), ?_⟩
  rw [hU, scalar_eq_smul_one]

theorem splitLeftP_ker (hq : 5 ≤ Nat.card k) : (splitLeftP ψ hq).ker = scalars 2 k := by
  ext U
  rw [MonoidHom.mem_ker, splitLeftP, MonoidHom.comp_apply, proj_eq_one_iff, mem_scalars]
  constructor
  · rintro ⟨c, -, hc⟩
    have h := (splitLeftHom_eq_scalar_iff ψ U c).mp (Units.ext hc)
    exact mem_scalars_two_of_eq_smul h
  · rintro ⟨c, hc, hU⟩
    refine ⟨c, by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hc, one_pow], ?_⟩
    have h := (splitLeftHom_eq_scalar_iff ψ U c).mpr (by rw [hU, scalar_eq_smul_one])
    exact congrArg Units.val h

theorem splitRightP_ker (hq : 5 ≤ Nat.card k) : (splitRightP ψ hq).ker = scalars 2 k := by
  ext W
  rw [MonoidHom.mem_ker, splitRightP, MonoidHom.comp_apply, proj_eq_one_iff, mem_scalars]
  constructor
  · rintro ⟨c, -, hc⟩
    have h := splitRightHom_eq_scalar ψ (W := W) (c := c) (Units.ext hc)
    obtain ⟨r, hr⟩ := mem_range_scalar_of_commute_single (M := (W : Matrix (Fin 2) (Fin 2) k))
      fun i j _ => (h (single i j 1)).symm.symm
    have hr0 : r ≠ 0 := by
      rintro rfl
      have hdet := W.2
      change (W : Matrix (Fin 2) (Fin 2) k).det = 1 at hdet
      rw [← hr, map_zero, det_zero] at hdet
      exact zero_ne_one hdet
    exact mem_scalars_two_of_eq_smul (c := Units.mk0 r hr0) (by
      rw [← hr, Units.val_mk0, scalar_eq_smul_one])
  · rintro ⟨c, hc, hW⟩
    refine ⟨c, by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hc, one_pow], ?_⟩
    have hWW : W * W = 1 := Subtype.ext (by
      change (W : Matrix (Fin 2) (Fin 2) k) * W = 1
      rw [hW, ← map_mul, ← Units.val_mul, ← sq, hc, Units.val_one, map_one])
    have hWi : W⁻¹ = W := inv_eq_of_mul_eq_one_right hWW
    have h : splitRightHom ψ W = GeneralLinearGroup.scalar (Fin 4) c := by
      rw [splitRightHom, MonoidHom.comp_apply, linearConjGL_eq_scalar_iff]
      intro X
      change (specialRho (1, W)).val X = (c : k) • X
      rw [specialRho_apply, hWi, hW, scalar_eq_smul_one]
      simp
    exact congrArg Units.val h

theorem orderOf_splitRightP_quatI (hq : 5 ≤ Nat.card k) (h2 : (2 : k) ≠ 0) :
    orderOf (splitRightP ψ hq splitQuatI) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow]
    apply (MonoidHom.mem_ker).mp
    rw [splitRightP_ker]
    refine mem_scalars_two_of_eq_smul (c := -1) ?_
    rw [sq]
    change ((splitQuatI : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
      ((splitQuatI : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = _
    rw [splitQuatI_mul_self]
    simp
  · intro h1
    have hmem : splitQuatI ∈ (splitRightP ψ hq).ker := h1
    rw [splitRightP_ker, mem_scalars] at hmem
    obtain ⟨c, -, hc⟩ := hmem
    apply not_forall_commute_of_sq_eq_neg_one h2 splitQuatI_mul_self QuaternionMatrices.det_quatI
    intro X
    rw [hc, scalar_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

theorem orderOf_splitLeftP_quatI (hq : 5 ≤ Nat.card k) (h2 : (2 : k) ≠ 0) :
    orderOf (splitLeftP ψ hq splitQuatI) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow]
    apply (MonoidHom.mem_ker).mp
    rw [splitLeftP_ker]
    refine mem_scalars_two_of_eq_smul (c := -1) ?_
    rw [sq]
    change ((splitQuatI : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
      ((splitQuatI : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = _
    rw [splitQuatI_mul_self]
    simp
  · intro h1
    have hmem : splitQuatI ∈ (splitLeftP ψ hq).ker := h1
    rw [splitLeftP_ker, mem_scalars] at hmem
    obtain ⟨c, -, hc⟩ := hmem
    apply not_forall_commute_of_sq_eq_neg_one h2 splitQuatI_mul_self QuaternionMatrices.det_quatI
    intro X
    rw [hc, scalar_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

omit [Finite k] in
theorem toGL_splitShearSL (Z : Matrix (Fin 2) (Fin 2) k) {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ] :
    SpecialLinearGroup.toGL (splitShearSL ψ Z (ℓ := ℓ)) = linearConjGL ψ (splitShear Z) :=
  Units.ext rfl

theorem toGL_splitLeftSL (hq : 5 ≤ Nat.card k) (U : SpecialLinearGroup (Fin 2) k) :
    SpecialLinearGroup.toGL (splitLeftSL ψ hq U) = splitLeftHom ψ U :=
  Units.ext rfl

theorem toGL_splitRightSL (hq : 5 ≤ Nat.card k) (W : SpecialLinearGroup (Fin 2) k) :
    SpecialLinearGroup.toGL (splitRightSL ψ hq W) = splitRightHom ψ W :=
  Units.ext rfl

omit [Finite k] in
theorem exists_scalar_of_proj_eq {x y : SpecialLinearGroup (Fin 4) k}
    (h : proj 4 k x = proj 4 k y) :
    ∃ c : kˣ, SpecialLinearGroup.toGL y =
      SpecialLinearGroup.toGL x * GeneralLinearGroup.scalar (Fin 4) c := by
  obtain ⟨c, -, hc⟩ := proj_eq_proj_iff.mp h
  refine ⟨c, ?_⟩
  have h1 : SpecialLinearGroup.toGL (x⁻¹ * y) = GeneralLinearGroup.scalar (Fin 4) c :=
    Units.ext hc
  rw [map_mul, map_inv] at h1
  rw [← h1, mul_inv_cancel_left]

theorem proj_splitShearSL_not_mem_normalizer (hq : 5 ≤ Nat.card k) (h2 : (2 : k) ≠ 0)
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ] :
    proj 4 k (splitShearSL ψ (QuaternionMatrices.quatI k) (ℓ := ℓ)) ∉
      normalizer ((splitLeftP ψ hq).range : Set (projectiveSL 4 k)) := by
  intro hN
  set S := splitShearSL ψ (QuaternionMatrices.quatI k) (ℓ := ℓ) with hS
  have hmem := (mem_normalizer_iff.mp hN (splitLeftP ψ hq splitLowerSL)).mp ⟨_, rfl⟩
  obtain ⟨U, hU⟩ := hmem
  have hU' : proj 4 k (splitLeftSL ψ hq U) =
      proj 4 k (S * splitLeftSL ψ hq splitLowerSL * S⁻¹) := by
    rw [map_mul, map_mul, map_inv]
    exact hU
  obtain ⟨c, hc⟩ := exists_scalar_of_proj_eq hU'
  rw [map_mul, map_mul, map_inv, toGL_splitShearSL, toGL_splitLeftSL, toGL_splitLeftSL,
    ← map_inv] at hc
  refine splitShear_not_normalizes h2 QuaternionMatrices.quatI_mul_self
    QuaternionMatrices.det_quatI c U fun X => ?_
  have h1 := congrArg (fun A : GL (Fin 4) k => (A : Matrix (Fin 4) (Fin 4) k) *ᵥ ψ.symm X) hc
  simp only [Units.val_mul, ← Matrix.mulVec_mulVec, linearConjGL_mulVec, splitLeftHom_mulVec,
    LinearEquiv.apply_symm_apply, GeneralLinearGroup.coe_scalar, scalar_eq_smul_one,
    Matrix.smul_mulVec, Matrix.one_mulVec, map_smul] at h1
  apply ψ.symm.injective
  rw [Matrix.mul_smul] at h1
  exact h1

omit [Finite k] in
theorem transposeLinearEquiv_mul_self :
    (transposeLinearEquiv (Fin 2) (Fin 2) k k : Matrix (Fin 2) (Fin 2) k ≃ₗ[k] _) *
      transposeLinearEquiv (Fin 2) (Fin 2) k k = 1 :=
  LinearEquiv.ext fun X => transpose_transpose X

@[expose] def splitShearT (Z : Matrix (Fin 2) (Fin 2) k) :
    Matrix (Fin 2) (Fin 2) k ≃ₗ[k] Matrix (Fin 2) (Fin 2) k :=
  transposeLinearEquiv (Fin 2) (Fin 2) k k * splitShear Zᵀ *
    transposeLinearEquiv (Fin 2) (Fin 2) k k

omit [Finite k] in
theorem splitShearT_apply (Z X : Matrix (Fin 2) (Fin 2) k) :
    splitShearT Z X = (splitShear Zᵀ Xᵀ)ᵀ := rfl

omit [Finite k] in
theorem splitShearT_symm_apply (Z X : Matrix (Fin 2) (Fin 2) k) :
    (splitShearT Z).symm X = ((splitShear Zᵀ).symm Xᵀ)ᵀ := rfl

omit [Finite k] in
theorem splitShearT_pow_char {ℓ : ℕ} [CharP k ℓ] (Z : Matrix (Fin 2) (Fin 2) k) :
    splitShearT Z ^ ℓ = 1 := by
  have hT : (transposeLinearEquiv (Fin 2) (Fin 2) k k : Matrix (Fin 2) (Fin 2) k ≃ₗ[k] _)⁻¹ =
      transposeLinearEquiv (Fin 2) (Fin 2) k k :=
    inv_eq_of_mul_eq_one_right transposeLinearEquiv_mul_self
  have h := conj_pow (a := transposeLinearEquiv (Fin 2) (Fin 2) k k) (b := splitShear Zᵀ)
    (i := ℓ)
  rw [hT, splitShear_pow_char, mul_one, transposeLinearEquiv_mul_self] at h
  exact h

@[expose] def splitShearTSL (Z : Matrix (Fin 2) (Fin 2) k) {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ] :
    SpecialLinearGroup (Fin 4) k :=
  ⟨((linearConjGL ψ (splitShearT Z) : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k),
    det_eq_one_of_pow_char (ℓ := ℓ) (by rw [← map_pow, splitShearT_pow_char, map_one])⟩

omit [Finite k] in
theorem toGL_splitShearTSL (Z : Matrix (Fin 2) (Fin 2) k) {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ] :
    SpecialLinearGroup.toGL (splitShearTSL ψ Z (ℓ := ℓ)) = linearConjGL ψ (splitShearT Z) :=
  Units.ext rfl

@[expose] def splitUpperInvSL : SpecialLinearGroup (Fin 2) k :=
  (SpecialLinearGroup.transpose splitLowerSL)⁻¹

theorem proj_splitShearTSL_not_mem_normalizer (hq : 5 ≤ Nat.card k) (h2 : (2 : k) ≠ 0)
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ] :
    proj 4 k (splitShearTSL ψ (QuaternionMatrices.quatI k) (ℓ := ℓ)) ∉
      normalizer ((splitRightP ψ hq).range : Set (projectiveSL 4 k)) := by
  intro hN
  set S := splitShearTSL ψ (QuaternionMatrices.quatI k) (ℓ := ℓ) with hS
  have hmem := (mem_normalizer_iff.mp hN (splitRightP ψ hq splitUpperInvSL)).mp ⟨_, rfl⟩
  obtain ⟨W, hW⟩ := hmem
  have hW' : proj 4 k (splitRightSL ψ hq W) =
      proj 4 k (S * splitRightSL ψ hq splitUpperInvSL * S⁻¹) := by
    rw [map_mul, map_mul, map_inv]
    exact hW
  obtain ⟨c, hc⟩ := exists_scalar_of_proj_eq hW'
  rw [map_mul, map_mul, map_inv, toGL_splitShearTSL, toGL_splitRightSL, toGL_splitRightSL,
    ← map_inv] at hc
  set Z : Matrix (Fin 2) (Fin 2) k := QuaternionMatrices.quatI k with hZ
  set N : Matrix (Fin 2) (Fin 2) k :=
    ((W⁻¹ : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) with hN
  have hZT : Zᵀ * Zᵀ = -1 := by
    rw [← transpose_mul, hZ, QuaternionMatrices.quatI_mul_self, transpose_neg, transpose_one]
  have hdetT : Zᵀ.det = 1 := by rw [det_transpose, hZ, QuaternionMatrices.det_quatI]
  have hinv : ((splitUpperInvSL⁻¹ : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      (splitLower k)ᵀ := by
    rw [splitUpperInvSL, inv_inv]
    rfl
  refine splitShear_not_normalizes h2 hZT hdetT c Nᵀ fun Y => ?_
  have h1 := congrArg (fun A : GL (Fin 4) k => (A : Matrix (Fin 4) (Fin 4) k) *ᵥ ψ.symm Yᵀ) hc
  simp only [Units.val_mul, ← Matrix.mulVec_mulVec, linearConjGL_mulVec, splitRightHom_mulVec,
    LinearEquiv.apply_symm_apply, GeneralLinearGroup.coe_scalar, scalar_eq_smul_one,
    Matrix.smul_mulVec, Matrix.one_mulVec, map_smul] at h1
  have h3 := congrArg transpose (ψ.symm.injective h1)
  change (splitShearT Z ((splitShearT Z).symm Yᵀ * _))ᵀ = _ at h3
  rw [splitShearT_apply, splitShearT_symm_apply, hinv, transpose_transpose, transpose_mul,
    transpose_transpose, transpose_transpose, Matrix.smul_mul, transpose_smul, transpose_mul,
    transpose_transpose] at h3
  exact h3

theorem splitShearSL_commute (hq : 5 ≤ Nat.card k) {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ] :
    splitShearSL ψ (QuaternionMatrices.quatI k) (ℓ := ℓ) * splitRightSL ψ hq splitQuatI =
      splitRightSL ψ hq splitQuatI * splitShearSL ψ (QuaternionMatrices.quatI k) (ℓ := ℓ) := by
  apply SpecialLinearGroup.toGL_injective
  rw [map_mul, map_mul, toGL_splitShearSL, toGL_splitRightSL]
  apply eq_of_mulVec_eq
  intro v
  simp only [Units.val_mul, ← Matrix.mulVec_mulVec, linearConjGL_mulVec, splitRightHom_mulVec,
    LinearEquiv.apply_symm_apply]
  congr 1
  refine splitShear_mul_right ?_ _
  have h1 : ((splitQuatI⁻¹ : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
      QuaternionMatrices.quatI k = 1 := congrArg Subtype.val (inv_mul_cancel splitQuatI)
  have h2 : QuaternionMatrices.quatI k *
      ((splitQuatI⁻¹ : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = 1 :=
    congrArg Subtype.val (mul_inv_cancel splitQuatI)
  rw [h1, h2]

theorem splitShearTSL_commute (hq : 5 ≤ Nat.card k) {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ] :
    splitShearTSL ψ (QuaternionMatrices.quatI k) (ℓ := ℓ) * splitLeftSL ψ hq splitQuatI =
      splitLeftSL ψ hq splitQuatI * splitShearTSL ψ (QuaternionMatrices.quatI k) (ℓ := ℓ) := by
  apply SpecialLinearGroup.toGL_injective
  rw [map_mul, map_mul, toGL_splitShearTSL, toGL_splitLeftSL]
  apply eq_of_mulVec_eq
  intro v
  simp only [Units.val_mul, ← Matrix.mulVec_mulVec, linearConjGL_mulVec, splitLeftHom_mulVec,
    LinearEquiv.apply_symm_apply]
  congr 1
  change splitShearT _ (QuaternionMatrices.quatI k * ψ v) =
    QuaternionMatrices.quatI k * splitShearT _ (ψ v)
  rw [splitShearT_apply, splitShearT_apply, transpose_mul, splitShear_mul_right rfl,
    transpose_mul, transpose_transpose]

theorem odd_split_four_graph_component_not_standard (hodd : Odd (Nat.card k))
    (hq : 5 ≤ Nat.card k) (ψ : (Fin 4 → k) ≃ₗ[k] Matrix (Fin 2) (Fin 2) k) :
    ∃ J₁ J₂ : Subgroup (projectiveSL 4 k),
      (∀ x, x ∈ J₁ ↔ ∃ (U : SpecialLinearGroup (Fin 2) k) (g : SpecialLinearGroup (Fin 4) k),
        (∀ v, (g : Matrix (Fin 4) (Fin 4) k) *ᵥ v =
          ψ.symm ((U : Matrix (Fin 2) (Fin 2) k) * ψ v)) ∧ x = proj 4 k g) ∧
      (∀ x, x ∈ J₂ ↔ ∃ (W : SpecialLinearGroup (Fin 2) k) (g : SpecialLinearGroup (Fin 4) k),
        (∀ v, (g : Matrix (Fin 4) (Fin 4) k) *ᵥ v =
          ψ.symm (ψ v * ((W⁻¹ : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k))) ∧
        x = proj 4 k g) ∧
      (∀ x ∈ J₁, ∀ y ∈ J₂, x * y = y * x) ∧
      Nonempty (J₁ ≃* projectiveSL 2 k) ∧ Nonempty (J₂ ≃* projectiveSL 2 k) ∧
      (∃ t ∈ J₂, orderOf t = 2 ∧ ∃ g : projectiveSL 4 k, g * t = t * g ∧
        g ∉ normalizer (J₁ : Set (projectiveSL 4 k))) ∧
      (∃ t ∈ J₁, orderOf t = 2 ∧ ∃ g : projectiveSL 4 k, g * t = t * g ∧
        g ∉ normalizer (J₂ : Set (projectiveSL 4 k))) ∧
      ∀ A : Subgroup (MulAut (projectiveSL 4 k)),
        OuterAutomorphisms.inner (projectiveSL 4 k) ≤ A →
          ¬ IsStandardSubgroup ((J₁.map MulAut.conj).subgroupOf A) ∧
          ¬ IsStandardSubgroup ((J₂.map MulAut.conj).subgroupOf A) := by
  classical
  obtain ⟨ℓ, hchar⟩ := CharP.exists k
  have : Fact ℓ.Prime := ⟨CharP.char_is_prime k ℓ⟩
  have h2 : (2 : k) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  set J₁ := (splitLeftP ψ hq).range with hJ₁
  set J₂ := (splitRightP ψ hq).range with hJ₂
  have hcomm : ∀ x ∈ J₁, ∀ y ∈ J₂, x * y = y * x := by
    rintro _ ⟨U, rfl⟩ _ ⟨W, rfl⟩
    simp only [splitLeftP, splitRightP, MonoidHom.comp_apply, ← map_mul]
    congr 1
    apply SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul, toGL_splitLeftSL, toGL_splitRightSL, splitLeftHom_commute]
  set t₂ := splitRightP ψ hq splitQuatI with ht₂
  set t₁ := splitLeftP ψ hq splitQuatI with ht₁
  set g₁ := proj 4 k (splitShearSL ψ (QuaternionMatrices.quatI k) (ℓ := ℓ)) with hg₁
  set g₂ := proj 4 k (splitShearTSL ψ (QuaternionMatrices.quatI k) (ℓ := ℓ)) with hg₂
  have ht₂o : orderOf t₂ = 2 := orderOf_splitRightP_quatI ψ hq h2
  have ht₁o : orderOf t₁ = 2 := orderOf_splitLeftP_quatI ψ hq h2
  have hg₁t : g₁ * t₂ = t₂ * g₁ := by
    rw [hg₁, ht₂, splitRightP, MonoidHom.comp_apply, ← map_mul, ← map_mul,
      splitShearSL_commute ψ hq]
  have hg₂t : g₂ * t₁ = t₁ * g₂ := by
    rw [hg₂, ht₁, splitLeftP, MonoidHom.comp_apply, ← map_mul, ← map_mul,
      splitShearTSL_commute ψ hq]
  have hg₁N : g₁ ∉ normalizer (J₁ : Set (projectiveSL 4 k)) :=
    proj_splitShearSL_not_mem_normalizer ψ hq h2
  have hg₂N : g₂ ∉ normalizer (J₂ : Set (projectiveSL 4 k)) :=
    proj_splitShearTSL_not_mem_normalizer ψ hq h2
  refine ⟨J₁, J₂, fun x => ?_, fun x => ?_, hcomm, ?_, ?_, ⟨t₂, ⟨_, rfl⟩, ht₂o, g₁, hg₁t, hg₁N⟩,
    ⟨t₁, ⟨_, rfl⟩, ht₁o, g₂, hg₂t, hg₂N⟩, fun A hA => ⟨?_, ?_⟩⟩
  · constructor
    · rintro ⟨U, rfl⟩
      exact ⟨U, splitLeftSL ψ hq U, fun v => splitLeftHom_mulVec ψ U v, rfl⟩
    · rintro ⟨U, g, hg, rfl⟩
      refine ⟨U, ?_⟩
      change proj 4 k (splitLeftSL ψ hq U) = _
      congr 1
      apply SpecialLinearGroup.toGL_injective
      rw [toGL_splitLeftSL]
      exact eq_of_mulVec_eq fun v => by rw [splitLeftHom_mulVec]; exact (hg v).symm
  · constructor
    · rintro ⟨W, rfl⟩
      exact ⟨W, splitRightSL ψ hq W, fun v => splitRightHom_mulVec ψ W v, rfl⟩
    · rintro ⟨W, g, hg, rfl⟩
      refine ⟨W, ?_⟩
      change proj 4 k (splitRightSL ψ hq W) = _
      congr 1
      apply SpecialLinearGroup.toGL_injective
      rw [toGL_splitRightSL]
      exact eq_of_mulVec_eq fun v => by rw [splitRightHom_mulVec]; exact (hg v).symm
  · exact ⟨(QuotientGroup.quotientMulEquivOfEq (splitLeftP_ker ψ hq).symm).trans
      (QuotientGroup.quotientKerEquivRange (splitLeftP ψ hq)) |>.symm⟩
  · exact ⟨(QuotientGroup.quotientMulEquivOfEq (splitRightP_ker ψ hq).symm).trans
      (QuotientGroup.quotientKerEquivRange (splitRightP ψ hq)) |>.symm⟩
  · exact not_isStandardSubgroup_conj_map (by norm_num) J₁ ht₂o
      (fun x hx => (hcomm x hx t₂ ⟨_, rfl⟩)) hg₁t hg₁N A hA
  · exact not_isStandardSubgroup_conj_map (by norm_num) J₂ ht₁o
      (fun x hx => (hcomm t₁ ⟨_, rfl⟩ x hx).symm) hg₂t hg₂N A hA

theorem map_conjAut_range_splitLeftHom (hq : 5 ≤ Nat.card k) :
    (splitLeftHom ψ).range.map (conjAut 4 k) = (splitLeftP ψ hq).range.map MulAut.conj := by
  rw [MonoidHom.range_eq_map, MonoidHom.range_eq_map, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext U : 1
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← toGL_splitLeftSL ψ hq, conjAut_toGL]
  rfl

theorem map_conjAut_range_splitRightHom (hq : 5 ≤ Nat.card k) :
    (splitRightHom ψ).range.map (conjAut 4 k) = (splitRightP ψ hq).range.map MulAut.conj := by
  rw [MonoidHom.range_eq_map, MonoidHom.range_eq_map, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext W : 1
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← toGL_splitRightSL ψ hq, conjAut_toGL]
  rfl

theorem not_isStandardSubgroup_of_splitLeft (hodd : Odd (Nat.card k)) (hq : 5 ≤ Nat.card k)
    {A : Type*} [Group A] {ρ : A →* MulAut (projectiveSL 4 k)} (hinj : Function.Injective ρ)
    (hinn : OuterAutomorphisms.inner (projectiveSL 4 k) ≤ ρ.range) {L : Subgroup A}
    (hL : L.map ρ = (splitLeftHom ψ).range.map (conjAut 4 k)) : ¬ IsStandardSubgroup L := by
  classical
  obtain ⟨ℓ, hchar⟩ := CharP.exists k
  have : Fact ℓ.Prime := ⟨CharP.char_is_prime k ℓ⟩
  have h2 : (2 : k) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  rw [map_conjAut_range_splitLeftHom ψ hq] at hL
  refine not_isStandardSubgroup_of_conj_witness (by norm_num) _
    (orderOf_splitRightP_quatI ψ hq h2) ?_ ?_
    (proj_splitShearSL_not_mem_normalizer ψ hq h2 (ℓ := ℓ)) hinj hinn hL
  · rintro _ ⟨U, rfl⟩
    simp only [splitLeftP, splitRightP, MonoidHom.comp_apply, ← map_mul]
    congr 1
    apply SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul, toGL_splitLeftSL, toGL_splitRightSL, splitLeftHom_commute]
  · rw [splitRightP, MonoidHom.comp_apply, ← map_mul, ← map_mul, splitShearSL_commute ψ hq]

theorem not_isStandardSubgroup_of_splitRight (hodd : Odd (Nat.card k)) (hq : 5 ≤ Nat.card k)
    {A : Type*} [Group A] {ρ : A →* MulAut (projectiveSL 4 k)} (hinj : Function.Injective ρ)
    (hinn : OuterAutomorphisms.inner (projectiveSL 4 k) ≤ ρ.range) {L : Subgroup A}
    (hL : L.map ρ = (splitRightHom ψ).range.map (conjAut 4 k)) : ¬ IsStandardSubgroup L := by
  classical
  obtain ⟨ℓ, hchar⟩ := CharP.exists k
  have : Fact ℓ.Prime := ⟨CharP.char_is_prime k ℓ⟩
  have h2 : (2 : k) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  rw [map_conjAut_range_splitRightHom ψ hq] at hL
  refine not_isStandardSubgroup_of_conj_witness (by norm_num) _
    (orderOf_splitLeftP_quatI ψ hq h2) ?_ ?_
    (proj_splitShearTSL_not_mem_normalizer ψ hq h2 (ℓ := ℓ)) hinj hinn hL
  · rintro _ ⟨W, rfl⟩
    simp only [splitLeftP, splitRightP, MonoidHom.comp_apply, ← map_mul]
    congr 1
    apply SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul, toGL_splitLeftSL, toGL_splitRightSL, splitLeftHom_commute]
  · rw [splitLeftP, MonoidHom.comp_apply, ← map_mul, ← map_mul, splitShearTSL_commute ψ hq]

end Theorem

end CFSG.ComponentClassification.OddSelector
