module

public import Mathlib.RingTheory.Norm.Defs
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Permutation

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

section Construction

variable (F : Type) {L : Type} [Field F] [Field L] [Algebra F L]

private noncomputable def wcPBMul {r : ℕ} (u : Fin r → Lˣ) : (Fin r → L) ≃ₗ[F] (Fin r → L) :=
  LinearEquiv.piCongrRight fun i => DistribMulAction.toModuleAut F L (u i)

private theorem wcPBMul_apply {r : ℕ} (u : Fin r → Lˣ) (v : Fin r → L) (i : Fin r) :
    wcPBMul F u v i = (u i : L) * v i := rfl

private theorem wcPBMul_mul {r : ℕ} (u v : Fin r → Lˣ) :
    wcPBMul F u * wcPBMul F v = wcPBMul F (u * v) := by
  ext x i
  show (u i : L) * ((v i : L) * x i) = ((u i * v i : Lˣ) : L) * x i
  rw [Units.val_mul, mul_assoc]

private theorem wcPBMul_comm {r : ℕ} (u v : Fin r → Lˣ) :
    wcPBMul F u * wcPBMul F v = wcPBMul F v * wcPBMul F u := by
  rw [wcPBMul_mul, wcPBMul_mul, mul_comm]

private noncomputable def wcPBT {r : ℕ} {G : Type} [Monoid G] (ρ : G →* Lˣ) :
    (Fin r → G) →* ((Fin r → L) ≃ₗ[F] (Fin r → L)) where
  toFun c := wcPBMul F fun i => ρ (c i)
  map_one' := by
    ext v i
    show ((ρ ((1 : Fin r → G) i) : Lˣ) : L) * v i = v i
    rw [Pi.one_apply, map_one, Units.val_one, one_mul]
  map_mul' c d := by
    ext v i
    show ((ρ ((c * d) i) : Lˣ) : L) * v i = ((ρ (c i) : Lˣ) : L) * (((ρ (d i) : Lˣ) : L) * v i)
    rw [Pi.mul_apply, map_mul, Units.val_mul, mul_assoc]

private theorem wcPBT_apply {r : ℕ} {G : Type} [Monoid G] (ρ : G →* Lˣ) (c : Fin r → G) :
    wcPBT F ρ c = wcPBMul F fun i => ρ (c i) := rfl

private noncomputable def wcPBPerm {r : ℕ} :
    Equiv.Perm (Fin r) →* ((Fin r → L) ≃ₗ[F] (Fin r → L)) where
  toFun σ := LinearEquiv.funCongrLeft F L σ⁻¹
  map_one' := by
    ext v i
    rfl
  map_mul' σ τ := by
    ext v i
    rfl

private theorem wcPBPerm_apply {r : ℕ} (σ : Equiv.Perm (Fin r)) (v : Fin r → L) (i : Fin r) :
    wcPBPerm F σ v i = v (σ⁻¹ i) := rfl

private theorem wcPBPerm_conj {r : ℕ} (σ : Equiv.Perm (Fin r)) (u : Fin r → Lˣ) :
    wcPBPerm F σ * wcPBMul F u * (wcPBPerm F σ)⁻¹ = wcPBMul F (u ∘ ⇑σ⁻¹) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext v i
  rfl

private noncomputable def wcPBFrob {r : ℕ} (φ : L ≃ₐ[F] L) (i : Fin r) :
    (Fin r → L) ≃ₗ[F] (Fin r → L) :=
  LinearEquiv.piCongrRight
    (Function.update (fun _ : Fin r => LinearEquiv.refl F L) i φ.toLinearEquiv)

private theorem wcPBFrob_apply_self {r : ℕ} (φ : L ≃ₐ[F] L) (i : Fin r) (v : Fin r → L) :
    wcPBFrob F φ i v i = φ (v i) := by
  simp [wcPBFrob]

private theorem wcPBFrob_apply_of_ne {r : ℕ} (φ : L ≃ₐ[F] L) {i j : Fin r} (h : j ≠ i)
    (v : Fin r → L) : wcPBFrob F φ i v j = v j := by
  simp [wcPBFrob, Function.update_of_ne h]

private theorem wcPBFrob_conj {r : ℕ} (φ : L ≃ₐ[F] L) (i : Fin r) (u u' : Fin r → Lˣ)
    (h1 : ∀ j, j ≠ i → u' j = u j) (h2 : (u' i : L) = φ (u i)) :
    wcPBFrob F φ i * wcPBMul F u * (wcPBFrob F φ i)⁻¹ = wcPBMul F u' := by
  rw [mul_inv_eq_iff_eq_mul]
  ext v j
  by_cases hj : j = i
  · rw [hj]
    show wcPBFrob F φ i (wcPBMul F u v) i = wcPBMul F u' (wcPBFrob F φ i v) i
    rw [wcPBFrob_apply_self, wcPBMul_apply, wcPBMul_apply, wcPBFrob_apply_self, map_mul, h2]
  · show wcPBFrob F φ i (wcPBMul F u v) j = wcPBMul F u' (wcPBFrob F φ i v) j
    rw [wcPBFrob_apply_of_ne F φ hj, wcPBMul_apply, wcPBMul_apply, wcPBFrob_apply_of_ne F φ hj,
      h1 j hj]

private theorem wcPB_det_toModuleAut [Module.Finite F L] (u : Lˣ) :
    LinearMap.det ((DistribMulAction.toModuleAut F L u : L ≃ₗ[F] L) : L →ₗ[F] L) =
      Algebra.norm F (u : L) := by
  rw [Algebra.norm_apply]
  congr 1

private theorem wcPBMul_det [Module.Finite F L] {r : ℕ} (u : Fin r → Lˣ) :
    LinearMap.det ((wcPBMul F u : (Fin r → L) ≃ₗ[F] (Fin r → L)) :
        (Fin r → L) →ₗ[F] (Fin r → L)) = ∏ i, Algebra.norm F (u i : L) := by
  have h : ((wcPBMul F u : (Fin r → L) ≃ₗ[F] (Fin r → L)) : (Fin r → L) →ₗ[F] (Fin r → L)) =
      LinearMap.pi (fun i => (((DistribMulAction.toModuleAut F L (u i) : L ≃ₗ[F] L) :
        L →ₗ[F] L)).comp (LinearMap.proj i)) := by
    ext v j
    rfl
  rw [h, LinearMap.det_pi]
  exact Finset.prod_congr rfl fun i _ => wcPB_det_toModuleAut F (u i)


variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module F V]

private noncomputable def wcPBMat (b : Module.Basis ι F V) : (V ≃ₗ[F] V) ≃* GL ι F :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv F V).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv)

private theorem wcPBMat_det (b : Module.Basis ι F V) (g : V ≃ₗ[F] V) :
    ((wcPBMat F b g : GL ι F) : Matrix ι ι F).det = LinearMap.det (g : V →ₗ[F] V) := by
  rw [← LinearMap.det_toMatrix b]
  rfl

private noncomputable def wcPBBasis {e : ℕ} (bL : Module.Basis (Fin e) F L) (r : ℕ) :
    Module.Basis (Fin r × Fin e) F (Fin r → L) :=
  (Pi.basis fun _ : Fin r => bL).reindex (Equiv.sigmaEquivProd (Fin r) (Fin e))

private theorem wcPBBasis_apply {e : ℕ} (bL : Module.Basis (Fin e) F L) (r : ℕ) (j : Fin r)
    (l : Fin e) : wcPBBasis F bL r (j, l) = Pi.single j (bL l) := by
  simp [wcPBBasis]

private theorem wcPBPerm_single {r : ℕ} (σ : Equiv.Perm (Fin r)) (j : Fin r) (x : L) :
    wcPBPerm F σ (Pi.single j x) = Pi.single (σ j) x := by
  ext m
  simp [wcPBPerm_apply, Pi.single_apply, Equiv.symm_apply_eq]

private theorem wcPBPerm_basis {e : ℕ} (bL : Module.Basis (Fin e) F L) {r : ℕ}
    (σ : Equiv.Perm (Fin r)) (j : Fin r) (l : Fin e) :
    wcPBPerm F σ (wcPBBasis F bL r (j, l)) = wcPBBasis F bL r (σ j, l) := by
  rw [wcPBBasis_apply, wcPBBasis_apply, wcPBPerm_single]

private theorem wcPBPerm_det {e : ℕ} (bL : Module.Basis (Fin e) F L) {r : ℕ}
    (σ : Equiv.Perm (Fin r)) :
    LinearMap.det ((wcPBPerm F σ : (Fin r → L) ≃ₗ[F] (Fin r → L)) :
        (Fin r → L) →ₗ[F] (Fin r → L)) = (((Equiv.Perm.sign σ ^ e : ℤˣ) : ℤ) : F) := by
  have hmat : LinearMap.toMatrix (wcPBBasis F bL r) (wcPBBasis F bL r)
      ((wcPBPerm F σ : (Fin r → L) ≃ₗ[F] (Fin r → L)) : (Fin r → L) →ₗ[F] (Fin r → L)) =
      Matrix.transpose (Equiv.Perm.permMatrix F (Equiv.prodCongr σ (Equiv.refl (Fin e))) :
        Matrix (Fin r × Fin e) (Fin r × Fin e) F) := by
    ext ⟨i, k⟩ ⟨j, l⟩
    rw [LinearMap.toMatrix_apply]
    show (wcPBBasis F bL r).repr (wcPBPerm F σ (wcPBBasis F bL r (j, l))) (i, k) = _
    rw [wcPBPerm_basis, Module.Basis.repr_self, Finsupp.single_apply]
    simp
  have hsign : Equiv.Perm.sign (Equiv.prodCongr σ (Equiv.refl (Fin e))) =
      Equiv.Perm.sign σ ^ e := by
    have h : Equiv.prodCongr σ (Equiv.refl (Fin e)) = Equiv.prodCongrLeft (fun _ : Fin e => σ) := by
      ext ⟨a, b⟩ <;> rfl
    rw [h, Equiv.Perm.sign_prodCongrLeft]
    simp
  rw [← LinearMap.det_toMatrix (wcPBBasis F bL r), hmat, Matrix.det_transpose,
    Matrix.det_permutation, hsign]

private noncomputable def wcPBEmb (r s : ℕ) :
    ((Fin r → L) ≃ₗ[F] (Fin r → L)) →*
      (((Fin r → L) × (Fin s → F)) ≃ₗ[F] ((Fin r → L) × (Fin s → F))) where
  toFun g := g.prodCongr (LinearEquiv.refl F (Fin s → F))
  map_one' := by
    ext <;> rfl
  map_mul' g h := by
    ext <;> rfl

private theorem wcPBEmb_det [Module.Finite F L] {r s : ℕ} (g : (Fin r → L) ≃ₗ[F] (Fin r → L)) :
    LinearMap.det ((wcPBEmb F r s g : ((Fin r → L) × (Fin s → F)) ≃ₗ[F]
        ((Fin r → L) × (Fin s → F))) : ((Fin r → L) × (Fin s → F)) →ₗ[F]
        ((Fin r → L) × (Fin s → F))) =
      LinearMap.det (g : (Fin r → L) →ₗ[F] (Fin r → L)) := by
  have h : ((wcPBEmb F r s g : ((Fin r → L) × (Fin s → F)) ≃ₗ[F] ((Fin r → L) × (Fin s → F))) :
      ((Fin r → L) × (Fin s → F)) →ₗ[F] ((Fin r → L) × (Fin s → F))) =
      LinearMap.prodMap (g : (Fin r → L) →ₗ[F] (Fin r → L)) LinearMap.id := by
    ext <;> rfl
  rw [h, LinearMap.det_prodMap, LinearMap.det_id, mul_one]

private theorem wcPBEmb_injective (r s : ℕ) : Function.Injective (wcPBEmb (L := L) F r s) := by
  intro g h hgh
  ext v i
  have := congrArg (fun e : ((Fin r → L) × (Fin s → F)) ≃ₗ[F] ((Fin r → L) × (Fin s → F)) =>
    ((e (v, 0)).1) i) hgh
  exact this

end Construction

theorem exists_blockFrame (F : Type) [Field F] [Finite F] {L : Type} [Field L] [Algebra F L]
    [Finite L] {G : Type} [Monoid G] (ρ : G →* Lˣ) (hρ : Function.Injective ρ) (r s n : ℕ)
    (hn : Module.finrank F L * r + s = n) (hr : 0 < r) :
    ∃ (T : (Fin r → G) →* GL (Fin n) F) (S : Equiv.Perm (Fin r) →* GL (Fin n) F)
      (Fr : Fin r → GL (Fin n) F),
      Function.Injective T ∧
      (∀ c, ((T c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det =
        ∏ i, Algebra.norm F ((ρ (c i) : Lˣ) : L)) ∧
      (∀ σ c, S σ * T c * (S σ)⁻¹ = T (c ∘ ⇑(σ⁻¹ : Equiv.Perm (Fin r)))) ∧
      (∀ σ, ((S σ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det =
        ((((Equiv.Perm.sign σ) ^ Module.finrank F L : ℤˣ) : ℤ) : F)) ∧
      (∀ i c, Fr i * T c * (Fr i)⁻¹ = T (Function.update c i (c i ^ Nat.card F))) ∧
      (∀ z : Fˣ, ∃ u : GL (Fin n) F, (∀ c, u * T c * u⁻¹ = T c) ∧
        ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = z) := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Module.Finite F L := Module.Finite.of_finite
  have hV : Module.finrank F ((Fin r → L) × (Fin s → F)) = n := by
    rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_fin_fun]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [← hn, mul_comm]
  let b : Module.Basis (Fin n) F ((Fin r → L) × (Fin s → F)) := Module.finBasisOfFinrankEq F _ hV
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (((Fin r → L) × (Fin s → F)) ≃ₗ[F] ((Fin r → L) × (Fin s → F))) ≃*
        GL (Fin n) F, ∀ g, ((Φ g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det =
        LinearMap.det (g : ((Fin r → L) × (Fin s → F)) →ₗ[F] ((Fin r → L) × (Fin s → F))) :=
    ⟨wcPBMat F b, wcPBMat_det F b⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : L ≃ₐ[F] L, ∀ x : L, φ x = x ^ Nat.card F :=
    ⟨FiniteField.frobeniusAlgEquivOfAlgebraic F L, fun x => by
      rw [Nat.card_eq_fintype_card]; rfl⟩
  have hTinj : Function.Injective (wcPBT F ρ : (Fin r → G) →* _) := by
    intro c d h
    funext i
    apply hρ
    apply Units.ext
    have := congrArg (fun g : (Fin r → L) ≃ₗ[F] (Fin r → L) => g (fun _ => (1 : L)) i) h
    simpa [wcPBT_apply, wcPBMul_apply] using this
  refine ⟨Φ.toMonoidHom.comp ((wcPBEmb F r s).comp (wcPBT F ρ)),
    Φ.toMonoidHom.comp ((wcPBEmb F r s).comp (wcPBPerm F)),
    fun i => Φ (wcPBEmb F r s (wcPBFrob F φ i)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c d h
    exact hTinj (wcPBEmb_injective F r s (Φ.injective h))
  · intro c
    show ((Φ (wcPBEmb F r s (wcPBT F ρ c)) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F).det = _
    rw [hΦ, wcPBEmb_det, wcPBT_apply, wcPBMul_det]
  · intro σ c
    show Φ (wcPBEmb F r s (wcPBPerm F σ)) * Φ (wcPBEmb F r s (wcPBT F ρ c)) *
        (Φ (wcPBEmb F r s (wcPBPerm F σ)))⁻¹ =
      Φ (wcPBEmb F r s (wcPBT F ρ (c ∘ ⇑σ⁻¹)))
    rw [← map_inv, ← map_mul, ← map_mul]
    refine congrArg Φ ?_
    rw [← map_inv, ← map_mul, ← map_mul]
    refine congrArg (wcPBEmb F r s) ?_
    rw [wcPBT_apply, wcPBT_apply]
    exact wcPBPerm_conj F σ _
  · intro σ
    show ((Φ (wcPBEmb F r s (wcPBPerm F σ)) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F).det = _
    rw [hΦ, wcPBEmb_det, wcPBPerm_det F (Module.finBasis F L) σ]
  · intro i c
    show Φ (wcPBEmb F r s (wcPBFrob F φ i)) * Φ (wcPBEmb F r s (wcPBT F ρ c)) *
        (Φ (wcPBEmb F r s (wcPBFrob F φ i)))⁻¹ =
      Φ (wcPBEmb F r s (wcPBT F ρ (Function.update c i (c i ^ Nat.card F))))
    rw [← map_inv, ← map_mul, ← map_mul]
    refine congrArg Φ ?_
    rw [← map_inv, ← map_mul, ← map_mul]
    refine congrArg (wcPBEmb F r s) ?_
    rw [wcPBT_apply, wcPBT_apply]
    refine wcPBFrob_conj F φ i _ _ (fun j hj => ?_) ?_
    · show ρ (Function.update c i (c i ^ Nat.card F) j) = ρ (c j)
      rw [Function.update_of_ne hj]
    · show ((ρ (Function.update c i (c i ^ Nat.card F) i) : Lˣ) : L) = φ ((ρ (c i) : Lˣ) : L)
      rw [Function.update_self, map_pow, Units.val_pow_eq_pow_val, hφ]
  · intro z
    obtain ⟨w, hw⟩ := FiniteField.unitsMap_norm_surjective F L z
    have hwz : Algebra.norm F (w : L) = (z : F) := by
      have := congrArg Units.val hw
      simpa using this
    let i₀ : Fin r := ⟨0, hr⟩
    refine ⟨Φ (wcPBEmb F r s (wcPBMul F (Function.update 1 i₀ w))), fun c => ?_, ?_⟩
    · show Φ (wcPBEmb F r s (wcPBMul F (Function.update 1 i₀ w))) *
          Φ (wcPBEmb F r s (wcPBT F ρ c)) *
          (Φ (wcPBEmb F r s (wcPBMul F (Function.update 1 i₀ w))))⁻¹ =
        Φ (wcPBEmb F r s (wcPBT F ρ c))
      rw [← map_inv, ← map_mul, ← map_mul]
      refine congrArg Φ ?_
      rw [← map_inv, ← map_mul, ← map_mul]
      refine congrArg (wcPBEmb F r s) ?_
      rw [wcPBT_apply, mul_inv_eq_iff_eq_mul, wcPBMul_comm]
    · rw [hΦ, wcPBEmb_det, wcPBMul_det, Finset.prod_eq_single i₀]
      · rw [Function.update_self]
        exact hwz
      · intro j _ hj
        rw [Function.update_of_ne hj]
        simp
      · intro h
        exact absurd (Finset.mem_univ i₀) h

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
