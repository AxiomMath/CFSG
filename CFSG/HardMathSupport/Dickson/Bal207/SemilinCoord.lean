module

public import CFSG.HardMathSupport.Dickson.Bal207.FCBlock
public import CFSG.RankThree.CentralLift.DefiningUnitary
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarConj

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

variable {E : Type} [Field E] {W : Type*} [AddCommGroup W] [Module E W]

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι E W)

@[expose] noncomputable def semMat (T : W → W) : Matrix ι ι E :=
  Matrix.of fun i j => b.repr (T (b j)) i

theorem semMat_apply (T : W → W) (i j : ι) : semMat b T i j = b.repr (T (b j)) i := rfl

theorem repr_semilin {τ : E →+* E} {T : W →+ W} (hT : ∀ (c : E) (v : W), T (c • v) = τ c • T v)
    (v : W) : b.equivFun (T v) = semMat b T *ᵥ (τ ∘ b.equivFun v) := by
  conv_lhs => rw [← b.sum_equivFun v]
  rw [map_sum]
  simp only [hT, map_sum, map_smul]
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, semMat_apply,
    Function.comp_apply, Module.Basis.equivFun_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem semMat_comp {τ : E →+* E} {T : W →+ W} (hT : ∀ (c : E) (v : W), T (c • v) = τ c • T v)
    (T' : W → W) : semMat b (fun v => T (T' v)) = semMat b T * (semMat b T').map τ := by
  ext i j
  have h := congrFun (repr_semilin b hT (T' (b j))) i
  rw [Module.Basis.equivFun_apply] at h
  rw [semMat_apply, h, mul_apply]
  simp only [mulVec, dotProduct, Function.comp_apply, Module.Basis.equivFun_apply, map_apply,
    semMat_apply]

theorem semMat_toLin' (M : GL ι E) :
    semMat b (fun v => ((Matrix.GeneralLinearGroup.toLin' b M : LinearMap.GeneralLinearGroup E W) :
      W →ₗ[E] W) v) = M := by
  ext i j
  rw [semMat_apply, ← Module.Basis.equivFun_apply,
    CFSG.RankThree.CentralLift.equivFun_toLin'_basis_apply]
  simp [mulVec, dotProduct, Module.Basis.equivFun_self]

theorem semMat_id : semMat b (id : W → W) = 1 := by
  ext i j
  rw [semMat_apply, id_eq, Module.Basis.repr_self_apply, Matrix.one_apply]
  by_cases h : i = j <;> simp [h, eq_comm]

theorem semMat_mul_symm (S : W ≃+ W) {τ : E ≃+* E}
    (hS : ∀ (c : E) (v : W), S (c • v) = τ c • S v) :
    semMat b S * (semMat b S.symm).map (τ : E →+* E) = 1 := by
  have h := semMat_comp b (τ := (τ : E →+* E)) (T := (S : W →+ W)) hS
    (fun v => (S.symm : W → W) v)
  have hfun : (fun v => (S : W →+ W) ((S.symm : W → W) v)) = id := funext S.apply_symm_apply
  rw [hfun, semMat_id] at h
  exact h.symm

theorem semMat_symm_mul (S : W ≃+ W) {τ : E ≃+* E}
    (hS : ∀ (c : E) (v : W), S (c • v) = τ c • S v) :
    (semMat b S.symm).map (τ : E →+* E) * semMat b S = 1 := by
  have h := semMat_comp b (τ := (τ.symm : E →+* E)) (T := (S.symm : W →+ W))
    (CFSG.RankThree.PartOne.KCOrthogonal.semilin_symm_smul S τ hS) (fun v => (S : W → W) v)
  have hfun : (fun v => (S.symm : W →+ W) ((S : W → W) v)) = id :=
    funext S.symm_apply_apply
  rw [hfun, semMat_id] at h
  have hmap : ((semMat b S).map (τ.symm : E →+* E)).map (τ : E →+* E) = semMat b S := by
    ext i j
    simp
  have hmap_one : (1 : Matrix ι ι E).map (τ : E →+* E) = 1 := by
    ext i j
    simp [Matrix.one_apply]
  have h' := congrArg (fun M : Matrix ι ι E => M.map (τ : E →+* E)) h
  rw [hmap_one, Matrix.map_mul, hmap] at h'
  exact h'.symm

@[expose] noncomputable def semMatUnit (S : W ≃+ W) {τ : E ≃+* E}
    (hS : ∀ (c : E) (v : W), S (c • v) = τ c • S v) : GL ι E :=
  Units.mk (semMat b S) ((semMat b S.symm).map (τ : E →+* E))
    (semMat_mul_symm b S hS) (semMat_symm_mul b S hS)

@[simp] theorem coe_semMatUnit (S : W ≃+ W) {τ : E ≃+* E}
    (hS : ∀ (c : E) (v : W), S (c • v) = τ c • S v) :
    ((semMatUnit b S hS : GL ι E) : Matrix ι ι E) = semMat b S := rfl

@[simp] theorem coe_semMatUnit_inv (S : W ≃+ W) {τ : E ≃+* E}
    (hS : ∀ (c : E) (v : W), S (c • v) = τ c • S v) :
    (((semMatUnit b S hS)⁻¹ : GL ι E) : Matrix ι ι E) =
      (semMat b S.symm).map (τ : E →+* E) := rfl

theorem semMat_conj_semilin (S : W ≃+ W) {τ : E ≃+* E}
    (hS : ∀ (c : E) (v : W), S (c • v) = τ c • S v)
    {u u' : W →ₗ[E] W} (hu' : ∀ v, u' v = S (u (S.symm v))) :
    semMat b (fun v => u' v) =
      semMat b S * (semMat b (fun v => u v)).map (τ : E →+* E) *
        (semMat b S.symm).map (τ : E →+* E) := by
  have h1 := semMat_comp b (τ := (τ : E →+* E)) (T := (S : W →+ W)) hS
    (fun v => u ((S.symm : W → W) v))
  have hfun : (fun v => (S : W →+ W) (u ((S.symm : W → W) v))) = fun v => u' v :=
    funext fun v => (hu' v).symm
  rw [hfun] at h1
  have h2 := semMat_comp b (τ := (RingHom.id E)) (T := u.toAddMonoidHom)
    (fun c v => by simp) (fun v => (S.symm : W → W) v)
  have hmap_id : (semMat b S.symm).map (RingHom.id E) = semMat b S.symm := by
    ext i j
    rfl
  change semMat b (fun v => u ((S.symm : W → W) v)) =
      semMat b (fun v => u v) * (semMat b S.symm).map (RingHom.id E) at h2
  rw [hmap_id] at h2
  rw [h2, Matrix.map_mul] at h1
  have hScoe : semMat b (S : W →+ W) = semMat b (fun v => S v) := rfl
  have hSsymm_coe : semMat b (S.symm : W →+ W) = semMat b (fun v => S.symm v) := rfl
  simpa only [hScoe, hSsymm_coe, Matrix.mul_assoc] using h1

theorem toLin'_symm_conj_semilin (S : W ≃+ W) {τ : E ≃+* E}
    (hS : ∀ (c : E) (v : W), S (c • v) = τ c • S v)
    (g g' : LinearMap.GeneralLinearGroup E W)
    (hg' : ∀ v, (g' : W →ₗ[E] W) v = S ((g : W →ₗ[E] W) (S.symm v))) :
    (Matrix.GeneralLinearGroup.toLin' b).symm g' =
      semMatUnit b S hS * Matrix.GeneralLinearGroup.map (τ : E →+* E)
        ((Matrix.GeneralLinearGroup.toLin' b).symm g) * (semMatUnit b S hS)⁻¹ := by
  let Cg := (Matrix.GeneralLinearGroup.toLin' b).symm g
  let Cg' := (Matrix.GeneralLinearGroup.toLin' b).symm g'
  have hu' : ∀ v,
      ((Matrix.GeneralLinearGroup.toLin' b Cg' : LinearMap.GeneralLinearGroup E W) :
        W →ₗ[E] W) v =
      S (((Matrix.GeneralLinearGroup.toLin' b Cg : LinearMap.GeneralLinearGroup E W) :
        W →ₗ[E] W) (S.symm v)) := by
    intro v
    simpa only [Cg, Cg', MulEquiv.apply_symm_apply] using hg' v
  have hmat := semMat_conj_semilin b S hS
    (u := ((Matrix.GeneralLinearGroup.toLin' b Cg : LinearMap.GeneralLinearGroup E W) :
      W →ₗ[E] W))
    (u' := ((Matrix.GeneralLinearGroup.toLin' b Cg' : LinearMap.GeneralLinearGroup E W) :
      W →ₗ[E] W)) hu'
  rw [semMat_toLin', semMat_toLin'] at hmat
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  rw [show ((Matrix.GeneralLinearGroup.map (τ : E →+* E) Cg : GL ι E) :
      Matrix ι ι E) = (Cg : Matrix ι ι E).map (τ : E →+* E) from rfl]
  rw [coe_semMatUnit, coe_semMatUnit_inv]
  exact hmat

end General

variable {n : ℕ} (b : Module.Basis (Fin n) E W)

variable {ℓ f : ℕ} (h : UnitaryFieldData ℓ f E)

theorem semMat_unitary {H : W →ₛₗ[h.bar] W →ₗ[E] E}
    (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0) {T : W → W}
    (hT : ∀ i j, H (T (b i)) (T (b j)) = if i = j then 1 else 0) :
    ((semMat b T).map h.bar)ᵀ * semMat b T = 1 := by
  ext i j
  have h1 := CFSG.RankThree.CentralLift.form_eq_gramForm h b
    (G := (1 : Matrix (Fin n) (Fin n) E)) (fun i j => by rw [hb, one_apply]) (T (b i)) (T (b j))
  rw [hT, gramForm_apply, Matrix.one_mulVec] at h1
  rw [one_apply, h1, mul_apply]
  simp only [dotProduct, transpose_apply, map_apply, semMat_apply, Module.Basis.equivFun_apply]

@[expose] noncomputable def semU {T : W → W} (hM : ((semMat b T).map h.bar)ᵀ * semMat b T = 1) :
    primeFormUnitary h (oneGram E n) :=
  ⟨⟨semMat b T, ((semMat b T).map h.bar)ᵀ, mul_eq_one_comm.mp hM, hM⟩, by
    change ((semMat b T).map h.bar)ᵀ * ((1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
      semMat b T = ((1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)
    rw [Units.val_one, Matrix.mul_one, hM]⟩

theorem coe_semU {T : W → W} (hM : ((semMat b T).map h.bar)ᵀ * semMat b T = 1) :
    ((semU b h hM : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = semMat b T := rfl

@[expose] noncomputable def semGamma {T : W → W}
    (hM : ((semMat b T).map h.bar)ᵀ * semMat b T = 1) (τ : E ≃+* E) : blockGamma h n :=
  ⟨semU b h hM, τ⟩

theorem semGamma_mul {τ τ' : E ≃+* E} {T : W →+ W} (hT : ∀ (c : E) (v : W), T (c • v) = τ c • T v)
    {T' T'' : W → W} (hTT : ∀ v, T'' v = T (T' v))
    (hM : ((semMat b T).map h.bar)ᵀ * semMat b T = 1)
    (hM' : ((semMat b T').map h.bar)ᵀ * semMat b T' = 1)
    (hM'' : ((semMat b T'').map h.bar)ᵀ * semMat b T'' = 1) :
    semGamma b h hM'' (τ * τ') = semGamma b h hM τ * semGamma b h hM' τ' := by
  refine SemidirectProduct.ext (Subtype.ext (Units.ext ?_)) rfl
  rw [SemidirectProduct.mul_left]
  change semMat b T'' = semMat b T * ((glAut τ (semU b h hM' : GL (Fin n) E) : GL (Fin n) E) :
    Matrix (Fin n) (Fin n) E)
  rw [coe_glAut, coe_semU, show T'' = fun v => T (T' v) from funext hTT]
  exact semMat_comp b (τ := (τ : E →+* E)) hT T'

theorem semGamma_one_eq_inl {T : W → W} (hM : ((semMat b T).map h.bar)ᵀ * semMat b T = 1)
    {M : primeFormUnitary h (oneGram E n)}
    (hTM : ∀ v, T v = ((Matrix.GeneralLinearGroup.toLin' b (M : GL (Fin n) E) :
      LinearMap.GeneralLinearGroup E W) : W →ₗ[E] W) v) :
    semGamma b h hM 1 = SemidirectProduct.inl M := by
  refine SemidirectProduct.ext (Subtype.ext (Units.ext ?_)) rfl
  change semMat b T = _
  rw [show T = _ from funext hTM, semMat_toLin']
  rfl

theorem toLin'_mem_sesqUnitaryGroup_iff {H : W →ₛₗ[h.bar] W →ₗ[E] E}
    (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0) (M : GL (Fin n) E) :
    Matrix.GeneralLinearGroup.toLin' b M ∈ sesqUnitaryGroup H ↔
      M ∈ primeFormUnitary h (oneGram E n) := by
  have he : ∀ i j, H (b i) (b j) = (1 : Matrix (Fin n) (Fin n) E) i j := fun i j => by
    rw [hb, one_apply]
  rw [mem_sesqUnitaryGroup]
  change _ ↔ ((M : Matrix (Fin n) (Fin n) E).map h.bar)ᵀ *
    ((1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * M =
      ((1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)
  rw [Units.val_one, ← gramForm_isometry_iff]
  constructor
  · intro hiso u v
    have huv := hiso (b.equivFun.symm u) (b.equivFun.symm v)
    simpa only [CFSG.RankThree.CentralLift.form_eq_gramForm h b he,
      CFSG.RankThree.CentralLift.equivFun_toLin'_basis_apply, LinearEquiv.apply_symm_apply]
      using huv
  · intro hiso x y
    rw [CFSG.RankThree.CentralLift.form_eq_gramForm h b he,
      CFSG.RankThree.CentralLift.form_eq_gramForm h b he,
      CFSG.RankThree.CentralLift.equivFun_toLin'_basis_apply,
      CFSG.RankThree.CentralLift.equivFun_toLin'_basis_apply, hiso]

theorem map_toLin'_primeFormUnitary {H : W →ₛₗ[h.bar] W →ₗ[E] E}
    (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0) :
    (primeFormUnitary h (oneGram E n)).map (Matrix.GeneralLinearGroup.toLin' b).toMonoidHom =
      sesqUnitaryGroup H := by
  ext g
  constructor
  · rintro ⟨M, hM, rfl⟩
    exact (toLin'_mem_sesqUnitaryGroup_iff b h hb M).2 hM
  · intro hg
    refine ⟨(Matrix.GeneralLinearGroup.toLin' b).symm g,
      (toLin'_mem_sesqUnitaryGroup_iff b h hb _).1 ?_, MulEquiv.apply_symm_apply _ g⟩
    rwa [MulEquiv.apply_symm_apply]

@[expose] noncomputable def unitaryEquivOfBasis {H : W →ₛₗ[h.bar] W →ₗ[E] E}
    (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0) :
    primeFormUnitary h (oneGram E n) ≃* sesqUnitaryGroup H :=
  ((Matrix.GeneralLinearGroup.toLin' b).subgroupMap _).trans
    (MulEquiv.subgroupCongr (map_toLin'_primeFormUnitary b h hb))

end CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

end
