module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ScalarDescent

public section

namespace CFSG.HardMathSupport.U4FF

open scoped TensorProduct Matrix

section

variable {G : Type*} [Group G] {E k : Type*} [Field E] [Field k] {m : ℕ}

noncomputable def matRepr (ρ : G →* GL (Fin m) E) : Representation E G (Fin m → E) :=
  (Matrix.toLinAlgEquiv' (R := E) (n := Fin m)).toMonoidHom.comp
    ((Units.coeHom (Matrix (Fin m) (Fin m) E)).comp ρ)

theorem matRepr_apply (ρ : G →* GL (Fin m) E) (g : G) (v : Fin m → E) :
    matRepr ρ g v = (ρ g : Matrix (Fin m) (Fin m) E) *ᵥ v := by
  simp [matRepr]

theorem exists_conj_of_conj_extend (f : E →+* k) (ρ σ : G →* GL (Fin m) E) (P : GL (Fin m) k)
    (h : ∀ g, (P : Matrix (Fin m) (Fin m) k) * (ρ g : Matrix (Fin m) (Fin m) E).map f =
      (σ g : Matrix (Fin m) (Fin m) E).map f * (P : Matrix (Fin m) (Fin m) k)) :
    ∃ M : GL (Fin m) E, ∀ g, (M : Matrix (Fin m) (Fin m) E) * (ρ g : Matrix (Fin m) (Fin m) E) =
      (σ g : Matrix (Fin m) (Fin m) E) * (M : Matrix (Fin m) (Fin m) E) := by
  classical
  letI : Algebra E k := f.toAlgebra
  let e1 : k ⊗[E] (Fin m → E) ≃ₗ[k] (Fin m → k) := TensorProduct.piScalarRight E k k (Fin m)
  have he1 : ∀ (a : k) (x : Fin m → E), e1 (a ⊗ₜ x) = fun i => f (x i) * a := by
    intro a x
    simp only [e1, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    funext i
    rw [Algebra.smul_def]
    rfl
  have hbase : ∀ (A : Matrix (Fin m) (Fin m) E) (t : k ⊗[E] (Fin m → E)),
      e1 ((Matrix.mulVecLin A).baseChange k t) = A.map f *ᵥ e1 t := by
    intro A t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add t₁ t₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂, Matrix.mulVec_add]
    | tmul a x =>
      rw [LinearMap.baseChange_tmul, he1, he1]
      ext i
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
        Finset.sum_mul, map_sum, map_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
  let Pe : (Fin m → k) ≃ₗ[k] (Fin m → k) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv k (Fin m → k))
      (Matrix.GeneralLinearGroup.toLin P)
  have hPe : ∀ y, Pe y = (P : Matrix (Fin m) (Fin m) k) *ᵥ y := fun y => rfl
  have hmat : ∀ τ : G →* GL (Fin m) E, ∀ g, matRepr τ g =
      Matrix.mulVecLin (τ g : Matrix (Fin m) (Fin m) E) :=
    fun τ g => LinearMap.ext fun v => by rw [matRepr_apply]; rfl
  let Φ : Theory.Representation.extendScalars k (matRepr ρ) ≃ₗ
      Theory.Representation.extendScalars k (matRepr σ) :=
    { toLinearEquiv := (e1.trans Pe).trans e1.symm
      isIntertwining' := fun g => by
        refine LinearMap.ext fun t => ?_
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
          Theory.Representation.extendScalars_apply]
        apply e1.injective
        simp only [hmat, LinearEquiv.apply_symm_apply, hbase, hPe, Matrix.mulVec_mulVec]
        rw [h g] }
  obtain ⟨Ψ⟩ := Theory.Representation.repEquiv_of_extendScalars (matRepr ρ) (matRepr σ) ⟨Φ⟩
  let M : GL (Fin m) E := Matrix.GeneralLinearGroup.toLin.symm
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin m → E)).symm Ψ.toLinearEquiv)
  have hM : ∀ v, (M : Matrix (Fin m) (Fin m) E) *ᵥ v = Ψ v := fun v => by
    have h : Matrix.GeneralLinearGroup.toLin M =
        (LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin m → E)).symm Ψ.toLinearEquiv := by
      simp [M]
    rw [← Matrix.mulVecLin_apply, ← Matrix.GeneralLinearGroup.toLin_apply, h]
    rfl
  refine ⟨M, fun g => ?_⟩
  ext i j
  have := congrFun (Ψ.isIntertwining g (Pi.single j 1)) i
  simp only [matRepr_apply, ← hM, Matrix.mulVec_mulVec] at this
  simpa [Matrix.mulVec_single_one] using this

end

theorem exists_coord_equiv {S : Type} [CommGroup S] {L : Subgroup (MulAut S)} {E E' : Type}
    [Field E] [Field E'] {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} (e : Fin m ≃ ι)
    (ε₀ : S ≃* Multiplicative (Fin m → E)) (R : ↥L →* GL (Fin m) E)
    (hR : ∀ (l : ↥L) (s : S), ε₀ ((l : MulAut S) s) = Multiplicative.ofAdd
      ((R l : Matrix (Fin m) (Fin m) E) *ᵥ Multiplicative.toAdd (ε₀ s)))
    (τ : E ≃+* E') (M : GL (Fin m) E') (ρ : ↥L →* GL ι E')
    (hM : ∀ l : ↥L, (M : Matrix (Fin m) (Fin m) E') * (R l : Matrix (Fin m) (Fin m) E).map τ =
      (ρ l : Matrix ι ι E').submatrix e e * (M : Matrix (Fin m) (Fin m) E')) :
    ∃ ψ : S ≃* Multiplicative (ι → E'), ∀ (l : ↥L) (s : S),
      ψ ((l : MulAut S) s) = Multiplicative.ofAdd
        ((ρ l : Matrix ι ι E') *ᵥ Multiplicative.toAdd (ψ s)) := by
  classical
  let τv : (Fin m → E) ≃+ (Fin m → E') := AddEquiv.piCongrRight fun _ => τ.toAddEquiv
  let Mv : (Fin m → E') ≃+ (Fin m → E') :=
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv E' (Fin m → E'))
      (Matrix.GeneralLinearGroup.toLin M)).toAddEquiv
  have hMv : ∀ x, Mv x = (M : Matrix (Fin m) (Fin m) E') *ᵥ x := fun x => rfl
  let rvv : (Fin m → E') ≃+ (ι → E') := (LinearEquiv.funCongrLeft E' E' e.symm).toAddEquiv
  have hrvv : ∀ x i, rvv x i = x (e.symm i) := fun x i => rfl
  have hτv : ∀ x i, τv x i = τ (x i) := fun x i => rfl
  refine ⟨ε₀.trans (AddEquiv.toMultiplicative (τv.trans (Mv.trans rvv))), fun l s => ?_⟩
  have key : ∀ x : Fin m → E,
      rvv (Mv (τv ((R l : Matrix (Fin m) (Fin m) E) *ᵥ x))) =
        (ρ l : Matrix ι ι E') *ᵥ rvv (Mv (τv x)) := by
    intro x
    have h1 : τv ((R l : Matrix (Fin m) (Fin m) E) *ᵥ x) =
        (R l : Matrix (Fin m) (Fin m) E).map τ *ᵥ τv x := by
      funext i
      rw [hτv]
      exact RingHom.map_mulVec τ.toRingHom _ _ i
    rw [h1, hMv, hMv, Matrix.mulVec_mulVec, hM l, ← Matrix.mulVec_mulVec]
    funext i
    rw [hrvv, Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct]
    simp only [Matrix.submatrix_apply, hrvv]
    rw [← Equiv.sum_comp e]
    simp
  simp only [MulEquiv.trans_apply]
  change Multiplicative.ofAdd (rvv (Mv (τv (Multiplicative.toAdd (ε₀ ((l : MulAut S) s)))))) = _
  rw [hR l s]
  simp only [toAdd_ofAdd]
  rw [key]
  rfl

end CFSG.HardMathSupport.U4FF
