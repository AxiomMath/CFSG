module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsForm
public import CFSG.GroupTheory.WeirSylow.FormSpace
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Open.MatrixModelCore
public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt CFSG.GroupTheory.WeirSylow CFSG.Open Matrix
open scoped IsMulCommutative

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

@[expose] noncomputable def glEquiv : GL ι K ≃* ((ι → K) ≃ₗ[K] (ι → K)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K))

theorem glEquiv_apply (g : GL ι K) (v : ι → K) : glEquiv g v = (g : Matrix ι ι K) *ᵥ v := by
  simp [glEquiv, LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv,
    Matrix.GeneralLinearGroup.toLin_apply]

@[expose] noncomputable def glRep (A : Subgroup (GL ι K)) : Representation K A (ι → K) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (glEquiv.toMonoidHom.comp A.subtype)

theorem glRep_apply (A : Subgroup (GL ι K)) (a : A) (v : ι → K) :
    glRep A a v = ((a : GL ι K) : Matrix ι ι K) *ᵥ v :=
  glEquiv_apply (a : GL ι K) v

theorem glRep_apply_eq_glEquiv (A : Subgroup (GL ι K)) (a : A) (v : ι → K) :
    glRep A a v = glEquiv (a : GL ι K) v :=
  rfl

theorem glRep_injective (A : Subgroup (GL ι K)) : Function.Injective (glRep A) := by
  intro a b h
  apply Subtype.ext
  apply glEquiv.injective
  exact LinearEquiv.ext fun v => congrArg (fun f : Module.End K (ι → K) => f v) h

variable {σ : K →+* K}

@[expose] noncomputable def isomGL (β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K) : Subgroup (GL ι K) :=
  (formIsometryGroup K (fun x y => β x y)).comap glEquiv.toMonoidHom

theorem mem_isomGL {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K} {g : GL ι K} :
    g ∈ isomGL β ↔ ∀ x y, β ((g : Matrix ι ι K) *ᵥ x) ((g : Matrix ι ι K) *ᵥ y) = β x y := by
  simp only [isomGL, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, mem_formIsometryGroup,
    glEquiv_apply]

@[expose] noncomputable def centGL (𝒮 : Set ((ι → K) →+ (ι → K))) : Subgroup (GL ι K) where
  carrier := {g | ∀ s ∈ 𝒮, ∀ v, glEquiv g (s v) = s (glEquiv g v)}
  one_mem' := fun s _ v => by simp
  mul_mem' := fun {g h} hg hh s hs v => by
    rw [map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hh s hs, hg s hs]
  inv_mem' := fun {g} hg s hs v => by
    rw [map_inv]
    apply (glEquiv g).injective
    rw [← LinearEquiv.mul_apply, mul_inv_cancel, LinearEquiv.coe_one, id, hg s hs,
      ← LinearEquiv.mul_apply, mul_inv_cancel, LinearEquiv.coe_one, id]

theorem mem_centGL {𝒮 : Set ((ι → K) →+ (ι → K))} {g : GL ι K} :
    g ∈ centGL 𝒮 ↔ ∀ s ∈ 𝒮, ∀ v, glEquiv g (s v) = s (glEquiv g v) :=
  Iff.rfl

theorem isIsomRep_glRep {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K} {A : Subgroup (GL ι K)}
    [IsMulCommutative A] (hA : A ≤ isomGL β) : IsIsomRep β (glRep A) := fun a x y => by
  rw [glRep_apply, glRep_apply]
  exact mem_isomGL.mp (hA a.2) x y

theorem isMaxElem_of_maximal {p : ℕ} (β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K)
    (𝒮 : Set ((ι → K) →+ (ι → K))) (A : Subgroup (GL ι K)) [IsMulCommutative A]
    (hAel : IsElemAbelian p A) (hAβ : A ≤ isomGL β) (hA𝒮 : A ≤ centGL 𝒮)
    (hmax : ∀ A' : Subgroup (GL ι K), A ≤ A' → IsElemAbelian p A' → A' ≤ isomGL β →
      A' ≤ centGL 𝒮 → A' ≤ A) :
    IsMaxElem β (glRep A) p 𝒮 := by
  intro g hg hgA hg𝒮 hgp
  set g' : GL ι K := glEquiv.symm g with hg'
  have hgg' : glEquiv g' = g := by rw [hg', MulEquiv.apply_symm_apply]
  have hcomm : ∀ a ∈ A, a * g' = g' * a := by
    intro a ha
    apply glEquiv.injective
    refine LinearEquiv.ext fun v => ?_
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hgg']
    exact (hgA ⟨a, ha⟩ v).symm
  have hzel : IsElemAbelian p (Subgroup.zpowers g') := by
    refine CFSG.Open.IsElemAbelian.closure_of_commute (s := {g'}) (fun a ha b hb => ?_)
      (fun a ha => ?_) |> fun h => by rwa [Subgroup.zpowers_eq_closure]
    · rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb]
    · rw [Set.mem_singleton_iff.mp ha]
      apply glEquiv.injective
      refine LinearEquiv.ext fun v => ?_
      rw [map_pow, hgg', map_one, LinearEquiv.coe_one, id]
      exact hgp v
  have hA' : IsElemAbelian p (A ⊔ Subgroup.zpowers g') :=
    CFSG.Open.IsElemAbelian.sup_of_commute hAel hzel (fun a ha b hb => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact ((Commute.zpow_right (hcomm a ha) k)).eq)
  have hgβ : g' ∈ isomGL β := by
    rw [mem_isomGL]
    intro x y
    rw [← glEquiv_apply, ← glEquiv_apply, hgg']
    exact hg x y
  have hg𝒮' : g' ∈ centGL 𝒮 := fun s hs v => by rw [hgg']; exact hg𝒮 s hs v
  have hle := hmax _ le_sup_left hA'
    (sup_le hAβ ((Subgroup.zpowers_le).mpr hgβ)) (sup_le hA𝒮 ((Subgroup.zpowers_le).mpr hg𝒮'))
  have hmem : g' ∈ A := hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers g'))
  exact ⟨⟨g', hmem⟩, fun v => by rw [glRep_apply_eq_glEquiv, hgg']⟩

section Semilinear

variable {A : Type*} [CommGroup A] [Finite A] {p : ℕ} {V : Type*} [AddCommGroup V] [Module K V]

theorem preserves_weightFamily_of_semilinear (ρ : Representation K A V) (τ : K →+* K)
    (s : V →+ V) (hs : ∀ (c : K) (v : V), s (c • v) = τ c • s v)
    (hsρ : ∀ a v, s (ρ a v) = ρ a (s v)) (i : Option (Hyperplane A p)) {v : V}
    (hv : v ∈ weightFamily (p := p) ρ i) : s v ∈ weightFamily (p := p) ρ i := by
  have hU : ∀ (U : Subgroup A) (w : V),
      s (ρ.asAlgebraHom (eSub U) w) = ρ.asAlgebraHom (eSub U) (s w) := by
    intro U w
    haveI : Fintype U := Fintype.ofFinite U
    rw [asAlgebraHom_eSub, LinearMap.smul_apply, LinearMap.smul_apply, hs, map_inv₀, map_natCast,
      LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    simp only [hsρ]
  obtain ⟨w, rfl⟩ := hv
  refine ⟨s w, ?_⟩
  rcases i with _ | H
  · exact (hU ⊤ w).symm
  · show ρ.asAlgebraHom (eSub H.1 - eSub ⊤) (s w) = s (ρ.asAlgebraHom (eSub H.1 - eSub ⊤) w)
    rw [map_sub, LinearMap.sub_apply, LinearMap.sub_apply, map_sub, hU, hU]

end Semilinear

theorem isomGL_zero : isomGL (0 : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K) = ⊤ := by
  ext g
  simp [mem_isomGL]

theorem transpose_mul_mul_of_mem_gramCore {J : Matrix ι ι K} {g : GL ι K}
    (hg : g ∈ CFSG.MatrixModel.gramCore J) :
    (g : Matrix ι ι K)ᵀ * J * (g : Matrix ι ι K) = J := by
  rw [CFSG.MatrixModel.gramCore] at hg
  induction hg using Subgroup.closure_induction with
  | mem A hA => exact hA
  | one => simp
  | mul A B _ _ hA hB =>
    calc ((A * B : GL ι K) : Matrix ι ι K)ᵀ * J * ((A * B : GL ι K) : Matrix ι ι K)
        = (B : Matrix ι ι K)ᵀ * ((A : Matrix ι ι K)ᵀ * J * (A : Matrix ι ι K)) *
            (B : Matrix ι ι K) := by
          rw [Units.val_mul, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [hA, hB]
  | inv A _ hA =>
    have h1 : (A : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((A⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * J * ((A⁻¹ : GL ι K) : Matrix ι ι K)
        = ((A⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * ((A : Matrix ι ι K)ᵀ * J * (A : Matrix ι ι K)) *
            ((A⁻¹ : GL ι K) : Matrix ι ι K) := by rw [hA]
      _ = ((A : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K))ᵀ * J *
            ((A : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K)) := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [h1, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem gramCore_le_isomGL (J : Matrix ι ι K) :
    CFSG.MatrixModel.gramCore J ≤ isomGL (Matrix.toBilin' J) := by
  intro g hg
  rw [mem_isomGL]
  intro x y
  have h := congrArg (fun B : LinearMap.BilinForm K (ι → K) => B x y)
    (Matrix.toBilin'_comp J (g : Matrix ι ι K) (g : Matrix ι ι K))
  simp only [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply,
    transpose_mul_mul_of_mem_gramCore hg] at h
  exact h

@[expose] noncomputable def unitForm (σ : K →+* K) : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K :=
  LinearMap.mk₂'ₛₗ (RingHom.id K) σ (fun x y => ∑ i, x i * σ (y i))
    (fun x x' y => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum,
      mul_assoc])
    (fun x y y' => by simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib])
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum,
      mul_left_comm])

theorem unitForm_apply (σ : K →+* K) (x y : ι → K) :
    unitForm σ x y = x ⬝ᵥ (σ ∘ y) :=
  rfl

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
