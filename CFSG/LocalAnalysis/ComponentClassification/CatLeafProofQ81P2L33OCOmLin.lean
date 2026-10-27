module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33OCOmTools
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33OCSpLin
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquareOrthogonal

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.OC

open CFSG Subgroup Matrix Module QuadraticMap CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare QuaternionMatrices
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
  CatalogueBOrthogonalScalarSquareField CatalogueBOrthogonalScalarSquareForms

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {A : V ≃ₗ[K] V}

theorem omWit_of_centralizer {G : Type} [Group G] {S : Set G} (hS : closure S = ⊤)
    (hSo : ∀ s ∈ S, Odd (orderOf s)) (Φ : G →* orthogonalOperatorCentralizer Q A.toLinearMap)
    {x : G} (hx4 : x ^ 4 = 1) (hxs : NotScalar (Φ x).val.val) :
    OmWit Q (Subgroup.centralizer {A}) := by
  refine ⟨G, inferInstance, S, (TauCeti.QuadraticMap.orthogonalGroup Q).subtype.comp
    ((orthogonalOperatorCentralizer Q A.toLinearMap).subtype.comp Φ), hS, hSo, fun g => ?_,
    fun g => ?_, x, hx4, hxs⟩
  · exact (Φ g).val.prop
  · refine Subgroup.mem_centralizer_singleton_iff.2 (LinearEquiv.ext fun v => ?_)
    have hc : ∀ y, (Φ g).val.val (A.toLinearMap y) = A.toLinearMap ((Φ g).val.val y) :=
      (Φ g).prop
    exact hc v

theorem polarBilin_comp_subtype (W : Submodule K V) :
    (Q.comp W.subtype).polarBilin = LinearMap.BilinForm.restrict Q.polarBilin W :=
  LinearMap.ext₂ fun _ _ => rfl

theorem notScalar_of_fix {f : V ≃ₗ[K] V} {W : Submodule K V} (hW : W ≠ ⊥)
    (hfix : ∀ y ∈ W, f y = y) {x : V} (hx : f x ≠ x) : NotScalar f := fun a h => by
  obtain ⟨y, hyW, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have h1 : f y = a • y := LinearMap.congr_fun h y
  rw [hfix y hyW] at h1
  have ha : a = 1 := by
    have h2 : (1 - a) • y = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    exact (sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hy0)).symm
  subst ha
  exact hx (by simpa using LinearMap.congr_fun h x)

theorem exists_ne_of_notScalar {W : Type*} [AddCommGroup W] [Module K W] {g : W ≃ₗ[K] W}
    (hg : NotScalar g) : ∃ x, g x ≠ x := by
  by_contra h
  push Not at h
  exact hg 1 (LinearMap.ext fun x => by simpa using h x)

theorem omWit_split [Finite K] (hK : ringChar K ≠ 2) [FiniteDimensional K V]
    {Vp Vm : Submodule K V} (hc : IsCompl Vp Vm) (hVp : Vp ≠ ⊥) (hVm : Vm ≠ ⊥)
    (h7 : 7 ≤ finrank K V)
    (hNp : (LinearMap.BilinForm.restrict Q.polarBilin Vp).Nondegenerate)
    (hNm : (LinearMap.BilinForm.restrict Q.polarBilin Vm).Nondegenerate)
    (e : orthogonalOperatorCentralizer Q A.toLinearMap ≃*
      (TauCeti.QuadraticMap.orthogonalGroup (Q.comp Vp.subtype) ×
        TauCeti.QuadraticMap.orthogonalGroup (Q.comp Vm.subtype)))
    (he : ∀ g (x : Vp) (y : Vm), (e.symm g).val.val (x.val + y.val) =
      (g.1.val x).val + (g.2.val y).val) :
    OmWit Q (Subgroup.centralizer {A}) := by
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  obtain ⟨hS, hSo⟩ := elementary_closure_odd hK 2
  by_cases h3 : 3 ≤ finrank K Vp
  · obtain ⟨ψ, hψ, hψs⟩ := exists_sl2_orth hK (Q.comp Vp.subtype)
      (by rw [polarBilin_comp_subtype]; exact hNp) h3
    let Φ := e.symm.toMonoidHom.comp (MonoidHom.prod (ψ.codRestrict _ hψ) 1)
    obtain ⟨x, hx⟩ := exists_ne_of_notScalar hψs
    refine omWit_of_centralizer hS hSo Φ slQuatI_pow_four
      (notScalar_of_fix hVm (fun y hy => ?_) (x := (x : V)) fun h => hx (Subtype.ext ?_))
    · have h1 := he (MonoidHom.prod (ψ.codRestrict _ hψ) 1 (slQuatI K)) 0 ⟨y, hy⟩
      rw [ZeroMemClass.coe_zero, zero_add, map_zero, ZeroMemClass.coe_zero, zero_add] at h1
      exact h1
    · have h1 := he (MonoidHom.prod (ψ.codRestrict _ hψ) 1 (slQuatI K)) x 0
      rw [ZeroMemClass.coe_zero, add_zero, map_zero, ZeroMemClass.coe_zero, add_zero] at h1
      exact h1.symm.trans h
  · have h3m : 3 ≤ finrank K Vm := by omega
    obtain ⟨ψ, hψ, hψs⟩ := exists_sl2_orth hK (Q.comp Vm.subtype)
      (by rw [polarBilin_comp_subtype]; exact hNm) h3m
    let Φ := e.symm.toMonoidHom.comp (MonoidHom.prod 1 (ψ.codRestrict _ hψ))
    obtain ⟨y, hy⟩ := exists_ne_of_notScalar hψs
    refine omWit_of_centralizer hS hSo Φ slQuatI_pow_four
      (notScalar_of_fix hVp (fun x hx => ?_) (x := (y : V)) fun h => hy (Subtype.ext ?_))
    · have h1 := he (MonoidHom.prod 1 (ψ.codRestrict _ hψ) (slQuatI K)) ⟨x, hx⟩ 0
      rw [ZeroMemClass.coe_zero, add_zero, map_zero, ZeroMemClass.coe_zero, add_zero] at h1
      exact h1
    · have h1 := he (MonoidHom.prod 1 (ψ.codRestrict _ hψ) (slQuatI K)) 0 y
      rw [ZeroMemClass.coe_zero, zero_add, map_zero, ZeroMemClass.coe_zero, zero_add] at h1
      exact h1.symm.trans h

theorem omWit_paired [Finite K] (hK : ringChar K ≠ 2) [FiniteDimensional K V]
    {Vp : Submodule K V} (h3 : 3 ≤ finrank K Vp)
    (e : orthogonalOperatorCentralizer Q A.toLinearMap ≃* (Vp ≃ₗ[K] Vp))
    (he : ∀ g (x : Vp), (e.symm g).val.val x.val = (g x).val) :
    OmWit Q (Subgroup.centralizer {A}) := by
  obtain ⟨m, hm⟩ : ∃ m, finrank K Vp = 2 + m := ⟨_, (Nat.add_sub_cancel' (by omega)).symm⟩
  let c := Module.finBasisOfFinrankEq K Vp hm
  let ρ : SpecialLinearGroup (Fin 2) K →* (Vp ≃ₗ[K] Vp) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K Vp).toMonoidHom.comp
      ((CLSFourGroupScalarSquare.basisGL c).comp
        ((LinearFlag.blockGL K 2 m).comp SpecialLinearGroup.toGL))
  have hρs : ∀ a : K, ∃ x : Vp, ρ (slQuatI K) x ≠ a • x := by
    intro a
    by_contra h
    push Not at h
    have h1 : Matrix.toLin c c ((LinearFlag.blockGL K 2 m (SpecialLinearGroup.toGL (slQuatI K)) :
        GL (Fin (2 + m)) K) : Matrix (Fin (2 + m)) (Fin (2 + m)) K) =
          a • (1 : Module.End K Vp) := LinearMap.ext fun x => h x
    exact LinearFlag.blockGL_ne_scalar_of_ne_one (k := 2) (m := m) (by omega)
      (LinearFlag.toGL_slQuatI_ne_one (K := K)) a
      (by
        rw [scalar_apply, ← smul_one_eq_diagonal]
        exact FourGroupOddUnitary.toLin_eq_smul_id c h1)
  obtain ⟨hS, hSo⟩ := elementary_closure_odd hK 2
  refine omWit_of_centralizer hS hSo (e.symm.toMonoidHom.comp ρ) slQuatI_pow_four
    fun a h => ?_
  obtain ⟨x, hx⟩ := hρs a
  refine hx (Subtype.ext ?_)
  rw [Submodule.coe_smul, ← he]
  exact LinearMap.congr_fun h (x : V)

theorem ringChar_ne_two_of_algebra (hK : ringChar K ≠ 2) {E : Type*} [Field E] [Algebra K E] :
    ringChar E ≠ 2 := fun h => by
  apply two_ne_zero_of_algebra hK (E := E)
  have := ringChar.Nat.cast_ringChar (R := E)
  rw [h] at this
  exact_mod_cast this

theorem omWit_field_orth [Finite K] (hK : ringChar K ≠ 2) [FiniteDimensional K V] {E : Type}
    [Field E] [Finite E] [Algebra K E] [Module E V] [IsScalarTower K E V] [FiniteDimensional E V]
    (hE3 : 3 ≤ finrank E V) {QE : QuadraticForm E V} (hQE : QE.polarBilin.Nondegenerate)
    (e : orthogonalOperatorCentralizer Q A.toLinearMap ≃* TauCeti.QuadraticMap.orthogonalGroup QE)
    (he : ∀ g x, (e.symm g).val.val x = g.val x) :
    OmWit Q (Subgroup.centralizer {A}) := by
  have hE2 := ringChar_ne_two_of_algebra hK (E := E)
  obtain ⟨ψ, hψ, hψs⟩ := exists_sl2_orth hE2 QE hQE hE3
  obtain ⟨hS, hSo⟩ := elementary_closure_odd hE2 2
  refine omWit_of_centralizer hS hSo (e.symm.toMonoidHom.comp (ψ.codRestrict _ hψ))
    slQuatI_pow_four fun a h => hψs (algebraMap K E a) (LinearMap.ext fun x => ?_)
  have h1 := LinearMap.congr_fun h x
  simp only [LinearEquiv.coe_coe, LinearMap.smul_apply, LinearMap.id_apply] at h1
  change (e.symm _).val.val x = a • x at h1
  rw [he] at h1
  simp only [LinearEquiv.coe_coe, LinearMap.smul_apply, LinearMap.id_apply, algebraMap_smul]
  exact h1

theorem omWit_field_unitary [Finite K] (hK : ringChar K ≠ 2) [FiniteDimensional K V] {E : Type}
    [Field E] [Algebra K E] [Module E V] [IsScalarTower K E V] [FiniteDimensional E V]
    (hE3 : 3 ≤ finrank E V) {ℓ f : ℕ} (hUF : UnitaryFieldData ℓ f E) {sigma : E ≃+* E}
    {h : V →ₛₗ[sigma.toRingHom] V →ₗ[E] E} (hs : h.IsSymm) (hn : h.Nondegenerate)
    (hfix : ∀ a : K, sigma (algebraMap K E a) = algebraMap K E a)
    (e : orthogonalOperatorCentralizer Q A.toLinearMap ≃*
      CatalogueBUnitaryIsometry.isometryGroup h)
    (he : ∀ g x, (e.symm g).val.val x = g.val x) (hsig : ∀ z, sigma z = z ^ (ℓ ^ f)) :
    OmWit Q (Subgroup.centralizer {A}) := by
  classical
  obtain ⟨ob, hob⟩ := exists_orthonormal_of_eq_pow hUF (τ := sigma.toRingHom) hsig h hs hn.1
  obtain ⟨m, hm⟩ : ∃ m, finrank E V = 3 + m := ⟨_, (Nat.add_sub_cancel' hE3).symm⟩
  let ob' := ob.reindex (finCongr hm)
  have hG : ∀ i j, h (ob' i) (ob' j) = (1 : Matrix (Fin (3 + m)) (Fin (3 + m)) E) i j :=
    fun i j => by
      rw [Basis.reindex_apply, Basis.reindex_apply, hob, Matrix.one_apply]
      simp
  obtain ⟨ζ, hζ, hζs⟩ := LinearFlag.exists_ternary_isometry_hom hK (fun _ => (1 : K))
    fun _ => one_ne_zero
  set φ := algebraMap K E with hφ
  let N : SpecialLinearGroup (Fin 2) K → Matrix (Fin (3 + m)) (Fin (3 + m)) K :=
    fun X => ((LinearFlag.blockGL K 3 m (ζ X) : GL (Fin (3 + m)) K) :
      Matrix (Fin (3 + m)) (Fin (3 + m)) K)
  have hblock : ∀ X, (N X)ᵀ * N X = 1 := by
    intro X
    have h1 := hζ X
    rw [diagonal_one, Matrix.mul_one] at h1
    change ((LinearFlag.blockGL K 3 m (ζ X) : GL (Fin (3 + m)) K) :
      Matrix (Fin (3 + m)) (Fin (3 + m)) K)ᵀ *
        ((LinearFlag.blockGL K 3 m (ζ X) : GL (Fin (3 + m)) K) :
          Matrix (Fin (3 + m)) (Fin (3 + m)) K) = 1
    rw [LinearFlag.coe_blockGL_eq_diagBlock, LinearFlag.diagBlock_transpose,
      LinearFlag.diagBlock_mul, h1, transpose_one, Matrix.one_mul]
    simp [LinearFlag.diagBlock, fromBlocks_one]
  let ψ : SpecialLinearGroup (Fin 2) K →* (V ≃ₗ[E] V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv E V).toMonoidHom.comp
      ((CLSFourGroupScalarSquare.basisGL ob').comp
        ((GeneralLinearGroup.map φ).comp ((LinearFlag.blockGL K 3 m).comp ζ)))
  have hψ : ∀ X v, ψ X v = Matrix.toLin ob' ob' ((N X).map φ) v := fun X v => rfl
  have hmem : ∀ X, ψ X ∈ CatalogueBUnitaryIsometry.isometryGroup h := fun X =>
    (CatalogueBUnitaryIsometry.mem_isometryGroup_iff h _).2 fun x y => by
      rw [hψ, hψ]
      refine toLin_preserves h ob' 1 hG (fun i j => hfix _) ?_ x y
      show ((N X).map φ)ᵀ * 1 * (N X).map φ = 1
      rw [Matrix.mul_one, ← transpose_map, ← Matrix.map_mul, hblock X,
        Matrix.map_one _ (map_zero φ) (map_one φ)]
  obtain ⟨hS, hSo⟩ := elementary_closure_odd hK 2
  refine omWit_of_centralizer hS hSo (e.symm.toMonoidHom.comp (ψ.codRestrict _ hmem))
    slQuatI_pow_four fun a ha => ?_
  have h1 : Matrix.toLin ob' ob' ((N (slQuatI K)).map φ) = φ a • (1 : Module.End E V) := by
    refine LinearMap.ext fun x => ?_
    have h2 := LinearMap.congr_fun ha x
    simp only [LinearEquiv.coe_coe, LinearMap.smul_apply, LinearMap.id_apply] at h2
    change (e.symm _).val.val x = a • x at h2
    rw [he] at h2
    rw [← hψ, LinearMap.smul_apply, Module.End.one_apply, algebraMap_smul]
    exact h2
  refine map_ne_smul_one φ (N := N (slQuatI K)) (fun c hc => ?_) (φ a)
    (FourGroupOddUnitary.toLin_eq_smul_id ob' h1)
  exact LinearFlag.blockGL_ne_scalar_of_ne_scalar hζs c
    (by rw [scalar_apply, ← smul_one_eq_diagonal]; exact hc)

end CFSG.ComponentClassification.HarrisLit.L33.OC
