module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaInputs

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification
open scoped MatrixGroups

theorem eq_of_inv_mul_mem_center {H M : Type*} [Group H] [Group M] [Group.IsPerfect H]
    (f g : H →* M) (hfg : ∀ x, (f x)⁻¹ * g x ∈ center M) : f = g := by
  let d : H →* center M :=
    { toFun := fun x => ⟨(f x)⁻¹ * g x, hfg x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        have hc := mem_center_iff.mp (hfg x) ((f y)⁻¹)
        change (f (x * y))⁻¹ * g (x * y) = (f x)⁻¹ * g x * ((f y)⁻¹ * g y)
        calc (f (x * y))⁻¹ * g (x * y) = (f y)⁻¹ * ((f x)⁻¹ * g x) * g y := by
              rw [map_mul, map_mul]
              group
          _ = (f x)⁻¹ * g x * ((f y)⁻¹ * g y) := by
              rw [hc]
              group }
  ext x
  have hx : x ∈ d.ker := Abelianization.commutator_subset_ker d
    (by rw [Group.IsPerfect.commutator_eq_top]; trivial)
  have h1 : (f x)⁻¹ * g x = 1 := congrArg Subtype.val hx
  exact (inv_mul_eq_one.mp h1)

section Standard

variable {n : ℕ} {F : Type*} [Field F]

theorem center_projectiveSL_eq_bot [Finite F] (hn : 3 ≤ n) : center (projectiveSL n F) = ⊥ := by
  refine eq_bot_iff.2 fun z hz => ?_
  obtain ⟨g, rfl⟩ := proj_surjective n F z
  have hconj : conjAut n F (SpecialLinearGroup.toGL g) = 1 := by
    rw [conjAut_toGL]
    ext x
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← mem_center_iff.1 hz x, mul_inv_cancel_right]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (K := F) hn
    (SpecialLinearGroup.toGL g) 1 (by rw [map_one, mul_one]; exact hconj)
  have hmat := congrArg (fun A : GL (Fin n) F => (A : Matrix (Fin n) (Fin n) F)) hc
  simp only [GeneralLinearGroup.coe_scalar] at hmat
  have hdet : c ^ n = 1 := by
    apply Units.ext
    have h1 := congrArg Matrix.det hmat
    rw [Matrix.scalar_apply, Matrix.det_diagonal] at h1
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
    rw [Units.val_pow_eq_pow_val, h1]
    exact g.2
  exact mem_bot.2 (proj_eq_one_iff.2 ⟨c, hdet, hmat.symm⟩)

variable (n F) in
@[expose] noncomputable def stdSL (A : GL (Fin n) F) (σ : F ≃+* F) (ε : ℕ) : MulAut SL(n, F) :=
  CatalogueBHigherLinearAction.slConjugation n F A *
    CatalogueBHigherLinearField.slFieldAut (Fin n) F σ * CatalogueBGraphForm.slGraphAut n F ^ ε

theorem descendAut_stdSL (A : GL (Fin n) F) (σ : F ≃+* F) (ε : ℕ) :
    descendAut n F (stdSL n F A σ ε) = conjAut n F A * fieldAut n F σ * dualAut n F ^ ε := by
  rw [stdSL, map_mul, map_mul, map_pow]
  rfl

theorem eq_of_descendAut_eq (hn : 3 ≤ n) {β β' : MulAut SL(n, F)}
    (h : descendAut n F β = descendAut n F β') : β = β' := by
  have := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := F) hn
  have hfg := eq_of_inv_mul_mem_center β.toMonoidHom β'.toMonoidHom fun x => by
    have h1 := congrArg (fun γ : MulAut (projectiveSL n F) => γ (proj n F x)) h
    simp only [descendAut_proj] at h1
    rw [← scalars_eq_center]
    exact proj_eq_proj_iff.mp h1
  exact MulEquiv.ext fun x => DFunLike.congr_fun hfg x

end Standard

section Lift

variable {n : ℕ} {F : Type*} [Field F] [Finite F] {G : Type*} [Group G] {K : Subgroup G}

theorem exists_stdSL_lift (hn : 3 ≤ n) (ψ : SL(n, F) →* K) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ center SL(n, F)) {t : G} (ht : t ∈ normalizer (K : Set G)) :
    ∃ (A : GL (Fin n) F) (σ : F ≃+* F) (ε : ℕ), ε ≤ 1 ∧
      ∀ x, t * (ψ x : G) * t⁻¹ = ψ (stdSL n F A σ ε x) := by
  classical
  have := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := F) hn
  set N : Subgroup K := (scalars n F).map ψ with hN
  have hNc : N ≤ center K := by
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_center_iff]
    intro k
    obtain ⟨y, rfl⟩ := hψ k
    rw [← map_mul, ← map_mul, mem_center_iff.mp ((scalars_eq_center n F) ▸ hz) y]
  have : N.Normal := normal_of_le_center hNc
  let e : projectiveSL n F →* K ⧸ N := QuotientGroup.map (scalars n F) N ψ (le_comap_map _ _)
  have he : ∀ y, e (proj n F y) = (ψ y : K ⧸ N) := fun y => rfl
  have he_inj : Function.Injective e := by
    rw [injective_iff_map_eq_one]
    intro z hz
    obtain ⟨y, rfl⟩ := proj_surjective n F z
    rw [he, QuotientGroup.eq_one_iff] at hz
    obtain ⟨w, hw, hwy⟩ := hz
    rw [proj_eq_one_iff]
    have h1 : w⁻¹ * y ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hwy, inv_mul_cancel]
    have h2 : w⁻¹ * y ∈ scalars n F := (scalars_eq_center n F).symm ▸ hker h1
    simpa using mul_mem hw h2
  have he_surj : Function.Surjective e := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨y, rfl⟩ := hψ k
    exact ⟨proj n F y, rfl⟩
  let eE : projectiveSL n F ≃* K ⧸ N := MulEquiv.ofBijective e ⟨he_inj, he_surj⟩
  have hcN : center K ≤ N := by
    intro k hk
    obtain ⟨y, rfl⟩ := hψ k
    have hcen : proj n F y ∈ center (projectiveSL n F) := by
      rw [mem_center_iff]
      intro z
      apply he_inj
      obtain ⟨w, rfl⟩ := proj_surjective n F z
      rw [map_mul, map_mul, he, he, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        mem_center_iff.mp hk]
    rw [center_projectiveSL_eq_bot hn, mem_bot, proj_eq_one_iff] at hcen
    exact ⟨y, hcen, rfl⟩
  set α := K.normalizerMonoidHom ⟨t, ht⟩
  have hαN : N.map (α : K →* K) = N := by
    rw [le_antisymm hNc hcN]
    exact map_center_eq α
  let αK : MulAut (K ⧸ N) := QuotientGroup.congr N N α hαN
  obtain ⟨A, σ, ε, hε, hᾱ⟩ := (automorphism_generation (K := F) hn).2 (MulAut.congr eE.symm αK)
  refine ⟨A, σ, ε, hε, fun x => ?_⟩
  have hkey : ∀ x, ((α.toMonoidHom.comp ψ) x)⁻¹ *
      (ψ.comp (stdSL n F A σ ε).toMonoidHom) x ∈ center K := by
    intro x
    apply hNc
    have h1 : eE (proj n F (stdSL n F A σ ε x)) = αK (eE (proj n F x)) := by
      rw [← descendAut_proj, descendAut_stdSL, ← hᾱ]
      change eE (eE.symm (αK (eE (proj n F x)))) = _
      rw [MulEquiv.apply_symm_apply]
    change (ψ (stdSL n F A σ ε x) : K ⧸ N) = QuotientGroup.congr N N α hαN (ψ x : K ⧸ N) at h1
    rw [QuotientGroup.congr_mk] at h1
    exact QuotientGroup.eq.mp h1.symm
  have h2 := DFunLike.congr_fun (eq_of_inv_mul_mem_center _ _ hkey) x
  change α (ψ x) = ψ (stdSL n F A σ ε x) at h2
  rw [← h2]
  rfl

end Lift

end CFSG.EvenSmallLie.UnitarySix.YamadaInputs
