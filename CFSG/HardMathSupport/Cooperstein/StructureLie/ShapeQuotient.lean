module

public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Quotient.Basic

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

section Abstract

variable {A : Type*} [AddCommGroup A] [Module (ZMod 2) A] {M : Type*} [Group M]

theorem exists_rep_quotient (N : Submodule (ZMod 2) A)
    (φ : M →* LinearMap.GeneralLinearGroup (ZMod 2) A)
    (hN : ∀ m : M, ∀ x ∈ N, (φ m : A →ₗ[ZMod 2] A) x ∈ N) :
    ∃ ρ : M →* LinearMap.GeneralLinearGroup (ZMod 2) (A ⧸ N),
      ∀ (m : M) (x : A), (ρ m : (A ⧸ N) →ₗ[ZMod 2] (A ⧸ N)) (Submodule.Quotient.mk x) =
        Submodule.Quotient.mk ((φ m : A →ₗ[ZMod 2] A) x) := by
  let e : M →* (A ≃ₗ[ZMod 2] A) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) A).toMonoidHom.comp φ
  have he : ∀ m x, e m x = (φ m : A →ₗ[ZMod 2] A) x := fun m x => rfl
  have hmap : ∀ m : M, N.map (e m : A →ₗ[ZMod 2] A) = N := by
    intro m
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [LinearEquiv.coe_coe, he]
      exact hN m x hx
    · intro y hy
      refine ⟨e m⁻¹ y, ?_, ?_⟩
      · rw [he]; exact hN m⁻¹ y hy
      · show e m (e m⁻¹ y) = y
        rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
  let T : M → ((A ⧸ N) ≃ₗ[ZMod 2] (A ⧸ N)) := fun m =>
    Submodule.Quotient.equiv N N (e m) (hmap m)
  have hT : ∀ m x, T m (Submodule.Quotient.mk x) = Submodule.Quotient.mk (e m x) :=
    fun m x => rfl
  refine ⟨{ toFun := fun m => LinearMap.GeneralLinearGroup.ofLinearEquiv (T m)
            map_one' := ?_
            map_mul' := ?_ }, fun m x => ?_⟩
  · refine Units.ext (LinearMap.ext fun x => ?_)
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      show T 1 (Submodule.Quotient.mk x) = _
      rw [hT, map_one]
      rfl
  · intro m n
    refine Units.ext (LinearMap.ext fun x => ?_)
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      show T (m * n) (Submodule.Quotient.mk x) =
        T m (T n (Submodule.Quotient.mk x))
      rw [hT, hT, hT, map_mul]
      rfl
  · exact congrArg Submodule.Quotient.mk (he m x)

def zmod2LinearEquiv {A : Type*} [AddCommGroup A] [Module (ZMod 2) A] (e : A ≃+ A) :
    A ≃ₗ[ZMod 2] A :=
  { e with map_smul' := fun c x => ZMod.map_smul e c x }

end Abstract

section Groups

variable {G : Type} [Group G]

@[expose, instance_reducible] def commGroupOfComm (U : Subgroup G)
    (hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) : CommGroup ↥U :=
  { (inferInstance : Group ↥U) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }

theorem exists_quotientModule [Finite G] (M U Cl : Subgroup G)
    (hUM : M ≤ Subgroup.normalizer (U : Set G)) (hClM : M ≤ Subgroup.normalizer (Cl : Set G))
    (hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) (hsq : ∀ u ∈ U, u * u = 1) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : Finite W)
      (cls : ↥U → W) (ρ : ↥M →* LinearMap.GeneralLinearGroup (ZMod 2) W),
      (∀ a b, cls (a * b) = cls a + cls b) ∧ Function.Surjective cls ∧
      (∀ u, cls u = 0 ↔ (u : G) ∈ Cl) ∧
      ∀ (m : ↥M) (u v : ↥U), (v : G) = m * u * m⁻¹ →
        (ρ m : W →ₗ[ZMod 2] W) (cls u) = cls v := by
  let _ : CommGroup ↥U := commGroupOfComm U hcomm
  have : Module (ZMod 2) (Additive ↥U) := AddCommGroup.zmodModule (fun x => by
    obtain ⟨u, rfl⟩ := Additive.ofMul.surjective x
    rw [two_nsmul]
    show Additive.ofMul (u * u) = Additive.ofMul 1
    congr 1
    exact Subtype.ext (hsq u u.2))
  let c : ↥M →* MulAut ↥U := U.normalizerMonoidHom.comp (Subgroup.inclusion hUM)
  have hc : ∀ (m : ↥M) (u : ↥U), ((c m u : ↥U) : G) = m * u * (m : G)⁻¹ := fun m u =>
    Subgroup.normalizerMonoidHom_apply_apply_coe U (Subgroup.inclusion hUM m) u
  let φ : ↥M →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive ↥U) :=
    { toFun := fun m => LinearMap.GeneralLinearGroup.ofLinearEquiv
        (zmod2LinearEquiv (MulEquiv.toAdditive (c m)))
      map_one' := Units.ext (LinearMap.ext fun x => by
        obtain ⟨u, rfl⟩ := Additive.ofMul.surjective x
        change Additive.ofMul (c 1 u) = Additive.ofMul u
        rw [map_one]
        rfl)
      map_mul' := fun m n => Units.ext (LinearMap.ext fun x => by
        obtain ⟨u, rfl⟩ := Additive.ofMul.surjective x
        change Additive.ofMul (c (m * n) u) = Additive.ofMul (c m (c n u))
        rw [map_mul]
        rfl) }
  have hφ : ∀ (m : ↥M) (u : ↥U), (φ m : Additive ↥U →ₗ[ZMod 2] Additive ↥U) (Additive.ofMul u) =
      Additive.ofMul (c m u) := fun m u => rfl
  let N : Submodule (ZMod 2) (Additive ↥U) :=
    AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup (Cl.subgroupOf U))
  have hN : ∀ u : ↥U, Additive.ofMul u ∈ N ↔ (u : G) ∈ Cl := fun u => Iff.rfl
  obtain ⟨ρ, hρ⟩ := exists_rep_quotient N φ (by
    intro m x hx
    obtain ⟨u, rfl⟩ := Additive.ofMul.surjective x
    rw [hφ, hN]
    rw [hN] at hx
    rw [hc]
    exact (Subgroup.mem_normalizer_iff.mp (hClM m.2) u).mp hx)
  have : Finite (Additive ↥U) := (inferInstance : Finite ↥U)
  have : Finite (Additive ↥U ⧸ N) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective N)
  refine ⟨Additive ↥U ⧸ N, inferInstance, inferInstance, inferInstance,
    fun u => Submodule.Quotient.mk (Additive.ofMul u), ρ, ?_, ?_, ?_, ?_⟩
  · intro a b
    rw [← Submodule.Quotient.mk_add]
    rfl
  · intro y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N y
    obtain ⟨u, rfl⟩ := Additive.ofMul.surjective x
    exact ⟨u, rfl⟩
  · intro u
    rw [Submodule.Quotient.mk_eq_zero, hN]
  · intro m u v hv
    rw [hρ, hφ]
    congr 2
    exact Subtype.ext (by rw [hc, hv]; rfl)

end Groups

end CFSG.HardMathSupport.Cooperstein.StructureLie
