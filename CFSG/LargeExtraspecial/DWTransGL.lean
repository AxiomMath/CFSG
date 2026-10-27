module

public import CFSG.LargeExtraspecial.DWTransFaith
public import CFSG.LargeExtraspecial.DWTransQ

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.GroupTheory.GLnTwoSplitting
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {A : Subgroup G}

theorem nonempty_linearEquiv_mulEquiv_GL {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] {m : ℕ} (hm : finrank (ZMod 2) E = m) :
    Nonempty ((E ≃ₗ[ZMod 2] E) ≃* GL (Fin m) (ZMod 2)) := by
  let b := (Module.finBasisOfFinrankEq (ZMod 2) E hm).equivFun
  let e₁ : (E ≃ₗ[ZMod 2] E) ≃* ((Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin m → ZMod 2)) :=
    { toFun := fun f => b.symm.trans (f.trans b)
      invFun := fun g => b.trans (g.trans b.symm)
      left_inv := fun f => by ext x; simp
      right_inv := fun g => by ext x; simp
      map_mul' := fun f g => by ext x; simp }
  exact ⟨e₁.trans (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)).symm⟩

theorem map_clSub_eq (hM : S.M ≤ normalizer (A : Set G)) {x : S.O} (hx : x ∈ S.Mbar) :
    (S.clSub A).map ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = S.clSub A := by
  refine le_antisymm ?_ fun v hv => ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact MaxEA.apply_mem_clSub hM hx hv
  · refine ⟨((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v,
      MaxEA.apply_mem_clSub hM (S.Mbar.inv_mem hx) hv, ?_⟩
    exact LinearEquiv.apply_symm_apply _ v

variable (S A) in
@[expose] noncomputable def resAt (hM : S.M ≤ normalizer (A : Set G)) :
    S.Mbar →* (S.clSub A ≃ₗ[ZMod 2] S.clSub A) where
  toFun x := LinearEquiv.ofSubmodules ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.clSub A)
    (S.clSub A) (map_clSub_eq hM x.2)
  map_one' := LinearEquiv.ext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => rfl

theorem coe_resAt_apply (hM : S.M ≤ normalizer (A : Set G)) (x : S.Mbar) (v : S.clSub A) :
    ((resAt S A hM x v : S.clSub A) : S.Qt) = ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v :=
  rfl

namespace MaxEA

variable [IsElementaryAbelian 2 A] (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G))
include hA hM

theorem resAt_injective : Function.Injective (resAt S A hM) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [mem_bot]
  refine Subtype.ext (hA.eq_one_of_forall_clSub hM x.2 fun v hv => ?_)
  have := congrArg (fun e : S.clSub A ≃ₗ[ZMod 2] S.clSub A => ((e ⟨v, hv⟩ : S.clSub A) : S.Qt)) hx
  exact this

theorem resAt_surjective (hsurj : Function.Surjective (conjLinear (AN A))) :
    Function.Surjective (resAt S A hM) := by
  have : Finite (Additive S.Q) := inferInstanceAs (Finite S.Q)
  have : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_transvections_eq_top, closure_le]
  rintro τ ⟨φ, c, hφc, rfl⟩
  obtain ⟨a, haA, haQ, hac⟩ := S.mem_clSub_iff.mp c.2
  let p : Additive (AN A) →ₗ[ZMod 2] S.clSub A := LinearMap.codRestrict _ hA.clMap
    fun x => S.cl_mem_clSub (elt_mem x) (hA.le_QG (elt_mem x))
  have hp : ∀ x, (p x : S.Qt) = hA.clMap x := fun _ => rfl
  set f : Dual (ZMod 2) (Additive (AN A)) := φ ∘ₗ p
  have hpa : p (vec haA) = c := Subtype.ext (by rw [hp, clMap_apply, elt_vec, hac])
  have hfd : f (vec haA) = 0 := by
    change φ (p (vec haA)) = 0
    rw [hpa, hφc]
  have hfz : f hA.zVec = 0 := by
    change φ (p hA.zVec) = 0
    have : p hA.zVec = 0 := Subtype.ext (by rw [hp, hA.clMap_zVec]; rfl)
    rw [this, map_zero]
  obtain ⟨n, hn⟩ := hsurj (LinearEquiv.transvection hfd)
  have hnz : (n : G) * S.z * (n : G)⁻¹ = S.z := by
    have h1 := congrArg elt (LinearEquiv.congr_fun hn hA.zVec)
    rw [elt_conjLinear, transvection_apply, hfz, zero_smul, add_zero] at h1
    exact h1
  have hnM : (n : G) ∈ S.M := mem_centralizer_singleton_iff.mpr (by
    calc (n : G) * S.z = (n : G) * S.z * (n : G)⁻¹ * n := by group
      _ = S.z * n := by rw [hnz])
  refine ⟨⟨S.ρ ⟨n, hnM⟩, ⟨n, hnM⟩, rfl⟩, LinearEquiv.ext fun v => Subtype.ext ?_⟩
  obtain ⟨b, hbA, hbQ, hbv⟩ := S.mem_clSub_iff.mp v.2
  have hpb : p (vec hbA) = v := Subtype.ext (by rw [hp, clMap_apply, elt_vec, hbv])
  rw [coe_resAt_apply, ← hbv]
  change ((S.ρ ⟨n, hnM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl b) = _
  rw [S.ρ_cl ⟨n, hnM⟩ hbQ, transvection_apply, Submodule.coe_add, Submodule.coe_smul, ← hbv,
    ← hac]
  have h2 := congrArg hA.clMap (LinearEquiv.congr_fun hn (vec hbA))
  rw [transvection_apply, map_add, map_smul, clMap_apply, clMap_apply, elt_conjLinear,
    elt_vec] at h2
  change S.cl ((n : G) * b * (n : G)⁻¹) = _
  rw [h2]
  change S.cl b + φ (p (vec hbA)) • hA.clMap (vec haA) = S.cl b + φ v • S.cl a
  rw [hpb, clMap_apply, elt_vec]

theorem resAt_bijective (hsurj : Function.Surjective (conjLinear (AN A))) :
    Function.Bijective (resAt S A hM) :=
  ⟨hA.resAt_injective hM, hA.resAt_surjective hM hsurj⟩

theorem nonempty_Mbar_mulEquiv (hsurj : Function.Surjective (conjLinear (AN A))) :
    Nonempty (S.Mbar ≃* GL (Fin S.width) (ZMod 2)) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_mulEquiv_GL hA.finrank_clSub
  exact ⟨(MulEquiv.ofBijective _ (hA.resAt_bijective hM hsurj)).trans e⟩

end MaxEA

end CFSG.LargeExtraspecial.DW
