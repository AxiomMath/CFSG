module

public import CFSG.Monster.GMS.Griess13.ChecksUniqueness
public import CFSG.Sporadic.Co1.Module.Forms
public import CFSG.LargeExtraspecial.S3Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.Blueprint

namespace CFSG.GF2Type.Widths1112

variable {G : Type} [Group G] [Finite G]

private noncomputable def co1IdentHom (S : Setting G) (e : S.Mbar ≃* NativeSporadic.Co1) :
    NativeSporadic.Co1 →* S.Mbar :=
  { toFun := e.symm, map_one' := map_one e.symm, map_mul' := map_mul e.symm }

private noncomputable def co1IdentRep (S : Setting G) (e : S.Mbar ≃* NativeSporadic.Co1) :
    Representation (ZMod 2) NativeSporadic.Co1 S.Qt :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    ((Subgroup.subtype S.O).comp ((Subgroup.subtype S.Mbar).comp (co1IdentHom S e)))

private theorem co1IdentRep_apply (S : Setting G) (e : S.Mbar ≃* NativeSporadic.Co1)
    (A : NativeSporadic.Co1) (v : S.Qt) :
    co1IdentRep S e A v = ((((e.symm A : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := rfl

theorem co1_ident
    (S : Setting G) (e : S.Mbar ≃* NativeSporadic.Co1) (hw : S.width = 12) :
    ∃ ψ : S.Qt ≃ₗ[ZMod 2] (Fin 24 → ZMod 2),
      (∀ (m : S.Mbar) (v : S.Qt), ψ (((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
        CFSG.Monster.GMS.co1Act (e m) (ψ v)) ∧
      ∀ v : S.Qt, S.q v = CFSG.Sporadic.Co1.Module.q₀ (ψ v) := by
  haveI : Nontrivial NativeSporadic.Co1 := CFSG.Sporadic.Co1.fam_co1_simplicity.2.1
  have h24 : Module.finrank (ZMod 2) S.Qt = 24 := by
    have := S.finrank_Qt_eq_two_mul_width
    omega
  have hρ : co1IdentRep S e ≠ 1 := by
    intro h
    obtain ⟨A, hA⟩ : ∃ A : NativeSporadic.Co1, A ≠ 1 := exists_ne 1
    have hA1 : co1IdentRep S e A = 1 := by
      rw [h, MonoidHom.one_apply]
    have hlin : ((((e.symm A : S.Mbar) : S.O)) : S.Qt ≃ₗ[ZMod 2] S.Qt) = 1 :=
      LinearEquiv.ext fun v => by
        have h1 := LinearMap.congr_fun hA1 v
        rw [co1IdentRep_apply] at h1
        exact h1
    have hM : e.symm A = 1 := Subtype.ext (Subtype.ext hlin)
    apply hA
    calc A = e (e.symm A) := (e.apply_symm_apply A).symm
      _ = e 1 := by rw [hM]
      _ = 1 := map_one e
  obtain ⟨ψ, hψ⟩ := CFSG.Monster.GMS.co1ModuleUniqueness S.Qt h24 (co1IdentRep S e) hρ
  have hmain : ∀ (m : S.Mbar) (v : S.Qt), ψ (((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
      CFSG.Monster.GMS.co1Act (e m) (ψ v) := by
    intro m v
    have h := hψ (e m) v
    have hm : co1IdentRep S e (e m) v = ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
      rw [co1IdentRep_apply, MulEquiv.symm_apply_apply]
    rw [← hm]
    exact h
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : (Fin 24 → ZMod 2) → ZMod 2, ∀ u, Θ u = S.q (ψ.symm u) :=
    ⟨fun u => S.q (ψ.symm u), fun _ => rfl⟩
  have hbil : ∀ u u' v : Fin 24 → ZMod 2,
      CFSG.Sporadic.Co1.Module.polar Θ (u + u') v =
        CFSG.Sporadic.Co1.Module.polar Θ u v + CFSG.Sporadic.Co1.Module.polar Θ u' v := by
    intro u u' v
    have key := QuadraticMap.polar_add_left S.q (ψ.symm u) (ψ.symm u') (ψ.symm v)
    simp only [CFSG.Sporadic.Co1.Module.polar, QuadraticMap.polar, hΘ, map_add] at key ⊢
    linear_combination key
  have hinv : ∀ (g : NativeSporadic.Co1) (v : Fin 24 → ZMod 2),
      Θ (CFSG.Sporadic.Co1.Module.co1Act g v) = Θ v := by
    intro g v
    have h1 := hψ g (ψ.symm v)
    rw [ψ.apply_symm_apply] at h1
    have h2 : ψ.symm (CFSG.Monster.GMS.co1Act g v) =
        ((((e.symm g : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (ψ.symm v)) := by
      rw [← h1, ψ.symm_apply_apply]
      rfl
    have hsp : CFSG.Sporadic.Co1.Module.co1Act g v = CFSG.Monster.GMS.co1Act g v := rfl
    simp only [hΘ]
    rw [hsp, h2]
    exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup ((e.symm g : S.Mbar) : S.O).2
      (ψ.symm v)
  have hΘne : Θ ≠ 0 := by
    intro h0
    have hq0 : ∀ x : S.Qt, S.q x = 0 := by
      intro x
      have h := congrFun h0 (ψ x)
      rw [hΘ, ψ.symm_apply_apply, Pi.zero_apply] at h
      exact h
    obtain ⟨x, hx⟩ : ∃ x : S.Qt, x ≠ 0 := by
      haveI : Nontrivial S.Qt := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
      exact exists_ne 0
    apply hx
    apply S.q_nondegenerate.1 x
    intro y
    rw [QuadraticMap.polarBilin_apply_apply]
    simp only [QuadraticMap.polar, hq0, sub_zero, sub_self]
  rcases CFSG.Sporadic.Co1.Module.co1_invariant_quadratic hbil hinv with h0 | hq
  · exact absurd h0 hΘne
  · refine ⟨ψ, hmain, fun v => ?_⟩
    have h := congrFun hq (ψ v)
    rw [hΘ, ψ.symm_apply_apply] at h
    exact h

end CFSG.GF2Type.Widths1112
