module

public import CFSG.GF2Type.Widths1112.Co2Uniq
public import CFSG.LargeExtraspecial.S3Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.Blueprint

namespace CFSG.GF2Type.Widths1112

variable {G : Type} [Group G] [Finite G]

private noncomputable def co2IdentHom (S : Setting G) (e : S.Mbar ≃* NativeSporadic.Co2) :
    NativeSporadic.Co2 →* S.Mbar :=
  { toFun := e.symm, map_one' := map_one e.symm, map_mul' := map_mul e.symm }

private noncomputable def co2IdentRep (S : Setting G) (e : S.Mbar ≃* NativeSporadic.Co2) :
    Representation (ZMod 2) NativeSporadic.Co2 S.Qt :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    ((Subgroup.subtype S.O).comp ((Subgroup.subtype S.Mbar).comp (co2IdentHom S e)))

private theorem co2IdentRep_apply (S : Setting G) (e : S.Mbar ≃* NativeSporadic.Co2)
    (A : NativeSporadic.Co2) (v : S.Qt) :
    co2IdentRep S e A v = ((((e.symm A : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := rfl

theorem co2_ident (hU : Co2ModuleUniqueness)
    (S : Setting G) (e : S.Mbar ≃* NativeSporadic.Co2) (hw : S.width = 11) :
    ∃ ψ : S.Qt ≃ₗ[ZMod 2] (Fin 22 → ZMod 2),
      (∀ (m : S.Mbar) (v : S.Qt), ψ (((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
        co2Act (e m) (ψ v)) ∧
      ∀ v : S.Qt, S.q v = q₀₂ (ψ v) := by
  have h22 : Module.finrank (ZMod 2) S.Qt = 22 := by
    have := S.finrank_Qt_eq_two_mul_width
    omega
  have hinj : Function.Injective (co2IdentRep S e) := by
    refine (injective_iff_map_eq_one _).mpr fun A hA1 => ?_
    have hlin : ((((e.symm A : S.Mbar) : S.O)) : S.Qt ≃ₗ[ZMod 2] S.Qt) = 1 :=
      LinearEquiv.ext fun v => by
        have h1 := LinearMap.congr_fun hA1 v
        rw [co2IdentRep_apply] at h1
        exact h1
    have hM : e.symm A = 1 := Subtype.ext (Subtype.ext hlin)
    calc A = e (e.symm A) := (e.apply_symm_apply A).symm
      _ = e 1 := by rw [hM]
      _ = 1 := map_one e
  have hinvρ : ∀ (g : NativeSporadic.Co2) (v : S.Qt),
      S.q (co2IdentRep S e g v) = S.q v := by
    intro g v
    rw [co2IdentRep_apply]
    exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup ((e.symm g : S.Mbar) : S.O).2 v
  obtain ⟨ψ, hψ⟩ := hU S.Qt h22 (co2IdentRep S e) hinj S.q S.q_nondegenerate hinvρ
  have hmain : ∀ (m : S.Mbar) (v : S.Qt), ψ (((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
      co2Act (e m) (ψ v) := by
    intro m v
    have h := hψ (e m) v
    have hm : co2IdentRep S e (e m) v = ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
      rw [co2IdentRep_apply, MulEquiv.symm_apply_apply]
    rw [← hm]
    exact h
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : (Fin 22 → ZMod 2) → ZMod 2, ∀ u, Θ u = S.q (ψ.symm u) :=
    ⟨fun u => S.q (ψ.symm u), fun _ => rfl⟩
  have hbil : ∀ u u' v : Fin 22 → ZMod 2,
      Θ (u + u' + v) - Θ (u + u') - Θ v =
        (Θ (u + v) - Θ u - Θ v) + (Θ (u' + v) - Θ u' - Θ v) := by
    intro u u' v
    have key := QuadraticMap.polar_add_left S.q (ψ.symm u) (ψ.symm u') (ψ.symm v)
    simp only [QuadraticMap.polar, hΘ, map_add] at key ⊢
    linear_combination key
  have hinv : ∀ (g : NativeSporadic.Co2) (v : Fin 22 → ZMod 2),
      Θ (co2Act g v) = Θ v := by
    intro g v
    have h1 := hψ g (ψ.symm v)
    rw [ψ.apply_symm_apply] at h1
    have h2 : ψ.symm (co2Act g v) = co2IdentRep S e g (ψ.symm v) := by
      rw [← h1, ψ.symm_apply_apply]
    simp only [hΘ]
    rw [h2]
    exact hinvρ g (ψ.symm v)
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
  rcases co2_invariant_quadratic (q := Θ) hbil hinv with h0 | hq
  · exact absurd h0 hΘne
  · refine ⟨ψ, hmain, fun v => ?_⟩
    have h := congrFun hq (ψ v)
    rw [hΘ, ψ.symm_apply_apply] at h
    exact h

end CFSG.GF2Type.Widths1112
