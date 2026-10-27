module

public import CFSG.LargeExtraspecial.S11Five

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u_G

variable {G : Type u_G} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} {τ : S.M}
  {u : G}

variable (S g) in
@[expose] noncomputable def TtHom (H : Hyp4 S g) (t : S.O) :
    Rbar S g t →* (Tt S g t ≃ₗ[ZMod 2] Tt S g t) :=
  restrictHom (S.O.subtype.comp (Rbar S g t).subtype) (Tt S g t)
    (fun x _ hv => apply_mem_Tt H x.2 hv)

theorem coe_TtHom_apply (H : Hyp4 S g) (x : Rbar S g t) (v : Tt S g t) :
    ((TtHom S g H t x v : Tt S g t) : S.Qt) = ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v :=
  rfl

variable (hy : Hyp S g) (K : Conf S g t τ u) (hCE : CentralExtInput.{u_G})
include hy K hCE

theorem Conf.apply_sub_mem_Vt_of_mem_Nbar {x : S.O} (hx : x ∈ Nbar S g t) {w : S.Qt}
    (hw : w ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
  obtain ⟨y, hyu, rfl⟩ := (S4.mem_Lbar S).mp (K.timmesfeld_11_5 hy hCE hx)
  obtain ⟨c, hcQ, rfl⟩ := S.exists_cl w
  have hcτ : c * τ = τ * c := commute_of_cl_mem_commSpace K.rho_eq K.conj_eq
    (isTypeA_of_linCase hy.hyp4 K.ne_one K.lin).2.2.2.2 hcQ hw
  have hmem : (y : G) * c * (y : G)⁻¹ * c⁻¹ ∈ S.QG ⊓ S.Qa u := by
    refine ⟨S.commutator_mem_QG y.2 hcQ, ?_⟩
    rw [show (y : G) * c * (y : G)⁻¹ * c⁻¹ = y * (c * (y : G)⁻¹ * c⁻¹) by group]
    exact mul_mem hyu.1 (conj_mem_Qa_of_commute K.conj_eq (inv_mem hyu.1) hcτ)
  rw [← S.cl_commutator y.2 hcQ, ← K.timmesfeld_11_3 hy]
  exact S.cl_mem_clSub hmem hmem.1

theorem Conf.apply_eq_of_mem_Nbar {x : S.O} (hx : x ∈ Nbar S g t) {w : S.Qt}
    (hw : w ∈ Tt S g t) : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
  obtain ⟨w₁, hw₁, rfl⟩ := mem_Tt.mp hw
  set xl := (x : S.Qt ≃ₗ[ZMod 2] S.Qt) with hxl
  set tl := (t : S.Qt ≃ₗ[ZMod 2] S.Qt) with htl
  have hxt : x * t = t * x := commute_of_mem_Rbar hy.hyp4.conj_mem hx.1
  have hxt' : ∀ v, xl (tl v) = tl (xl v) := fun v => by
    rw [← coe_mul_apply, ← coe_mul_apply, hxt]
  have key : xl w₁ - w₁ ∈ fixSpace tl := by
    rw [fixSpace_eq_orthogonal_commSpace S.q_nondegenerate t.2 (coe_mul_self K.mul_self),
      LinearMap.BilinForm.mem_orthogonal_iff]
    intro v hv
    change polar S.q v (xl w₁ - w₁) = 0
    have h1 : polar S.q v (xl w₁) = polar S.q (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) w₁ := by
      have := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup x.2
        (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) w₁
      rwa [apply_inv_apply_O] at this
    rw [polar_sub_right, h1, ← polar_sub_left]
    exact mem_Wt.mp hw₁ _ (K.apply_sub_mem_Vt_of_mem_Nbar hy hCE (inv_mem hx) hv)
  have e : xl (tl w₁ - w₁) = tl w₁ - w₁ + (tl (xl w₁ - w₁) - (xl w₁ - w₁)) := by
    rw [map_sub, hxt', map_sub]
    abel
  rw [e, mem_fixSpace.mp key, sub_self, add_zero]

theorem Conf.ker_resV_le : (resV hy.hyp4.conj_mem t).ker ≤ (TtHom S g hy.hyp4 t).ker := by
  intro x hx
  rw [MonoidHom.mem_ker, resV_eq_one_iff] at hx
  rw [MonoidHom.mem_ker]
  exact LinearEquiv.ext fun v => Subtype.ext (K.apply_eq_of_mem_Nbar hy hCE hx v.2)

end CFSG.LargeExtraspecial.S11
