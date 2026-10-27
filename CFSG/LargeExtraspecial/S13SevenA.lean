module

public import CFSG.LargeExtraspecial.S13Pts
public import CFSG.LargeExtraspecial.S13TwoE
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {K : Subgroup S.O}

theorem linCase_pt (H : Hyp4 S g) {σ : S.O} (hσ : σ ∈ S.Lbar g) (hL : LinCase S g hσ)
    {v : S.Qt} (hv : v ∈ Vt S g σ) (hv0 : v ≠ 0) :
    ∃ m : S.M, v = S.cl ((m : G) * g * S.z * ((m : G) * g)⁻¹) ∧ σ ∈ S.Lbar ((m : G) * g) ∧
      Vt S g σ ≤ S.clSub (S.QG ⊓ S.Qa ((m : G) * g)) := by
  obtain ⟨x, hx, hvx⟩ := hL.mem_orbit ⟨v, hv⟩ (fun h => hv0 (congrArg Subtype.val h))
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hx)
  have hv' : v = S.cl ((m : G) * g * S.z * ((m : G) * g)⁻¹) := by
    rw [← ρ_cl_conj_z S m H.conj_mem]
    exact hvx
  refine ⟨m, hv', ?_, ?_⟩
  · have h1 := conj_mem_Lbar_mul S m hσ
    have hc := commute_of_mem_Rbar H.conj_mem hx
    rwa [hc, mul_inv_cancel_right] at h1
  · intro w hw
    have hw' := apply_mem_Vt_of_mem_Rbar H.conj_mem (inv_mem hx) hw
    have := apply_mem_clSub_Qa_mul m g (Vt_le_clSub_of_V_le hL.le_Qa hw')
    rwa [apply_inv_apply_O] at this

theorem exists_pt_not_mem (H : Hyp4 S g) (hirr : ¬ S.IsReducible)
    {U : Submodule (ZMod 2) S.Qt} (hU : U ≠ ⊤) :
    ∃ c : S.M, S.cl ((c : G) * g * S.z * ((c : G) * g)⁻¹) ∉ U := by
  by_contra hcon
  push Not at hcon
  set A : Set S.Qt := {v | ∃ c : S.M, v = S.cl ((c : G) * g * S.z * ((c : G) * g)⁻¹)} with hA
  set P := Submodule.span (ZMod 2) A with hP
  have hPU : P ≤ U := Submodule.span_le.mpr (by rintro _ ⟨c, rfl⟩; exact hcon c)
  have hPinv : ∀ m : S.M, ∀ v ∈ P, ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ P := by
    intro m v hv
    have h1 : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈
        P.map ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap :=
      Submodule.mem_map_of_mem hv
    rw [hP, Submodule.map_span] at h1
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    refine ⟨m * c, ?_⟩
    have hcQ := conj_mem_QG' S c.2 H.conj_mem
    simp only [LinearEquiv.coe_coe]
    rw [ρ_cl_conj_z S m hcQ, Subgroup.coe_mul]
    group
  have hPne : P ≠ ⊥ := by
    intro h0
    have : S.cl (((1 : S.M) : G) * g * S.z * (((1 : S.M) : G) * g)⁻¹) ∈ P :=
      Submodule.subset_span ⟨1, rfl⟩
    rw [h0, Submodule.mem_bot] at this
    exact cl_conj_z_ne_zero S H.conj_mem H.conj_ne (by simpa using this)
  by_cases hPt : P = ⊤
  · exact hU (top_le_iff.mp (hPt ▸ hPU))
  · exact hirr ⟨P, hPne, hPt, hPinv⟩

theorem cl_mem_clSub_of_add (H : Hyp4 S g) {h₁ h₂ h₃ y : S.M}
    (hsum : S.cl ((h₁ : G) * g * S.z * ((h₁ : G) * g)⁻¹) +
      S.cl ((h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹) = S.cl ((h₃ : G) * g * S.z * ((h₃ : G) * g)⁻¹))
    (hy₁ : S.cl ((y : G) * g * S.z * ((y : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa ((h₁ : G) * g)))
    (hy₂ : S.cl ((y : G) * g * S.z * ((y : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa ((h₂ : G) * g))) :
    S.cl ((y : G) * g * S.z * ((y : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa ((h₃ : G) * g)) := by
  have e₁ := cl_mem_clSub_symm H hy₁
  have e₂ := cl_mem_clSub_symm H hy₂
  have e₃ : S.cl ((h₃ : G) * g * S.z * ((h₃ : G) * g)⁻¹) ∈
      S.clSub (S.QG ⊓ S.Qa ((y : G) * g)) := hsum ▸ add_mem e₁ e₂
  exact cl_mem_clSub_symm H e₃

end CFSG.LargeExtraspecial.S13
