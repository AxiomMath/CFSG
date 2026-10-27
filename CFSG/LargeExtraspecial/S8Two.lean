module

public import CFSG.LargeExtraspecial.S8Std
public import CFSG.LargeExtraspecial.S8FusB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem exists_mem_Lbar_of_mem_orbit (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t)
    {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹) {d : S.Qt} (hdV : d ∈ Vt S g t)
    (hdτ : d ∈ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) (hd : d ∈ orbit S g t) :
    ∃ k : S.M, S.ρ k ∈ Rbar S g t ∧ τ ∈ S.Lbar ((k : G) * g) := by
  obtain ⟨k, hk, rfl⟩ := exists_of_mem_orbit hd H.conj_mem
  have hV1eq : commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (Vt S g t).map (x : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap := by
    rw [hxτ, commSpace_conj, (commSpace_t_eq H C ht ht1 hVQ).1]
  rw [hV1eq] at hdτ
  obtain ⟨v, hv, hvd⟩ := hdτ
  obtain ⟨k₁, hk₁⟩ := MonoidHom.mem_range.mp (S.Mbar.mul_mem (inv_mem hxM) (Rbar_le_Mbar hk))
  have hv1 : v = S.cl ((k₁ : G) * g * S.z * ((k₁ : G) * g)⁻¹) := by
    rw [← ρ_cl_conj_z S k₁ H.conj_mem, hk₁]
    change v = ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((S.ρ k : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl (g * S.z * g⁻¹)))
    rw [ρ_cl_conj_z S k H.conj_mem, ← hvd]
    exact (inv_apply_apply_O x v).symm
  have hvorb := hfus k₁ (hv1 ▸ hv)
  rw [← hv1] at hvorb
  obtain ⟨k₂, hk₂, hk₂v⟩ := exists_of_mem_orbit hvorb H.conj_mem
  obtain ⟨k₃, hk₃⟩ := MonoidHom.mem_range.mp (S.Mbar.mul_mem hxM (Rbar_le_Mbar hk₂))
  have hcl : S.cl ((k₃ : G) * g * S.z * ((k₃ : G) * g)⁻¹) =
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) := by
    rw [← ρ_cl_conj_z S k₃ H.conj_mem, hk₃]
    change (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((S.ρ k₂ : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl (g * S.z * g⁻¹))) = _
    rw [ρ_cl_conj_z S k₂ H.conj_mem, ← hk₂v]
    exact hvd
  have hLeq := Lbar_eq_of_cl_eq S (conj_mem_QG' S k.2 H.conj_mem) (conj_ne_z' S k.2 H.conj_ne)
    (conj_mem_QG' S k₃.2 H.conj_mem) hcl
  refine ⟨k, hk, ?_⟩
  rw [← hLeq]
  have h1 := conj_mem_Lbar_mul S k₃ ht
  have e : S.ρ k₃ * t * (S.ρ k₃)⁻¹ = τ := by
    rw [hk₃, hxτ, mul_inv_rev]
    have hc := commute_of_mem_Rbar H.conj_mem hk₂
    calc x * S.ρ k₂ * t * ((S.ρ k₂)⁻¹ * x⁻¹) = x * (S.ρ k₂ * t) * (S.ρ k₂)⁻¹ * x⁻¹ := by
          group
      _ = x * (t * S.ρ k₂) * (S.ρ k₂)⁻¹ * x⁻¹ := by rw [hc]
      _ = x * t * x⁻¹ := by group
  rwa [e] at h1

theorem not_mem_orbit_of_not_mem_Nbar (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t)
    (hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹) (hτN : τ ∉ Nbar S g t) :
    ∀ d ∈ Vt S g t ⊓ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt), d ∉ orbit S g t := by
  rintro d ⟨hdV, hdτ⟩ hd
  obtain ⟨k, hk, hτk⟩ := exists_mem_Lbar_of_mem_orbit H C ht ht1 hVQ hfus hxM hxτ hdV hdτ hd
  apply hτN
  have h1 : (S.ρ k)⁻¹ * τ * S.ρ k ∈ S.Lbar g := (mem_Lbar_mul_iff S k g).mp hτk
  have e : (S.ρ k)⁻¹ * τ * S.ρ k = ((S.ρ k)⁻¹ * x) * t * ((S.ρ k)⁻¹ * x)⁻¹ := by
    rw [hxτ]; group
  rw [e] at h1
  have h2 := hsub _ (S.Mbar.mul_mem (inv_mem (Rbar_le_Mbar hk)) hxM) h1
  rw [← e] at h2
  have h3 := conj_mem_Nbar H.conj_mem (commute_of_mem_Rbar H.conj_mem hk) h2
  have e' : S.ρ k * ((S.ρ k)⁻¹ * τ * S.ρ k) * (S.ρ k)⁻¹ = τ := by group
  rwa [e'] at h3

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem eq_one_or_transvection (D : Std H C ht ht1 hVQ)
    (hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t)
    (hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹) (hτt : τ * t = t * τ)
    (hτN : τ ∉ Nbar S g t) :
    (∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) ∨
      ∃ d : Vt S g t, D.Q d = 1 ∧ ∀ v : Vt S g t,
        (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v + polar D.Q v d • (d : S.Qt) := by
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  have hτM : τ ∈ S.Mbar := by
    rw [hxτ]; exact S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  have hτC : τ ∈ CMt S t := mem_CMt.mpr ⟨hτM, hτt⟩
  set φ := resCV S g H.conj_mem t ⟨τ, hτC⟩ with hφ
  by_cases h1 : φ = 1
  · left
    intro v hv
    have := congrArg (fun f : Vt S g t ≃ₗ[ZMod 2] Vt S g t => ((f ⟨v, hv⟩ : Vt S g t) : S.Qt)) h1
    simpa only [hφ, coe_resCV_apply, LinearEquiv.coe_one, id_eq] using this
  · right
    have hO := resCV_mem_orthogonalGroup H ht D.hsing hfus ⟨τ, hτC⟩
    have hsq : φ * φ = 1 := by
      rw [hφ, ← map_mul]
      have e : (⟨τ, hτC⟩ : CMt S t) * ⟨τ, hτC⟩ = 1 := Subtype.ext (by
        change τ * τ = 1
        rw [hxτ]
        calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
          _ = 1 := by rw [htt, mul_one, mul_inv_cancel])
      rw [e, map_one]
    have hanis : ∀ c ∈ commSpace φ, D.Q c = 0 → c = 0 := by
      intro c hc hQc
      by_contra hc0
      have horb := (mem_orbitOf_RmodN_iff H.conj_mem ht).mp ((D.hsing c hc0).mp hQc)
      obtain ⟨v, rfl⟩ := mem_commSpace.mp hc
      refine not_mem_orbit_of_not_mem_Nbar H C ht ht1 hVQ hfus hsub hxM hxτ hτN _
        ⟨(φ v - v : Vt S g t).2, ?_⟩ horb
      rw [Submodule.coe_sub, hφ, coe_resCV_apply]
      exact sub_mem_commSpace _ _
    obtain ⟨-, c, hc, hcv, -, -⟩ := eq_transvection_of_anisotropic_commSpace D.hQ hO hsq h1 hanis
    refine ⟨c, hc, fun v => ?_⟩
    have := congrArg Subtype.val (hcv v)
    rwa [coe_resCV_apply, Submodule.coe_add, Submodule.coe_smul] at this

end CFSG.LargeExtraspecial.S8
