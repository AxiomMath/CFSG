module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LargeExtraspecial.S6ThreeF
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem finrank_map_Vt_eq (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} (r : Rbar S g t) :
    finrank (ZMod 2) ((Vt S g t).map (((r : S.O) : S.Qt →ₗ[ZMod 2] S.Qt) - 1)) =
      finrank (ZMod 2) (commSpace (resV haQ t r)) := by
  have e : (commSpace (resV haQ t r)).map (Vt S g t).subtype =
      (Vt S g t).map (((r : S.O) : S.Qt →ₗ[ZMod 2] S.Qt) - 1) := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨u, rfl⟩ := mem_commSpace.mp hw
      refine ⟨u, u.2, ?_⟩
      simp [coe_resV_apply]
    · rintro ⟨u, hu, rfl⟩
      refine ⟨resV haQ t r ⟨u, hu⟩ - ⟨u, hu⟩, sub_mem_commSpace _ _, ?_⟩
      simp [coe_resV_apply]
  rw [← e, Submodule.finrank_map_subtype_eq]

section Flag

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hSp : SpCase H C ht ht1 hVQ) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
  (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
include hCE H hNo C ht ht1 hVQ hSp hh hb

theorem finrank_commSpace_ge {τ : S.O} (hτ : τ ∈ Rbar S g t) :
    2 * finrank (ZMod 2) ((Vt S g t).map ((τ : S.Qt →ₗ[ZMod 2] S.Qt) - 1)) +
      finrank (ZMod 2) (((Wone S g t g ((h : G) * g)).map
        ((τ : S.Qt →ₗ[ZMod 2] S.Qt) - 1)).map (Vone S g t g ((h : G) * g)).mkQ) ≤
      finrank (ZMod 2) (commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  have haQ := H.conj_mem
  obtain ⟨hct, hft⟩ := commSpace_t_eq H C ht ht1 hVQ
  have hτt := commute_of_mem_Rbar haQ hτ
  set φ : S.Qt →ₗ[ZMod 2] S.Qt := (τ : S.Qt →ₗ[ZMod 2] S.Qt) - 1 with hφ
  set ψ : S.Qt →ₗ[ZMod 2] S.Qt := (t : S.Qt →ₗ[ZMod 2] S.Qt) - 1 with hψ
  have hcomm : ψ ∘ₗ φ = φ ∘ₗ ψ := by
    ext v
    have e : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
        (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
      rw [← coe_mul_apply, ← coe_mul_apply, hτt]
    simp only [hφ, hψ, LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearEquiv.coe_coe, map_sub, e]
    abel_nf
  have h1 : (LinearMap.range φ).map ψ = (Vt S g t).map φ := by
    rw [← LinearMap.range_comp, hcomm, LinearMap.range_comp]
    congr 1
  have h2 : LinearMap.ker ψ = Wt S g t := hft
  have h3 := S2.finrank_map_add_finrank_inf_ker ψ (LinearMap.range φ)
  rw [h1, h2] at h3
  set X := Vone S g t g ((h : G) * g) with hX
  set Y := Wone S g t g ((h : G) * g) with hY
  have hYφ : ∀ w ∈ Y, φ w ∈ Y := fun w hw =>
    sub_mem (apply_mem_Wone hCE H hNo C ht ht1 hVQ hSp hh hb hτ hw) hw
  have h4 : Y.map φ ≤ LinearMap.range φ ⊓ Wt S g t := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨LinearMap.mem_range_self φ w, Wone_le_Wt _ _ (hYφ w hw)⟩
  have h5 := S2.finrank_map_add_finrank_inf_ker X.mkQ (Y.map φ)
  rw [Submodule.ker_mkQ] at h5
  have hVY : Vt S g t ≤ Y :=
    (Vt_le_Vone _ _).trans (Vone_le_Wone H C ht ht1 hVQ hh hb)
  have h6 : (Vt S g t).map φ ≤ Y.map φ ⊓ X := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨⟨v, hVY hv, rfl⟩, Vt_le_Vone _ _ ?_⟩
    exact sub_mem (apply_mem_Vt_of_mem_Rbar haQ hτ hv) hv
  have h7 := Submodule.finrank_mono h4
  have h8 := Submodule.finrank_mono h6
  change _ ≤ finrank (ZMod 2) (LinearMap.range φ)
  omega

end Flag

theorem finrank_commSpace_secMk (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O}
    {X Y : Submodule (ZMod 2) S.Qt} {Z : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)}
    (ρ : Z →* (↥(Y.map X.mkQ) ≃ₗ[ZMod 2] ↥(Y.map X.mkQ)))
    (hρ : ∀ (e : Z) (x : Rbar S g t), (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = resV haQ t x →
      ∀ w (hw : w ∈ Y), ((ρ e (secMk X hw) : ↥(Y.map X.mkQ)) : S.Qt ⧸ X) =
        X.mkQ (((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w))
    (e : Z) (r : Rbar S g t) (he : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = resV haQ t r) :
    finrank (ZMod 2) (commSpace (ρ e)) =
      finrank (ZMod 2) ((Y.map (((r : S.O) : S.Qt →ₗ[ZMod 2] S.Qt) - 1)).map X.mkQ) := by
  have e1 : (commSpace (ρ e)).map (Y.map X.mkQ).subtype =
      (Y.map (((r : S.O) : S.Qt →ₗ[ZMod 2] S.Qt) - 1)).map X.mkQ := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨m, rfl⟩ := mem_commSpace.mp hu
      obtain ⟨w, hw, rfl⟩ := exists_secMk X m
      refine ⟨_, ⟨w, hw, rfl⟩, ?_⟩
      rw [Submodule.coe_subtype, Submodule.coe_sub, hρ e r he w hw, coe_secMk]
      simp
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨ρ e (secMk X hw) - secMk X hw, sub_mem_commSpace _ _, ?_⟩
      rw [Submodule.coe_subtype, Submodule.coe_sub, hρ e r he w hw, coe_secMk]
      simp
  rw [← e1, Submodule.finrank_map_subtype_eq]

end CFSG.LargeExtraspecial.S9
