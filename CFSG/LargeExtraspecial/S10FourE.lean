module

public import CFSG.LargeExtraspecial.S10FlagA
public import CFSG.LargeExtraspecial.S10TwoB
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem map_clSub_inf_Wt (X : Hyp10 S g t) {k : S.M} (hk : S.ρ k ∈ Rbar S g t) (g' : G) :
    (S.clSub (S.QG ⊓ S.Qa g') ⊓ Wt S g t).map
        (((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) =
      S.clSub (S.QG ⊓ S.Qa ((k : G) * g')) ⊓ Wt S g t := by
  ext w
  rw [Submodule.mem_map_equiv (e := ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))]
  change (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ S.clSub (S.QG ⊓ S.Qa g') ⊓ Wt S g t ↔ _
  rw [Submodule.mem_inf, Submodule.mem_inf, mem_clSub_Qa_mul_iff (g := g') k]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => apply_mem_Wt X.H (inv_mem hk) h⟩
  have := apply_mem_Wt X.H hk h
  rwa [apply_inv_apply_O] at this

theorem map_Vt_eq (X : Hyp10 S g t) {k : S.M} (hk : S.ρ k ∈ Rbar S g t) :
    (Vt S g t).map (((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) =
      Vt S g t := by
  ext w
  rw [Submodule.mem_map_equiv (e := ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))]
  change (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Vt S g t ↔ _
  refine ⟨fun h => ?_, fun h => apply_mem_Vt_of_mem_Rbar X.haQ (inv_mem hk) h⟩
  have := apply_mem_Vt_of_mem_Rbar X.haQ hk h
  rwa [apply_inv_apply_O] at this

theorem beta_aV_orbV_inv_mul (X : Hyp10 S g t) {k₁ k₂ : S.M} (hk₁ : S.ρ k₁ ∈ Rbar S g t)
    (hk₂ : S.ρ k₂ ∈ Rbar S g t) (hh : S.ρ (k₁⁻¹ * k₂) ∈ Rbar S g t) :
    beta X.H X.C X.ht X.ht1 X.hVQ (aV X.ht) (orbV X.haQ X.ht hh) =
      beta X.H X.C X.ht X.ht1 X.hVQ (orbV X.haQ X.ht hk₁) (orbV X.haQ X.ht hk₂) := by
  set r : Rbar S g t := ⟨S.ρ k₁, hk₁⟩
  have e₁ : aV X.ht = resV X.haQ t r⁻¹ (orbV X.haQ X.ht hk₁) := Subtype.ext (by
    rw [coe_resV_apply, coe_orbV]
    exact (inv_apply_apply_O _ _).symm)
  have e₂ : orbV X.haQ X.ht hh = resV X.haQ t r⁻¹ (orbV X.haQ X.ht hk₂) := Subtype.ext (by
    rw [coe_resV_apply, coe_orbV, coe_orbV, map_mul, map_inv]
    rfl)
  rw [e₁, e₂, beta_apply_resV]

theorem decomp_pair (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) {k₁ k₂ : S.M}
    (hk₁ : S.ρ k₁ ∈ Rbar S g t) (hk₂ : S.ρ k₂ ∈ Rbar S g t)
    (hβ : beta X.H X.C X.ht X.ht1 X.hVQ (orbV X.haQ X.ht hk₁) (orbV X.haQ X.ht hk₂) = 1) :
    (S.clSub (S.QG ⊓ S.Qa ((k₁ : G) * g)) ⊓ Wt S g t) ⊔
        (S.clSub (S.QG ⊓ S.Qa ((k₂ : G) * g)) ⊓ Wt S g t) = Wt S g t ∧
      ((S.clSub (S.QG ⊓ S.Qa ((k₁ : G) * g)) ⊓ Wt S g t) ⊔ Vt S g t) ⊓
        ((S.clSub (S.QG ⊓ S.Qa ((k₂ : G) * g)) ⊓ Wt S g t) ⊔ Vt S g t) = Vt S g t ∧
      finrank (ZMod 2) ↥((S.clSub (S.QG ⊓ S.Qa ((k₁ : G) * g)) ⊓ Wt S g t) ⊔ Vt S g t) =
        S.width ∧
      finrank (ZMod 2) ↥((S.clSub (S.QG ⊓ S.Qa ((k₂ : G) * g)) ⊓ Wt S g t) ⊔ Vt S g t) =
        S.width := by
  have hh : S.ρ (k₁⁻¹ * k₂) ∈ Rbar S g t := by
    rw [map_mul, map_inv]
    exact mul_mem (inv_mem hk₁) hk₂
  have hβ' := (beta_aV_orbV_inv_mul X hk₁ hk₂ hh).trans hβ
  have hb := not_mem_Qa_of_beta X hh hβ'
  obtain ⟨hsup, hinf, hd1, hd2, -⟩ := timmesfeld_10_1_two hCE X hh hb
  set e : S.Qt ≃ₗ[ZMod 2] S.Qt := ((S.ρ k₁ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with he
  have hA := map_clSub_inf_Wt X hk₁ g
  have hB := map_clSub_inf_Wt X hk₁ (((k₁⁻¹ * k₂ : S.M) : G) * g)
  have hk : ((k₁ : G) * (((k₁⁻¹ * k₂ : S.M) : G) * g)) = (k₂ : G) * g := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hk] at hB
  have hV := map_Vt_eq X hk₁
  have hW : (Wt S g t).map (e : S.Qt →ₗ[ZMod 2] S.Qt) = Wt S g t := by
    ext w
    rw [Submodule.mem_map_equiv (e := e)]
    change (((S.ρ k₁)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Wt S g t ↔ _
    refine ⟨fun h => ?_, fun h => apply_mem_Wt X.H (inv_mem hk₁) h⟩
    have := apply_mem_Wt X.H hk₁ h
    rwa [apply_inv_apply_O] at this
  have hinj : Function.Injective (e : S.Qt →ₗ[ZMod 2] S.Qt) := e.injective
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := congrArg (Submodule.map (e : S.Qt →ₗ[ZMod 2] S.Qt)) hsup
    rwa [Submodule.map_sup, hA, hB, hW] at this
  · have := congrArg (Submodule.map (e : S.Qt →ₗ[ZMod 2] S.Qt)) hinf
    rwa [Submodule.map_inf _ hinj, Submodule.map_sup, Submodule.map_sup, hA, hB, hV] at this
  · have h1 : ((S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊔ Vt S g t).map
        (e : S.Qt →ₗ[ZMod 2] S.Qt) = (S.clSub (S.QG ⊓ S.Qa ((k₁ : G) * g)) ⊓ Wt S g t) ⊔
          Vt S g t := by rw [Submodule.map_sup, hA, hV]
    rw [← h1, LinearEquiv.finrank_map_eq]
    exact hd1
  · have h1 : ((S.clSub (S.QG ⊓ S.Qa (((k₁⁻¹ * k₂ : S.M) : G) * g)) ⊓ Wt S g t) ⊔
        Vt S g t).map (e : S.Qt →ₗ[ZMod 2] S.Qt) =
          (S.clSub (S.QG ⊓ S.Qa ((k₂ : G) * g)) ⊓ Wt S g t) ⊔ Vt S g t := by
      rw [Submodule.map_sup, hB, hV]
    rw [← h1, LinearEquiv.finrank_map_eq]
    exact hd2

theorem width_le_of_swap (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) {k₁ k₂ : S.M}
    (hk₁ : S.ρ k₁ ∈ Rbar S g t) (hk₂ : S.ρ k₂ ∈ Rbar S g t)
    (hβ : beta X.H X.C X.ht X.ht1 X.hVQ (orbV X.haQ X.ht hk₁) (orbV X.haQ X.ht hk₂) = 1)
    {y : S.Qt ≃ₗ[ZMod 2] S.Qt} (hyV : ∀ v ∈ Vt S g t, y v ∈ Vt S g t)
    (hyP : ∀ w ∈ S.clSub (S.QG ⊓ S.Qa ((k₁ : G) * g)) ⊓ Wt S g t,
      y w ∈ S.clSub (S.QG ⊓ S.Qa ((k₂ : G) * g)) ⊓ Wt S g t) :
    S.width ≤ finrank (ZMod 2) ↥((Wt S g t).map ((y : S.Qt →ₗ[ZMod 2] S.Qt) - 1) ⊔
      Vt S g t) := by
  obtain ⟨-, hint, hd1, hd2⟩ := decomp_pair hCE X hk₁ hk₂ hβ
  set U := (S.clSub (S.QG ⊓ S.Qa ((k₁ : G) * g)) ⊓ Wt S g t) ⊔ Vt S g t with hU
  set U' := (S.clSub (S.QG ⊓ S.Qa ((k₂ : G) * g)) ⊓ Wt S g t) ⊔ Vt S g t with hU'
  have hUU' : U.map (y : S.Qt →ₗ[ZMod 2] S.Qt) ≤ U' := by
    rw [hU, Submodule.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      exact hyP w hw
    · rintro _ ⟨v, hv, rfl⟩
      exact hyV v hv
  have hsw := finrank_swap y hUU' hint
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq U U'
  rw [hint, X.h4, hd1, hd2] at hsup
  rw [X.h4, hd2] at hsw
  have hUW : U ≤ Wt S g t := sup_le inf_le_right (Vt_le_Wt X.H X.ht1)
  have hle : U.map ((y : S.Qt →ₗ[ZMod 2] S.Qt) - 1) ⊔ Vt S g t ≤
      (Wt S g t).map ((y : S.Qt →ₗ[ZMod 2] S.Qt) - 1) ⊔ Vt S g t :=
    sup_le_sup_right (Submodule.map_mono hUW) _
  have := Submodule.finrank_mono hle
  omega

theorem flag_of_commute (X : Hyp10 S g t) {x : S.Qt ≃ₗ[ZMod 2] S.Qt}
    (hxt : x * (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = (t : S.Qt ≃ₗ[ZMod 2] S.Qt) * x) :
    2 * finrank (ZMod 2) ((Vt S g t).map ((x : S.Qt →ₗ[ZMod 2] S.Qt) - 1)) +
      (finrank (ZMod 2) ↥((Wt S g t).map ((x : S.Qt →ₗ[ZMod 2] S.Qt) - 1) ⊔ Vt S g t) - 4) ≤
      finrank (ZMod 2) (commSpace x) := by
  obtain ⟨hcomm, hfix⟩ := commSpace_t_eq X.H X.C X.ht X.ht1 X.hVQ
  have hxtv : ∀ v, x ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (x v) :=
    fun v => by rw [← LinearEquiv.mul_apply, hxt, LinearEquiv.mul_apply]
  have hA : (Vt S g t).map ((x : S.Qt →ₗ[ZMod 2] S.Qt) - 1) ≤ Vt S g t := by
    rintro _ ⟨v, hv, rfl⟩
    rw [← hcomm] at hv ⊢
    obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
    refine mem_commSpace.mpr ⟨x w - w, ?_⟩
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, map_sub, hxtv]
  have hB : (Wt S g t).map ((x : S.Qt →ₗ[ZMod 2] S.Qt) - 1) ≤ Wt S g t := by
    rintro _ ⟨v, hv, rfl⟩
    have hv' : v ∈ fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := hfix ▸ hv
    rw [← hfix, mem_fixSpace]
    rw [mem_fixSpace] at hv'
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, map_sub, ← hxtv,
      hv']
  have h := finrank_flag ((x : S.Qt →ₗ[ZMod 2] S.Qt) - 1) (Vt_le_Wt X.H X.ht1) hA hB
  have h2 : finrank (ZMod 2) ↥(commSpace x ⊔ fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      finrank (ZMod 2) ((commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)).map
        ((x : S.Qt →ₗ[ZMod 2] S.Qt) - 1)) +
        finrank (ZMod 2) (fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :=
    finrank_commSpace_sup_fixSpace hxt
  rw [hcomm, hfix] at h2
  rw [X.h4] at h
  change _ + _ + (finrank (ZMod 2) ↥(commSpace x ⊔ Wt S g t) - _) ≤
    finrank (ZMod 2) (commSpace x) at h
  omega

end CFSG.LargeExtraspecial.S10
