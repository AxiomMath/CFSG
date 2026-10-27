module

public import CFSG.LargeExtraspecial.S10FlagB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

theorem exists_conj_pf_E00 : ∃ δ : Gm, pf E00 (act (δ⁻¹ * (τ₁ * τ₂) * δ) E00) = 1 := by
  decide +kernel

theorem τ₁τ₂_ne_one : τ₁ * τ₂ ≠ 1 := by decide +kernel

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem finrank_clSub_Qa (X : Hyp10 S g t) :
    finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) = S.width := by
  have hz : S.z ∈ S.QG ⊓ S.Qa g :=
    ⟨S.z_mem_QG, S.z_mem_Qa_of_mem_QG rfl X.haQ X.H.conj_ne⟩
  have h1 := S.card_clPre (S.clSub (S.QG ⊓ S.Qa g))
  rw [S.clPre_clSub inf_le_left hz, S.card_submodule, X.C.card_QG_inf_Qa] at h1
  have h2 : 2 ^ (S.width + 1) = 2 ^ (finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) + 1) := by
    rw [h1, pow_succ]
    ring
  have := Nat.pow_right_injective le_rfl h2
  omega

theorem finrank_clSub_inf_Vt_le (X : Hyp10 S g t) :
    finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t) ≤ 3 := by
  obtain ⟨k, hk, hβ, -⟩ := X.exists_pair
  have hb : (orbV X.haQ X.ht hk : S.Qt) ∉ S.clSub (S.QG ⊓ S.Qa g) := by
    rw [← beta_aV_eq_zero_iff X.H X.C X.ht X.ht1 X.hVQ, hβ]
    exact one_ne_zero
  have hlt : S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t < Vt S g t := by
    refine lt_of_le_of_ne inf_le_right fun h => hb ?_
    have : (orbV X.haQ X.ht hk : S.Qt) ∈ S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t := by
      rw [h]
      exact (orbV X.haQ X.ht hk).2
    exact this.1
  have := Submodule.finrank_lt_finrank_of_lt hlt
  rw [X.h4] at this
  omega

theorem finrank_commSpace_le_six (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) {y : S.O}
    (hy : y ∈ S.Lbar g ⊓ Nbar S g t) :
    finrank (ZMod 2) (commSpace (y : S.Qt ≃ₗ[ZMod 2] S.Qt)) ≤ 6 := by
  obtain ⟨k, hk, -, hb⟩ := X.exists_pair
  obtain ⟨-, -, hdim, -, hN⟩ := timmesfeld_10_1_two hCE X hk hb
  have hU : (Wt S g t ⊔ S.clSub (S.QG ⊓ S.Qa g)).map
      (((y : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1) ≤
      S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t := by
    rw [Submodule.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      refine ⟨?_, hN y hy.2 w hw⟩
      obtain ⟨x, hxQ, rfl⟩ := S.exists_cl w
      have hxa : x * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * x := by
        rw [← S.polar_cl_eq_zero_iff hxQ X.haQ, polar_comm]
        exact (mem_Wt.mp hw) _ (cl_a_mem_Vt X.ht)
      exact X.C.comm_le x ⟨hxQ, mem_centralizer_singleton_iff.mpr hxa⟩ y hy.1
    · rintro _ ⟨p, hp, rfl⟩
      have hspan : (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) ≤ S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t :=
        (Submodule.span_singleton_le_iff_mem _ _).mpr
          ⟨cl_mem_clSub_self X.haQ, cl_a_mem_Vt X.ht⟩
      exact hspan (Lbar_apply_sub_mem_span' X.haQ hp hy.1)
  have hn := S.finrank_Qt_eq_two_mul_width
  have hW := finrank_Wt (S := S) (g := g) (t := t)
  rw [X.h4] at hW
  have hPdim := finrank_clSub_Qa X
  have hVa := finrank_clSub_inf_Vt_le X
  have h5 := X.five_le_width
  have hPa : finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) + 1 ≤ S.width := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq
      (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) (Vt S g t)
    rw [hdim, X.h4] at h1
    have h2 : (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊓ Vt S g t ≤
        S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t := fun v hv => ⟨hv.1.1, hv.2⟩
    have := Submodule.finrank_mono h2
    omega
  have hU1 : 2 * S.width ≤ finrank (ZMod 2) ↥(Wt S g t ⊔ S.clSub (S.QG ⊓ S.Qa g)) + 3 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Wt S g t) (S.clSub (S.QG ⊓ S.Qa g))
    rw [inf_comm (Wt S g t)] at h1
    omega
  have h3 := finrank_range_le_map_add
    (((y : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1)
    (Wt S g t ⊔ S.clSub (S.QG ⊓ S.Qa g))
  have h4 := Submodule.finrank_mono hU
  change finrank (ZMod 2) (LinearMap.range
    (((y : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1)) ≤ 6
  omega

theorem width_le_finrank_Wstar (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) (F : Frame X)
    {x : S.O} (hxL : x ∈ S.Lbar g) (hπ : F.π ⟨x, Lbar_le_Rbar X.ht hxL⟩ = τ₁ * τ₂) :
    S.width ≤ finrank (ZMod 2) ↥((Wt S g t).map
      (((x : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1) ⊔ Vt S g t) := by
  have hxR := Lbar_le_Rbar X.ht hxL
  obtain ⟨δ, hδ⟩ := exists_conj_pf_E00
  obtain ⟨r, hr⟩ := F.surj δ
  obtain ⟨h₀, hh₀⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar r.2)
  obtain ⟨m₁, hm₁⟩ := MonoidHom.mem_range.mp (S.Lbar_le_Mbar g hxL)
  obtain ⟨m, hm⟩ : ∃ m : S.M, m = h₀⁻¹ * m₁ * h₀ := ⟨_, rfl⟩
  have hρm : S.ρ m = (r : S.O)⁻¹ * x * r := by
    rw [hm, map_mul, map_mul, map_inv, hh₀, hm₁]
  have hmR : S.ρ m ∈ Rbar S g t := by
    rw [hρm]
    exact mul_mem (mul_mem (inv_mem r.2) hxR) r.2
  have hπm : F.π ⟨S.ρ m, hmR⟩ = δ⁻¹ * (τ₁ * τ₂) * δ := by
    have e : (⟨S.ρ m, hmR⟩ : Rbar S g t) = r⁻¹ * ⟨x, hxR⟩ * r := Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hρm)
    rw [e, map_mul, map_mul, map_inv, hπ, hr]
  have hβ : beta X.H X.C X.ht X.ht1 X.hVQ (aV X.ht) (orbV X.haQ X.ht hmR) = 1 := by
    rw [orbV_eq_resV X, F.beta_eq, F.compat, F.base, hπm]
    exact hδ
  have hb := not_mem_Qa_of_beta X hmR hβ
  obtain ⟨-, hint, hdim, hdim', -⟩ := timmesfeld_10_1_two hCE X hmR hb
  have hUU' : ((S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊔ Vt S g t).map
      (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) ≤
      (S.clSub (S.QG ⊓ S.Qa ((m : G) * g)) ⊓ Wt S g t) ⊔ Vt S g t := by
    rw [Submodule.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨p, hp, rfl⟩
      exact ⟨apply_mem_clSub_Qa_mul m hp.1, apply_mem_Wt X.H hmR hp.2⟩
    · rintro _ ⟨v, hv, rfl⟩
      exact apply_mem_Vt_of_mem_Rbar X.haQ hmR hv
  have hsw := finrank_swap ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) hUU' hint
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq
    ((S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊔ Vt S g t)
    ((S.clSub (S.QG ⊓ S.Qa ((m : G) * g)) ⊓ Wt S g t) ⊔ Vt S g t)
  rw [hint, X.h4, hdim, hdim'] at hsup
  rw [X.h4, hdim'] at hsw
  have hUW : (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊔ Vt S g t ≤ Wt S g t :=
    sup_le inf_le_right (Vt_le_Wt X.H X.ht1)
  have hrm : ∀ v, (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := fun v => by
    rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← Subgroup.coe_mul, ← Subgroup.coe_mul,
      hρm]
    congr 2
    group
  have hle : (((S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊔ Vt S g t).map
      ((((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1) ⊔ Vt S g t).map
      (((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) ≤
      (Wt S g t).map (((x : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1) ⊔ Vt S g t := by
    rw [Submodule.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨(r : S.Qt ≃ₗ[ZMod 2] S.Qt) w, apply_mem_Wt X.H r.2 (hUW hw), ?_⟩
      simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, map_sub, hrm]
    · rintro _ ⟨v, hv, rfl⟩
      exact apply_mem_Vt_of_mem_Rbar X.haQ r.2 hv
  have h1 := Submodule.finrank_mono hle
  rw [LinearEquiv.finrank_map_eq] at h1
  omega

theorem width_le_finrank_commSpace (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) (F : Frame X)
    {x : S.O} (hxL : x ∈ S.Lbar g) (hπ : F.π ⟨x, Lbar_le_Rbar X.ht hxL⟩ = τ₁ * τ₂) :
    S.width ≤ finrank (ZMod 2) (commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  have hxR := Lbar_le_Rbar X.ht hxL
  have hxN : x ∉ Nbar S g t := fun h => by
    have := (F.ker ⟨x, hxR⟩).mpr h
    rw [hπ] at this
    exact τ₁τ₂_ne_one this
  have hflag := flag_Hyp10 X hxR
  rw [finrank_map_Vt_of_Lbar X hxL hxN] at hflag
  have := width_le_finrank_Wstar hCE X F hxL hπ
  omega

end CFSG.LargeExtraspecial.S10
