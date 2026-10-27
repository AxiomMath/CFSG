module

public import CFSG.GF2Type.Smith1980Orth.S3GoodStep

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S14 CFSG.RankThree.OrthogonalInvolutions
  CFSG.Open
open CFSG.ClassicalGroups.Orthogonal (eichler HypPair)
open TauCeti.QuadraticMap (orthogonalGroup)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

private instance instFiniteDimensionalVtGoodType (g : G) (t : S.O) :
    FiniteDimensional (ZMod 2) (Vt S g t) :=
  Module.Finite.of_finite

namespace S2Data

namespace Rebase

variable {D : S2Data S} (T : Rebase D)

@[expose] noncomputable def psiV (hw6 : 6 ≤ S.width) (τ : T.P.perp) :
    Vt S D.g D.t ≃ₗ[ZMod 2] Vt S D.g D.t :=
  D.resC ⟨T.psi τ, T.psi_mem_Cbar hw6 τ⟩

theorem psiV_mul (hw6 : 6 ≤ S.width) (τ τ' : T.P.perp) :
    T.psiV hw6 (τ + τ') = T.psiV hw6 τ * T.psiV hw6 τ' := by
  unfold psiV
  rw [← map_mul]
  congr 1
  exact Subtype.ext (T.psi_mul τ τ')

theorem psiV_mem_pointRadical (hw6 : 6 ≤ S.width) (τ : T.P.perp) :
    T.psiV hw6 τ ∈ pointRadical D.QV T.P.e := by
  have h : T.psiV hw6 τ ∈ LmodN S D.g D.t := by
    rw [← D.range_resLC]
    exact ⟨⟨T.psi τ, T.psi_mem_Lbar τ, T.psi_mem_Cbar hw6 τ⟩, rfl⟩
  rw [T.hP]
  rwa [D.LmodN_eq_pointRadical] at h

theorem exists_eichler_psiV (hw6 : 6 ≤ S.width) (τ : T.P.perp) :
    ∃ u : Vt S D.g D.t, polar D.QV T.P.e u = 0 ∧ T.psiV hw6 τ = eichler D.QV T.P.e u := by
  obtain ⟨u, hu, hv⟩ := D.exists_eichler_of_mem_Lbar_inf_Cbar D.QV_nondegenerate D.QV_aV
    D.LmodN_eq_pointRadical (c := T.psi τ) ⟨T.psi_mem_Lbar τ, T.psi_mem_Cbar hw6 τ⟩
  refine ⟨u, by rw [T.hP]; exact hu, ?_⟩
  rw [T.hP]
  exact LinearEquiv.ext fun v => Subtype.ext (hv v)

@[expose] noncomputable def Theta (hw6 : 6 ≤ S.width) : T.P.perp →ₗ[ZMod 2] T.P.perp :=
  (AddMonoidHom.mk' (fun τ => HypPerp.theta T.P (T.psiV hw6 τ)) (fun a b => by
    rw [T.psiV_mul hw6, HypPerp.theta_mul D.QV_nondegenerate T.P (T.psiV_mem_pointRadical hw6 a)
      (T.psiV_mem_pointRadical hw6 b)])).toZModLinearMap 2

theorem Theta_apply (hw6 : 6 ≤ S.width) (τ : T.P.perp) :
    T.Theta hw6 τ = HypPerp.theta T.P (T.psiV hw6 τ) := rfl

theorem QV_Theta_eichler (hw6 : 6 ≤ S.width) (p q : T.P.perp)
    (hp : D.QV (p : Vt S D.g D.t) = 0)
    (hpq : polar D.QV (p : Vt S D.g D.t) (q : Vt S D.g D.t) = 0) (τ : T.P.perp) :
    D.QV ((T.Theta hw6 (eichler (D.QV.restrict T.P.perp) p q τ) : T.P.perp) : Vt S D.g D.t) =
      D.QV ((T.Theta hw6 τ : T.P.perp) : Vt S D.g D.t) := by
  obtain ⟨n, hn, -⟩ := T.exists_lift_data p q hp hpq
  obtain ⟨c'', hc''s, hconj⟩ := T.Psi_conj_Cbar n (T.psi_mem_Cbar hw6 τ)
  have h1 : T.psiV hw6 (eichler (D.QV.restrict T.P.perp) p q τ) =
      D.resC c'' * T.psiV hw6 τ * (D.resC c'')⁻¹ := by
    unfold psiV
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((hn τ).symm.trans hconj)
  have hν : D.resC c'' ∈ orthogonalGroup D.QV :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => D.QV_resC c'' v
  have hνe : (D.resC c'') T.P.e = T.P.e := by
    rw [T.hP]
    exact hc''s
  rw [Theta_apply, Theta_apply, h1]
  exact (HypPerp.theta_conj D.QV_nondegenerate T.P hν hνe (T.psiV_mem_pointRadical hw6 τ)).2

theorem Theta_QV_cases (hw6 : 6 ≤ S.width) :
    (∀ τ : T.P.perp, D.QV ((T.Theta hw6 τ : T.P.perp) : Vt S D.g D.t) = 0) ∨
      (∀ τ : T.P.perp, D.QV ((T.Theta hw6 τ : T.P.perp) : Vt S D.g D.t) =
        D.QV (τ : Vt S D.g D.t)) :=
  HypPerp.perp_invariant_quadraticForm D.QV_nondegenerate T.P (T.three_le_finrank_Z hw6)
    (T.Theta hw6) (fun p q hp hpq τ => T.QV_Theta_eichler hw6 p q hp hpq τ)

theorem psiV_isTypeA (hw6 : 6 ≤ S.width) {τ : T.P.perp} (hτ0 : τ ≠ 0)
    (hτ : D.QV (τ : Vt S D.g D.t) = 0) : IsTypeA D.QV (T.psiV hw6 τ) 2 := by
  obtain ⟨u, hu, hpsi⟩ := T.exists_eichler_psiV hw6 τ
  have hΘ : D.QV ((T.Theta hw6 τ : T.P.perp) : Vt S D.g D.t) = 0 := by
    rcases T.Theta_QV_cases hw6 with h | h
    · exact h τ
    · rw [h τ]
      exact hτ
  have hΘu : T.Theta hw6 τ = HypPerp.projZ T.P u := by
    rw [T.Theta_apply, hpsi]
    exact HypPerp.theta_eichler T.P hu
  have hQu : D.QV u = 0 := by
    rw [← HypPerp.map_projZ T.P hu, ← hΘu]
    exact hΘ
  have hu' : u ∉ (ZMod 2) ∙ T.P.e := by
    intro hmem
    have h1 : eichler D.QV T.P.e u = 1 :=
      (CFSG.LargeExtraspecial.eichler_eq_one_iff D.QV_nondegenerate T.P.e_ne_zero T.P.Q_e hu).mpr
        hmem
    have h2 : D.resC ⟨T.psi τ, T.psi_mem_Cbar hw6 τ⟩ =
        D.resC 1 := by
      rw [map_one]
      show T.psiV hw6 τ = 1
      rw [hpsi, h1]
    have h3 := congrArg Subtype.val (D.resC_injective h2)
    exact hτ0 (T.psi_eq_one h3)
  rw [hpsi]
  exact (CFSG.LargeExtraspecial.eichler_type_of_not_mem_span D.QV_nondegenerate T.P.e_ne_zero
    T.P.Q_e hu hu').2.1 hQu

theorem Psi_eq_of_cl {y : G} (hyQ : y ∈ S.QG) (hy : y ∈ T.H) {u v : Vt S D.g D.t}
    (hcl : S.cl y = D.coord (u, v)) :
    T.Psi ⟨y, hy⟩ = T.Phi (D.coord (polar D.QV u T.P.e • T.P.f, 0)) *
      T.psi (HypPerp.projZ T.P v) := by
  have hperp : S.cl y ∈ T.perp := by
    rw [T.mem_perp, S.polar_cl_eq_zero_iff T.c_mem_QG hyQ]
    exact (T.comm_c_of_mem_H hy).symm
  rw [hcl] at hperp
  rw [← T.Phi_cl hyQ hy, hcl]
  exact T.Phi_coord_eq u v ((T.coord_mem_perp_iff u v).mp hperp)

theorem Psi_eq_psi {y : G} (hyQ : y ∈ S.QG) (hy : y ∈ T.H) {u v : Vt S D.g D.t}
    (hcl : S.cl y = D.coord (u, v)) (hb : polar D.QV u T.P.e = 0) :
    T.Psi ⟨y, hy⟩ = T.psi (HypPerp.projZ T.P v) := by
  rw [T.Psi_eq_of_cl hyQ hy hcl, hb, zero_smul, show D.coord ((0 : Vt S D.g D.t),
    (0 : Vt S D.g D.t)) = 0 by rw [Prod.mk_zero_zero, map_zero], T.Phi_zero, one_mul]

theorem isUInv_Psi (hw6 : 6 ≤ S.width) {y : G} (hyQ : y ∈ S.QG) (hy : y ∈ T.H)
    {u v : Vt S D.g D.t} (hcl : S.cl y = D.coord (u, v)) (hb : polar D.QV u T.P.e = 0)
    (hv0 : HypPerp.projZ T.P v ≠ 0) (hvQ : D.QV v = 0) : D.IsUInv (T.Psi ⟨y, hy⟩) := by
  have hperp : S.cl y ∈ T.perp := by
    rw [T.mem_perp, S.polar_cl_eq_zero_iff T.c_mem_QG hyQ]
    exact (T.comm_c_of_mem_H hy).symm
  rw [hcl] at hperp
  have hv : polar D.QV T.P.e v = 0 := by
    rw [← T.betaV_aV]
    exact (T.coord_mem_perp_iff u v).mp hperp
  have hsing : D.QV (HypPerp.projZ T.P v : Vt S D.g D.t) = 0 := by
    rw [HypPerp.map_projZ T.P hv]
    exact hvQ
  rw [T.Psi_eq_psi hyQ hy hcl hb]
  exact ⟨T.psi_mem_Cbar hw6 _, T.psiV_isTypeA hw6 hv0 hsing⟩

end Rebase

end S2Data

end CFSG.GF2Type.Smith1980Orth
