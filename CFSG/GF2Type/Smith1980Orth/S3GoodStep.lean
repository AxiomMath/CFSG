module

public import CFSG.GF2Type.Smith1980Orth.S3GoodRebase
public import CFSG.GF2Type.Smith1980Orth.S3GoodConj
public import CFSG.GF2Type.Smith1980Orth.S3Count
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LargeExtraspecial.S14SMEPath
public import CFSG.LargeExtraspecial.S14SMHDefs
public import CFSG.LargeExtraspecial.S14SMIDefs
public import CFSG.LargeExtraspecial.S14SMKDelta32
public import CFSG.LargeExtraspecial.S14SMKDivMain
public import CFSG.Sporadic.ThSchreier.Max3Aut

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

private instance instFiniteDimensionalVtGoodStep (g : G) (t : S.O) :
    FiniteDimensional (ZMod 2) (Vt S g t) :=
  Module.Finite.of_finite

namespace S2Data

private theorem Obar_cases_good (D : S2Data S) {s : S.O} (hs : s ∈ D.Obar) :
    s = 1 ∨ s = D.k ∨ s = D.k * D.k := by
  rw [D.Obar_eq_zpowers] at hs
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hs
  have hpow : D.k ^ n = D.k ^ (n % 3) := by simpa using zpow_eq_zpow_emod' n D.k_cube
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h
  · left
    rw [hpow, h, zpow_zero]
  · right
    left
    rw [hpow, h, zpow_one]
  · right
    right
    rw [hpow, h, zpow_two]

namespace Rebase

variable {D : S2Data S} (T : Rebase D)

theorem exists_lift {c' : S.O} (hc' : c' ∈ S.Mbar)
    (hfix : (c' : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl T.c) = S.cl T.c) :
    ∃ n : T.H, S.ρ ⟨n, n.2.1⟩ = c' := by
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hc'
  have hmQ : (m : G) * T.c * (m : G)⁻¹ ∈ S.QG := S.conj_mem_QG m.2 T.c_mem_QG
  have hcl : S.cl T.c = S.cl ((m : G) * T.c * (m : G)⁻¹) := by
    rw [← S.ρ_cl m T.c_mem_QG]
    exact hfix.symm
  rcases (S.cl_eq_cl_iff T.c_mem_QG hmQ).mp hcl with h | h
  · refine ⟨⟨m, T.mem_H_iff.mpr ⟨m.2, ?_⟩⟩, rfl⟩
    calc (m : G) * T.c = ((m : G) * T.c * (m : G)⁻¹) * (m : G) := by group
      _ = T.c * (m : G) := by rw [h]
  · have hczQ : T.c * S.z ∈ S.QG := S.QG.mul_mem T.c_mem_QG S.z_mem_QG
    have hcz1 : T.c * S.z ≠ 1 := by
      intro h1
      apply T.c_ne_z
      calc T.c = T.c * S.z * S.z := by rw [mul_assoc, S.z_mul_z, mul_one]
        _ = S.z := by rw [h1, one_mul]
    have hczz : T.c * S.z ≠ S.z := by
      intro h1
      apply T.c_ne_one
      calc T.c = T.c * S.z * S.z := by rw [mul_assoc, S.z_mul_z, mul_one]
        _ = 1 := by rw [h1, S.z_mul_z]
    obtain ⟨u, huQ, hu⟩ := S.exists_conj_eq_mul_z hczQ hcz1 hczz
    have hu' : u * ((m : G) * T.c * (m : G)⁻¹) * u⁻¹ = T.c := by
      rw [h, hu, mul_assoc, S.z_mul_z, mul_one]
    have hnM : u * (m : G) ∈ S.M := S.M.mul_mem (S.QG_le_M huQ) m.2
    refine ⟨⟨u * m, T.mem_H_iff.mpr ⟨hnM, ?_⟩⟩, ?_⟩
    · calc u * (m : G) * T.c = (u * ((m : G) * T.c * (m : G)⁻¹) * u⁻¹) * (u * (m : G)) := by
            group
        _ = T.c * (u * (m : G)) := by rw [hu']
    · have e : (⟨u * (m : G), hnM⟩ : S.M) = ⟨u, S.QG_le_M huQ⟩ * m := rfl
      rw [e, map_mul, (S.ρ_eq_one_iff ⟨u, S.QG_le_M huQ⟩).mpr huQ, one_mul]

theorem Psi_apply_base (n : T.H) :
    (T.Psi n : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (aV D.good.ht, 0)) =
      D.coord (aV D.good.ht, 0) := by
  rw [← D.cl_base_eq_coord, T.Psi_apply, S.ρ_cl _ D.good.H.conj_mem]
  congr 1
  have hz : (n : G) * S.z * (n : G)⁻¹ = S.z := by
    rw [S.z_comm n.2.1]
    group
  rw [← T.hg₁]
  calc T.g₁ * (n : G) * T.g₁⁻¹ * (T.g₁ * S.z * T.g₁⁻¹) * (T.g₁ * (n : G) * T.g₁⁻¹)⁻¹ =
      T.g₁ * ((n : G) * S.z * (n : G)⁻¹) * T.g₁⁻¹ := by group
    _ = T.g₁ * S.z * T.g₁⁻¹ := by rw [hz]

theorem exists_cbar_of_mem_H (n : T.H) :
    ∃ c'' : D.Cbar,
      D.resC c'' (aV D.good.ht) = aV D.good.ht ∧
        (T.Psi n = c'' ∨ T.Psi n = D.t * c'') := by
  have hfix := T.Psi_apply_base n
  obtain ⟨s, hs, c'', hc'', hsc⟩ := D.exists_mul_Cbar (T.Psi_mem_Mbar n)
  set σ' := D.resC ⟨c'', hc''⟩ (aV D.good.ht) with hσ'
  have hc : ((c'' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (aV D.good.ht, 0)) =
      D.coord (σ', 0) := by
    have := D.Cbar_apply_coord ⟨c'', hc''⟩ (aV D.good.ht) 0
    rwa [map_zero] at this
  have hfix' : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (σ', 0)) = D.coord (aV D.good.ht, 0) := by
    rw [← hc, ← coe_mul_apply, ← hsc]
    exact hfix
  have hne := aV_ne_zero D.good.H D.good.ht
  refine ⟨⟨c'', hc''⟩, ?_, ?_⟩
  · rcases D.mem_Obar_sup_cases hs with hso | rfl | rfl | rfl
    · rcases D.Obar_cases_good hso with rfl | rfl | rfl
      · have h := (Prod.mk.inj (D.coord.injective hfix')).1
        exact h
      · exfalso
        rw [D.k_apply_coord] at hfix'
        exact hne (congrArg Prod.fst (D.coord.injective hfix')).symm
      · exfalso
        rw [coe_mul_apply, D.k_apply_coord, D.k_apply_coord] at hfix'
        have h1 := congrArg Prod.fst (D.coord.injective hfix')
        have h2 := congrArg Prod.snd (D.coord.injective hfix')
        simp only [add_zero, zero_add] at h1 h2
        exact hne (h1.symm.trans h2)
    · rw [D.t_apply_coord, add_zero] at hfix'
      exact (Prod.mk.inj (D.coord.injective hfix')).1
    · exfalso
      rw [coe_mul_apply, D.t_apply_coord, D.k_apply_coord] at hfix'
      exact hne (congrArg Prod.fst (D.coord.injective hfix')).symm
    · exfalso
      rw [pow_two, coe_mul_apply, coe_mul_apply, D.t_apply_coord, D.k_apply_coord,
        D.k_apply_coord] at hfix'
      have h1 := congrArg Prod.fst (D.coord.injective hfix')
      have h2 := congrArg Prod.snd (D.coord.injective hfix')
      simp only [add_zero, zero_add] at h1 h2
      exact hne (h1.symm.trans h2)
  · rcases D.mem_Obar_sup_cases hs with hso | rfl | rfl | rfl
    · rcases D.Obar_cases_good hso with rfl | rfl | rfl
      · left
        rw [hsc, one_mul]
      · exfalso
        rw [D.k_apply_coord] at hfix'
        exact hne (congrArg Prod.fst (D.coord.injective hfix')).symm
      · exfalso
        rw [coe_mul_apply, D.k_apply_coord, D.k_apply_coord] at hfix'
        have h1 := congrArg Prod.fst (D.coord.injective hfix')
        have h2 := congrArg Prod.snd (D.coord.injective hfix')
        simp only [add_zero, zero_add] at h1 h2
        exact hne (h1.symm.trans h2)
    · right
      exact hsc
    · exfalso
      rw [coe_mul_apply, D.t_apply_coord, D.k_apply_coord] at hfix'
      exact hne (congrArg Prod.fst (D.coord.injective hfix')).symm
    · exfalso
      rw [pow_two, coe_mul_apply, coe_mul_apply, D.t_apply_coord, D.k_apply_coord,
        D.k_apply_coord] at hfix'
      have h1 := congrArg Prod.fst (D.coord.injective hfix')
      have h2 := congrArg Prod.snd (D.coord.injective hfix')
      simp only [add_zero, zero_add] at h1 h2
      exact hne (h1.symm.trans h2)

theorem Psi_conj_t (n : T.H) : T.Psi n * D.t * (T.Psi n)⁻¹ = D.t := by
  obtain ⟨c'', -, h | h⟩ := T.exists_cbar_of_mem_H n
  · have hc := D.comm_of_mem_Cbar c''.2
    rw [h]
    calc (c'' : S.O) * D.t * (c'' : S.O)⁻¹ = D.t * (c'' : S.O) * (c'' : S.O)⁻¹ := by rw [hc]
      _ = D.t := by group
  · have hc := D.comm_of_mem_Cbar c''.2
    rw [h]
    calc D.t * (c'' : S.O) * D.t * (D.t * (c'' : S.O))⁻¹ =
        D.t * ((c'' : S.O) * D.t) * (c'' : S.O)⁻¹ * D.t⁻¹ := by group
      _ = D.t * (D.t * (c'' : S.O)) * (c'' : S.O)⁻¹ * D.t⁻¹ := by rw [hc]
      _ = D.t * D.t * D.t⁻¹ := by group
      _ = D.t := by rw [D.t_mul_t, one_mul, D.t_inv_eq]

theorem Psi_conj_Cbar (n : T.H) {x : S.O} (hx : x ∈ D.Cbar) :
    ∃ c'' : D.Cbar,
      D.resC c'' (aV D.good.ht) = aV D.good.ht ∧
        T.Psi n * x * (T.Psi n)⁻¹ = (c'' : S.O) * x * (c'' : S.O)⁻¹ := by
  obtain ⟨c'', hc''s, h | h⟩ := T.exists_cbar_of_mem_H n
  · exact ⟨c'', hc''s, by rw [h]⟩
  · refine ⟨c'', hc''s, ?_⟩
    have hxx : (c'' : S.O) * x * (c'' : S.O)⁻¹ ∈ D.Cbar :=
      mul_mem (mul_mem c''.2 hx) (inv_mem c''.2)
    have hcomm : D.t * ((c'' : S.O) * x * (c'' : S.O)⁻¹) = ((c'' : S.O) * x * (c'' : S.O)⁻¹) * D.t :=
      (D.comm_of_mem_Cbar hxx).symm
    rw [h]
    calc D.t * (c'' : S.O) * x * (D.t * (c'' : S.O))⁻¹ =
        D.t * ((c'' : S.O) * x * (c'' : S.O)⁻¹) * D.t⁻¹ := by group
      _ = (c'' : S.O) * x * (c'' : S.O)⁻¹ := by rw [hcomm]; group

theorem exists_lift_data (p q : T.P.perp) (hp : D.QV (p : Vt S D.g D.t) = 0)
    (hpq : polar D.QV (p : Vt S D.g D.t) (q : Vt S D.g D.t) = 0) :
    ∃ n : T.H,
      (∀ τ : T.P.perp, T.Psi n * T.psi τ * (T.Psi n)⁻¹ =
        T.psi (eichler (D.QV.restrict T.P.perp) p q τ)) ∧
      T.Psi n * T.Phi (D.coord (T.P.f, 0)) * (T.Psi n)⁻¹ = T.Phi (D.coord (T.P.f, 0)) := by
  obtain ⟨c', hc'⟩ := D.exists_Cbar_resC_eq_eichler (p : Vt S D.g D.t) (q : Vt S D.g D.t)
  have hs₀ : eichler D.QV (p : Vt S D.g D.t) (q : Vt S D.g D.t) (aV D.good.ht) =
      aV D.good.ht := by
    have := HypPerp.eichler_apply_e T.P p q
    rwa [T.hP] at this
  have hfix : ((c' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl T.c) = S.cl T.c := by
    rw [T.cl_c, D.Cbar_apply_coord, map_zero, hc', hs₀]
  obtain ⟨n, hn⟩ := T.exists_lift (D.Cbar_le_Mbar c'.2) hfix
  refine ⟨n, fun τ => ?_, ?_⟩
  · have h := (T.Phi_conj n (T.coord_zero_mem_perp τ)).2
    rw [hn, D.Cbar_apply_coord, map_zero, hc'] at h
    unfold psi
    rw [HypPerp.coe_eichler_restrict]
    exact h.symm
  · have hf : D.coord (T.P.f, 0) ∈ T.perp :=
      (T.coord_mem_perp_iff _ _).mpr (by rw [map_zero])
    have h := (T.Phi_conj n hf).2
    rw [hn, D.Cbar_apply_coord, map_zero, hc', HypPerp.eichler_apply_f] at h
    exact h.symm

theorem psi_mem_Cbar (hw6 : 6 ≤ S.width) (τ : T.P.perp) : T.psi τ ∈ D.Cbar := by
  let Z₁ : Submodule (ZMod 2) T.P.perp :=
    { carrier := {τ | T.psi τ ∈ D.Cbar}
      add_mem' := fun {a b} ha hb => by
        show T.psi (a + b) ∈ D.Cbar
        rw [T.psi_mul]
        exact mul_mem ha hb
      zero_mem' := by
        show T.psi 0 ∈ D.Cbar
        rw [T.psi_zero]
        exact one_mem _
      smul_mem' := fun c a ha => by
        rcases OrthoF2.zmod2_eq_zero_or_eq_one c with rfl | rfl
        · rw [zero_smul]
          show T.psi 0 ∈ D.Cbar
          rw [T.psi_zero]
          exact one_mem _
        · rw [one_smul]
          exact ha }
  have hinv : ∀ p q : T.P.perp, D.QV (p : Vt S D.g D.t) = 0 →
      polar D.QV (p : Vt S D.g D.t) (q : Vt S D.g D.t) = 0 →
      ∀ x ∈ Z₁, eichler (D.QV.restrict T.P.perp) p q x ∈ Z₁ := by
    intro p q hp hpq x hx
    obtain ⟨n, hn, -⟩ := T.exists_lift_data p q hp hpq
    show T.psi (eichler (D.QV.restrict T.P.perp) p q x) ∈ D.Cbar
    rw [← hn x]
    exact D.conj_mem_Cbar (T.Psi_mem_Mbar n) hx
  rcases HypPerp.perp_invariant_submodule D.QV_nondegenerate T.P (T.three_le_finrank_Z hw6) Z₁
    hinv with h | h
  · exfalso
    have hfr := T.three_le_finrank_Z hw6
    haveI : Nontrivial T.P.perp := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
    obtain ⟨τ₁, hτ₁⟩ := exists_ne (0 : T.P.perp)
    obtain ⟨τ₂, hτ₂⟩ : ∃ τ₂ : T.P.perp, τ₂ ∉ (ZMod 2) ∙ τ₁ := by
      by_contra hcon
      push Not at hcon
      have htop : (ZMod 2) ∙ τ₁ = ⊤ := eq_top_iff.mpr fun x _ => hcon x
      have h1 := finrank_span_singleton (K := ZMod 2) hτ₁
      rw [htop, finrank_top] at h1
      omega
    have hτ₂0 : τ₂ ≠ 0 := fun h0 => hτ₂ (h0 ▸ Submodule.zero_mem _)
    have hτ₂1 : τ₂ ≠ τ₁ := fun h0 => hτ₂ (h0 ▸ Submodule.mem_span_singleton_self _)
    have hnot : ∀ τ : T.P.perp, τ ≠ 0 → T.psi τ ∉ D.Cbar := by
      intro τ hτ hmem
      have : τ ∈ Z₁ := hmem
      rw [h, Submodule.mem_bot] at this
      exact hτ this
    have hdec : ∀ τ : T.P.perp, τ ≠ 0 → ∃ c ∈ S.Lbar D.g ⊓ D.Cbar,
        T.psi τ = D.t * c := by
      intro τ hτ
      obtain ⟨c, hc, h1 | h1⟩ := D.exists_eq_mul_of_mem_Lbar (T.psi_mem_Lbar τ)
      · exact absurd (h1 ▸ hc.2) (hnot τ hτ)
      · exact ⟨c, hc, h1⟩
    obtain ⟨c₁, hc₁, h₁⟩ := hdec τ₁ hτ₁
    obtain ⟨c₂, hc₂, h₂⟩ := hdec τ₂ hτ₂0
    have hmul : T.psi (τ₁ + τ₂) ∈ D.Cbar := by
      rw [T.psi_mul, h₁, h₂]
      have hc₁t : c₁ * D.t = D.t * c₁ := D.comm_of_mem_Cbar hc₁.2
      have e : D.t * c₁ * (D.t * c₂) = c₁ * c₂ := by
        calc D.t * c₁ * (D.t * c₂) = D.t * (c₁ * D.t) * c₂ := by group
          _ = D.t * (D.t * c₁) * c₂ := by rw [hc₁t]
          _ = (D.t * D.t) * (c₁ * c₂) := by group
          _ = c₁ * c₂ := by rw [D.t_mul_t, one_mul]
      rw [e]
      exact mul_mem hc₁.2 hc₂.2
    have h3 : τ₁ + τ₂ ∈ Z₁ := hmul
    rw [h, Submodule.mem_bot] at h3
    exact hτ₂1 (by rw [eq_neg_of_add_eq_zero_right h3, OrthoF2.vec_neg])
  · have : τ ∈ Z₁ := by
      rw [h]
      exact Submodule.mem_top
    exact this

theorem Phi_coord_eq (u v : Vt S D.g D.t) (hv : D.betaV (aV D.good.ht) v = 0) :
    T.Phi (D.coord (u, v)) =
      T.Phi (D.coord (polar D.QV u T.P.e • T.P.f, 0)) * T.psi (HypPerp.projZ T.P v) := by
  have hv' : polar D.QV T.P.e v = 0 := by rw [← T.betaV_aV]; exact hv
  have hu := HypPerp.eq_add_projZ T.P u
  have hv2 := HypPerp.eq_add_projZ_of_polar_e T.P hv'
  have hsum : D.coord (u, v) =
      D.coord (polar D.QV u T.P.e • T.P.f, 0) + D.coord (0, (HypPerp.projZ T.P v : Vt S D.g D.t)) +
        D.coord (polar D.QV u T.P.f • T.P.e + (HypPerp.projZ T.P u : Vt S D.g D.t),
          polar D.QV v T.P.f • T.P.e) := by
    rw [← map_add, ← map_add]
    congr 1
    have h1 : u = polar D.QV u T.P.e • T.P.f + 0 +
        (polar D.QV u T.P.f • T.P.e + (HypPerp.projZ T.P u : Vt S D.g D.t)) := by
      calc u = polar D.QV u T.P.f • T.P.e + polar D.QV u T.P.e • T.P.f +
            (HypPerp.projZ T.P u : Vt S D.g D.t) := hu
        _ = _ := by abel
    have h2 : v = 0 + (HypPerp.projZ T.P v : Vt S D.g D.t) + polar D.QV v T.P.f • T.P.e := by
      calc v = polar D.QV v T.P.f • T.P.e + (HypPerp.projZ T.P v : Vt S D.g D.t) := hv2
        _ = _ := by abel
    exact Prod.ext h1 h2
  have hw₁ : D.coord (polar D.QV u T.P.e • T.P.f, 0) ∈ T.perp :=
    (T.coord_mem_perp_iff _ _).mpr (by rw [map_zero])
  have hw₂ : D.coord (0, (HypPerp.projZ T.P v : Vt S D.g D.t)) ∈ T.perp :=
    T.coord_zero_mem_perp _
  have hw₃ : D.coord (polar D.QV u T.P.f • T.P.e + (HypPerp.projZ T.P u : Vt S D.g D.t),
      polar D.QV v T.P.f • T.P.e) ∈ T.perp := by
    refine (T.coord_mem_perp_iff _ _).mpr ?_
    rw [T.betaV_aV, polar_smul_right, T.P.polar_ee, smul_zero]
  have hw₃1 : T.Phi (D.coord (polar D.QV u T.P.f • T.P.e + (HypPerp.projZ T.P u : Vt S D.g D.t),
      polar D.QV v T.P.f • T.P.e)) = 1 := by
    rw [T.Phi_eq_one_iff hw₃, T.clSub_eq_Pfst, D.mem_Pfst_iff]
    refine ⟨polar D.QV u T.P.f • T.P.e + (HypPerp.projZ T.P u : Vt S D.g D.t),
      polar D.QV v T.P.f, ?_, ?_⟩
    · rw [T.betaV_aV, polar_add_right, polar_smul_right, T.P.polar_ee, smul_zero, zero_add]
      exact (HypPair.mem_perp.mp (HypPerp.projZ T.P u).2).1
    · rw [T.hP]
  rw [hsum, T.Phi_mul (add_mem hw₁ hw₂) hw₃, T.Phi_mul hw₁ hw₂, hw₃1, mul_one]
  rfl

theorem Phi_f_eq_t (hw6 : 6 ≤ S.width) : T.Phi (D.coord (T.P.f, 0)) = D.t := by
  obtain ⟨w, hw, hwt⟩ := T.exists_Phi_eq D.good.ht
  obtain ⟨⟨u, v⟩, rfl⟩ := D.coord.surjective w
  have hv : D.betaV (aV D.good.ht) v = 0 := (T.coord_mem_perp_iff u v).mp hw
  have key := T.Phi_coord_eq u v hv
  rw [hwt] at key
  set τ₀ := HypPerp.projZ T.P v with hτ₀
  have hb : polar D.QV u T.P.e = 1 := by
    rcases OrthoF2.zmod2_eq_zero_or_eq_one (polar D.QV u T.P.e) with h0 | h1
    · exfalso
      rw [h0, zero_smul, show D.coord ((0 : Vt S D.g D.t), (0 : Vt S D.g D.t)) = 0 by
        rw [Prod.mk_zero_zero, map_zero], T.Phi_zero, one_mul] at key
      exact D.t_notMem_Cbar (key ▸ T.psi_mem_Cbar hw6 τ₀)
    · exact h1
  rw [hb, one_smul] at key
  have hτ₀0 : τ₀ = 0 := by
    refine HypPerp.perp_fixed_eq_zero D.QV_nondegenerate T.P (T.three_le_finrank_Z hw6) τ₀
      (fun p q hp hpq => ?_)
    obtain ⟨n, hn1, hn2⟩ := T.exists_lift_data p q hp hpq
    have h1 : T.psi (eichler (D.QV.restrict T.P.perp) p q τ₀) = T.psi τ₀ := by
      have e1 : T.Psi n * (T.Phi (D.coord (T.P.f, 0)) * T.psi τ₀) * (T.Psi n)⁻¹ = D.t := by
        rw [← key]
        exact T.Psi_conj_t n
      have e2 : T.Psi n * (T.Phi (D.coord (T.P.f, 0)) * T.psi τ₀) * (T.Psi n)⁻¹ =
          (T.Psi n * T.Phi (D.coord (T.P.f, 0)) * (T.Psi n)⁻¹) *
            (T.Psi n * T.psi τ₀ * (T.Psi n)⁻¹) := by group
      rw [e2, hn2, hn1 τ₀] at e1
      exact mul_left_cancel (e1.trans key)
    have h2 := T.psi_injective h1
    have h3 := congrArg Subtype.val h2
    rw [HypPerp.coe_eichler_restrict] at h3
    exact h3
  rw [hτ₀0, T.psi_zero, mul_one] at key
  exact key.symm

end Rebase

end S2Data

end CFSG.GF2Type.Smith1980Orth
