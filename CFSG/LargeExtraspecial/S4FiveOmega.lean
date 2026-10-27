module

public import CFSG.LargeExtraspecial.S4FiveConj
public import CFSG.LargeExtraspecial.S4OmegaTau
public import CFSG.LargeExtraspecial.S2OrthGen
public import CFSG.LargeExtraspecial.S4FiveApp
public import CFSG.LargeExtraspecial.S4FiveRad

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.OrthoF2
open CFSG.ClassicalGroups.Orthogonal (eichler)

theorem omegaGroup_le_closure_pointRadical {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] {q : QuadraticForm (ZMod 2) U}
    (hq : q.polarBilin.Nondegenerate) {m : ℕ} (hm : 2 ≤ m) (hdim : finrank (ZMod 2) U = 2 * m) :
    omegaGroup q hq ≤ closure {t | ∃ p : U, p ≠ 0 ∧ q p = 0 ∧ t ∈ pointRadical q p} := by
  have h := S2.omegaFix_le_radGen hq m ⊥ hm (bot_inf_eq _)
    (by rw [S2.perp_bot, finrank_top]; exact hdim)
  rw [S2.omegaFix_bot] at h
  refine h.trans (closure_mono ?_)
  rintro x ⟨p, -, hp0, hp, hx⟩
  exact ⟨p, hp0, hp, by rwa [S2.radFix_bot] at hx⟩

section Abstract

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] {q : QuadraticForm (ZMod 2) U}

theorem conj_mem_pointRadical {x w : U ≃ₗ[ZMod 2] U}
    (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup q) {p : U} (hw : w ∈ pointRadical q p) :
    x * w * x⁻¹ ∈ pointRadical q (x p) := by
  have e1 : ∀ v y, polar q (x⁻¹ v) y = polar q v (x y) := fun v y => by
    rw [← TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hx (x⁻¹ v) y,
      show x (x⁻¹ v) = v from x.apply_symm_apply v]
  obtain ⟨hw1, hw2, hw3, hw4⟩ := hw
  refine ⟨mul_mem (mul_mem hx hw1) (inv_mem hx), ?_, fun y hy => ?_, fun v => ?_⟩
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, show x⁻¹ (x p) = p from x.symm_apply_apply p,
      hw2]
  · have hy' : polar q p (x⁻¹ y) = 0 := by
      rw [polar_comm, e1, polar_comm, hy]
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp (hw3 _ hy')
    rw [Submodule.mem_span_singleton]
    refine ⟨k, ?_⟩
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      show w (x⁻¹ y) = x⁻¹ y + k • p by rw [hk]; abel, map_add, map_smul,
      show x (x⁻¹ y) = y from x.apply_symm_apply y]
    abel
  · have h := hw4 (x⁻¹ v)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    have e2 : x (w (x⁻¹ v)) - v = x (w (x⁻¹ v) - x⁻¹ v) := by
      rw [map_sub, show x (x⁻¹ v) = v from x.apply_symm_apply v]
    rw [e2, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hx, h]

variable [FiniteDimensional (ZMod 2) U]

theorem pointRadical_le_omegaGroup (hq : q.polarBilin.Nondegenerate) {p : U} (hp0 : p ≠ 0)
    (hp : q p = 0) : pointRadical q p ≤ omegaGroup q hq := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  obtain ⟨w, hpw, rfl⟩ := (mem_pointRadical_iff hq hp0 hp).mp hx
  by_cases hw : w ∈ (ZMod 2) ∙ p
  · rw [(eichler_eq_one_iff hq hp0 hp hpw).mpr hw, commSpace_one, finrank_bot]
    exact ⟨0, rfl⟩
  · rw [(eichler_type_of_not_mem_span hq hp0 hp hpw hw).1]
    have hli : LinearIndependent (ZMod 2) ![p, w] :=
      linearIndependent_pair_iff.mpr ⟨hp0, fun h => hw (h ▸ Submodule.zero_mem _),
        fun h => hw (h ▸ Submodule.mem_span_singleton_self p)⟩
    rw [finrank_span_pair hli]
    exact even_two

end Abstract

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g)
include H C ht ht1 hVQ

theorem radConfig (hNo : NoA2 S g)
    (hntr : ∃ v : Vt S g t, v ≠ 0 ∧ v ∉ orbitOf (RmodN S g t) (aV ht)) :
    RadConfig (beta H C ht ht1 hVQ) (RmodN S g t) (aV ht) (LmodN S g t) where
  alt := beta_isAlt H C ht ht1 hVQ
  nondeg := beta_nondegenerate H C ht ht1 hVQ
  le_sp := RmodN_le_isometryGroup H C ht ht1 hVQ
  ne_zero := aV_ne_zero H ht
  span_eq := span_orbitOf_RmodN H ht
  le_X := LmodN_le_RmodN ht
  le_U := LmodN_le_spPointRadical H C ht ht1 hVQ
  card_le := card_spPointRadical_le_two_mul H C ht ht1 hVQ
  tau_not_mem := spTransvection_not_mem_of_not_transitive (beta_isAlt H C ht ht1 hVQ)
    (beta_nondegenerate H C ht ht1 hVQ) (four_le_finrank_Vt H C ht ht1 hVQ hNo)
    (RmodN_le_isometryGroup H C ht ht1 hVQ) (aV_ne_zero H ht) (span_orbitOf_RmodN H ht)
    (LmodN_le_RmodN ht) (LmodN_le_spPointRadical H C ht ht1 hVQ)
    (card_spPointRadical_le_two_mul H C ht ht1 hVQ) hntr

theorem bV_mem_orbitOf (hNo : NoA2 S g)
    (hntr : ∃ v : Vt S g t, v ≠ 0 ∧ v ∉ orbitOf (RmodN S g t) (aV ht)) {h : S.M}
    (hth : t ∈ S.Lbar ((h : G) * g)) : bV hth ∈ orbitOf (RmodN S g t) (aV ht) := by
  have : Finite (Vt S g t ≃ₗ[ZMod 2] Vt S g t) := finite_linearEquiv_of_finite
  set RC := radConfig H C ht ht1 hVQ hNo hntr with hRC
  by_contra hb
  have hQb : RC.qOrbitForm hntr (bV hth) = 1 := by
    rw [RadConfig.qOrbitForm_apply, RadConfig.qOrbit_eq_one_iff]
    rintro (h0 | h0)
    · exact bV_ne_zero H hth h0
    · exact hb h0
  have hle : LhmodN S g t h ≤ spPointRadical (beta H C ht ht1 hVQ) (bV hth) ⊓
      TauCeti.QuadraticMap.orthogonalGroup (RC.qOrbitForm hntr) := fun e he =>
    ⟨LhmodN_le_spPointRadical H C ht ht1 hVQ hth he,
      RC.mem_orthogonalGroup_of_mem hntr (LhmodN_le_RmodN hth he)⟩
  have h1 := (card_le_of_le hle).trans (card_spPointRadical_inf_le_two (beta_isAlt H C ht ht1 hVQ)
    (beta_nondegenerate H C ht ht1 hVQ) (RC.polar_qOrbitForm hntr) hQb)
  have h2 := card_LhmodN_ge H C ht ht1 hVQ hth
  have h4 := four_le_finrank_Vt H C ht ht1 hVQ hNo
  have h3 : 4 ≤ 2 ^ (finrank (ZMod 2) (Vt S g t) - 2) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (finrank (ZMod 2) (Vt S g t) - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem RmodN_eq_omegaGroup (hNo : NoA2 S g)
    (hntr : ∃ v : Vt S g t, v ≠ 0 ∧ v ∉ orbitOf (RmodN S g t) (aV ht)) :
    RmodN S g t = omegaGroup ((radConfig H C ht ht1 hVQ hNo hntr).qOrbitForm hntr)
      ((radConfig H C ht ht1 hVQ hNo hntr).qOrbitForm_nondegenerate hntr) := by
  set RC := radConfig H C ht ht1 hVQ hNo hntr with hRC
  set Q := RC.qOrbitForm hntr with hQdef
  have hE := RC.E_eq_pointRadical hntr
  have hQa : Q (aV ht) = 0 := by
    rw [hQdef, RadConfig.qOrbitForm_apply, RadConfig.qOrbit_eq_zero_iff]
    exact Or.inr ⟨1, one_mem _, rfl⟩
  apply le_antisymm
  · refine (RmodN_le_closure_conj H ht fun _ hth =>
      bV_mem_orbitOf H C ht ht1 hVQ hNo hntr hth).trans ((closure_le _).mpr ?_)
    rintro _ ⟨x, hx, e, he, rfl⟩
    have hxO := RC.mem_orthogonalGroup_of_mem hntr hx
    have hmem := conj_mem_pointRadical hxO (hE ▸ he)
    refine pointRadical_le_omegaGroup _ (fun h0 => aV_ne_zero H ht (x.map_eq_zero_iff.mp h0)) ?_
      hmem
    rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hxO, hQa]
  · obtain ⟨k, hk⟩ := even_finrank_Vt H C ht ht1 hVQ
    have h4 := four_le_finrank_Vt H C ht ht1 hVQ hNo
    refine (omegaGroup_le_closure_pointRadical (RC.qOrbitForm_nondegenerate hntr)
      (m := k) (by omega) (by omega)).trans ((closure_le _).mpr ?_)
    rintro w ⟨p, hp0, hp, hw⟩
    have hpT : p ∈ orbitOf (RmodN S g t) (aV ht) := by
      rw [RadConfig.qOrbitForm_apply, RadConfig.qOrbit_eq_zero_iff] at hp
      exact hp.resolve_left hp0
    obtain ⟨x, hx, rfl⟩ := hpT
    have hxO := RC.mem_orthogonalGroup_of_mem hntr hx
    have h1 := conj_mem_pointRadical (inv_mem hxO) hw
    rw [show x⁻¹ (x (aV ht)) = aV ht from x.symm_apply_apply _, ← hE] at h1
    have h2 := mul_mem (mul_mem hx (LmodN_le_RmodN ht h1)) (inv_mem hx)
    rwa [show x * (x⁻¹ * w * x⁻¹⁻¹) * x⁻¹ = w by group] at h2

end CFSG.LargeExtraspecial.S4
