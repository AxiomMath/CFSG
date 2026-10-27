module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.E6FixP1Gen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverFixInduced
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BabyP3Core
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.CoverUniqueOuter
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.CoverUnique
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.IndexTwo
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.NativeFacts
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.InvolutionsN1
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.Monster.B.TwoA.Amalgam CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Overlap CFSG.EvenSmallLie.TwoE6
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

@[expose] noncomputable def e6fix_epsE :
    ↥(commutator ↥Eam) ⧸ center ↥(commutator ↥Eam) ≃* ↥stdGroup :=
  (derived_Eam_facts.2.2.2).some

noncomputable abbrev e6fix_pi : ↥(commutator ↥Eam) →* ↥stdGroup := quotCover e6fix_epsE

theorem e6fix_pi_surjective : Function.Surjective e6fix_pi :=
  e6fix_epsE.surjective.comp (QuotientGroup.mk'_surjective _)

theorem e6fix_ker_pi : e6fix_pi.ker = center ↥(commutator ↥Eam) := ker_quotCover _

theorem finite_stdGroup' : Finite ↥stdGroup :=
  have := derived_Eam_facts.2.1
  Finite.of_surjective e6fix_pi e6fix_pi_surjective

@[expose] noncomputable def e6fix_rho : ↥Eam →* MulAut ↥stdGroup :=
  (autCover e6fix_epsE).comp MulAut.conjNormal

theorem e6fix_pi_conj (y : ↥Eam) (e : ↥(commutator ↥Eam)) :
    e6fix_pi (MulAut.conjNormal y e) = e6fix_rho y (e6fix_pi e) :=
  quotCover_autCover e6fix_epsE (MulAut.conjNormal y) e

theorem e6fix_rho_coe (t : ↥(commutator ↥Eam)) :
    e6fix_rho (t : ↥Eam) = MulAut.conj (e6fix_pi t) :=
  (congrArg (autCover e6fix_epsE)
    (MulAut.conjNormal_val (H := commutator ↥Eam) (h := t))).trans (autCover_conj e6fix_epsE t)

theorem e6fix_mem_zpowers_of_rho_eq_one {y : ↥Eam} (h : e6fix_rho y = 1) :
    y ∈ zpowers cE' := by
  have hperf : Group.IsPerfect ↥(commutator ↥Eam) := derived_Eam_facts.1
  have hconj : (MulAut.conjNormal y : MulAut ↥(commutator ↥Eam)) = 1 := by
    refine CoverFix.eq_one_of_induced_eq_one hperf e6fix_pi e6fix_ker_pi.le fun e => ?_
    rw [e6fix_pi_conj, h]
    rfl
  have hcent : y ∈ centralizer ((commutator ↥Eam : Subgroup ↥Eam) : Set ↥Eam) := by
    rw [mem_centralizer_iff]
    intro e he
    have h1 := congrArg
      (fun f : MulAut ↥(commutator ↥Eam) => ((f ⟨e, he⟩ : ↥(commutator ↥Eam)) : ↥Eam)) hconj
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc e * y = (y * e * y⁻¹) * y := by rw [h1]
      _ = y * e := by group
  rw [centralizer_commutator_Eam] at hcent
  exact hcent

theorem e6fix_mul_self_eq_one {y : ↥Eam} (h : e6fix_rho y * e6fix_rho y = 1) : y * y = 1 := by
  have h1 : e6fix_rho (y * y) = 1 := by
    rw [map_mul]
    exact h
  rcases eq_one_or_eq_of_mem_zpowers_mul_self bFix_cE'_mul_cE'
    (e6fix_mem_zpowers_of_rho_eq_one h1) with h3 | h3
  · exact h3
  · exact absurd h3 (mul_self_ne_cE' y)

theorem e6fix_mem_commutator_of_rho_mem_inner {y : ↥Eam} (h : e6fix_rho y ∈ inner ↥stdGroup) :
    y ∈ commutator ↥Eam := by
  obtain ⟨gb, hg⟩ := h
  obtain ⟨t, rfl⟩ := e6fix_pi_surjective gb
  have h1 : e6fix_rho (y * ((t : ↥Eam))⁻¹) = 1 := by
    rw [map_mul, map_inv, e6fix_rho_coe, hg]
    exact mul_inv_cancel _
  have h2 := e6fix_mem_zpowers_of_rho_eq_one h1
  have hc : cE' ∈ commutator ↥Eam := CFSG.Monster.B.TwoA.Amalgam.cE'_mem_commutator
  have h3 : y * ((t : ↥Eam))⁻¹ ∈ commutator ↥Eam := (zpowers_le.2 hc) h2
  have h4 := mul_mem h3 t.2
  rwa [inv_mul_cancel_right] at h4

theorem e6fix_two_subgroup_card_le (T : Subgroup (Outer ↥stdGroup)) (hT : IsPGroup 2 T) :
    Nat.card T ≤ 2 := by
  obtain ⟨Θ, hΘ⟩ := exists_outer_hom
  have hfin : Finite (RingAut K) :=
    Nat.finite_of_card_ne_zero (by rw [natCard_ringAut_K]; norm_num)
  have hinj : Function.Injective (Θ.comp T.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨u, hu⟩ := hΘ (show (x : Outer ↥stdGroup) ∈ Θ.ker from hx)
    have h3' : diagOut u ^ 3 = 1 := by
      rw [← map_pow, diagParam_pow_three, map_one]
    have h3 : (x : Outer ↥stdGroup) ^ 3 = 1 := by
      rw [← hu]
      exact h3'
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 hT) x
    have hj' : orderOf (x : Outer ↥stdGroup) = 2 ^ j := by
      rw [← Subgroup.orderOf_coe] at hj
      exact hj
    have hdvd : 2 ^ j ∣ 3 := hj' ▸ orderOf_dvd_of_pow_eq_one h3
    have hj0 : j = 0 := by
      by_contra hne
      have : 2 ∣ 3 := (dvd_pow_self 2 hne).trans hdvd
      omega
    have hx1 : (x : Outer ↥stdGroup) = 1 := by
      rw [← orderOf_eq_one_iff, hj', hj0]
      rfl
    exact Subtype.ext hx1
  calc Nat.card T ≤ Nat.card (RingAut K) := Nat.card_le_card_of_injective _ hinj
    _ = 2 := natCard_ringAut_K

theorem e6fix_exists_conj_rho (β₀ : MulAut ↥stdGroup) (h2 : β₀ * β₀ = 1) :
    ∃ (a : MulAut ↥stdGroup) (y : ↥Eam), y * y = 1 ∧ a * β₀ * a⁻¹ = e6fix_rho y := by
  have := finite_stdGroup'
  have hfinA : Finite (MulAut ↥stdGroup) :=
    Finite.of_injective (fun f : MulAut ↥stdGroup => (f : ↥stdGroup → ↥stdGroup))
      DFunLike.coe_injective
  by_cases hin : β₀ ∈ inner ↥stdGroup
  · obtain ⟨gb, hg⟩ := hin
    obtain ⟨t, rfl⟩ := e6fix_pi_surjective gb
    have hρ : e6fix_rho (t : ↥Eam) = β₀ := by rw [e6fix_rho_coe, hg]
    refine ⟨1, (t : ↥Eam), e6fix_mul_self_eq_one (by rw [hρ]; exact h2), ?_⟩
    rw [hρ]
    group
  · obtain ⟨y0, hy0, hy02⟩ := exists_mul_self_eq_one_not_mem_commutator
    have hρy0 : e6fix_rho y0 ∉ inner ↥stdGroup := fun h =>
      hy0 (e6fix_mem_commutator_of_rho_mem_inner h)
    have hout : ∀ T : Subgroup (Outer ↥stdGroup), IsPGroup 2 T → Nat.card T ≤ 2 :=
      e6fix_two_subgroup_card_le
    have hβ1 : (QuotientGroup.mk β₀ : Outer ↥stdGroup) ≠ 1 := fun h =>
      hin ((QuotientGroup.eq_one_iff β₀).1 h)
    have hβ2 : (QuotientGroup.mk β₀ : Outer ↥stdGroup) * QuotientGroup.mk β₀ = 1 := by
      rw [← QuotientGroup.mk_mul, h2]
      rfl
    have hρ1 : (QuotientGroup.mk (e6fix_rho y0) : Outer ↥stdGroup) ≠ 1 := fun h =>
      hρy0 ((QuotientGroup.eq_one_iff _).1 h)
    have hρ2 : (QuotientGroup.mk (e6fix_rho y0) : Outer ↥stdGroup) *
        QuotientGroup.mk (e6fix_rho y0) = 1 := by
      rw [← QuotientGroup.mk_mul, ← map_mul, hy02, map_one]
      rfl
    obtain ⟨gb, hgb⟩ := e6fix_exists_conj_of_two_bound hout hβ2 hρ2 hβ1 hρ1
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective gb
    have hmk : (QuotientGroup.mk (a * β₀ * a⁻¹) : Outer ↥stdGroup) =
        QuotientGroup.mk (e6fix_rho y0) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      exact hgb
    obtain ⟨gb', hg'⟩ :
        (a * β₀ * a⁻¹)⁻¹ * e6fix_rho y0 ∈ inner ↥stdGroup := QuotientGroup.eq.1 hmk
    obtain ⟨t, rfl⟩ := e6fix_pi_surjective gb'
    have hρt : e6fix_rho (t : ↥Eam) = (a * β₀ * a⁻¹)⁻¹ * e6fix_rho y0 := by
      rw [e6fix_rho_coe, hg']
    have hw : a * β₀ * a⁻¹ = e6fix_rho (y0 * (t : ↥Eam)⁻¹) := by
      rw [map_mul, map_inv, hρt]
      group
    have hsq : e6fix_rho (y0 * (t : ↥Eam)⁻¹) * e6fix_rho (y0 * (t : ↥Eam)⁻¹) = 1 := by
      rw [← hw]
      calc a * β₀ * a⁻¹ * (a * β₀ * a⁻¹) = a * (β₀ * β₀) * a⁻¹ := by group
        _ = 1 := by rw [h2]; group
    exact ⟨a, y0 * (t : ↥Eam)⁻¹, e6fix_mul_self_eq_one hsq, hw⟩

theorem e6fix_exists_conj_rho' (β₀ : MulAut ↥stdGroup) (h2 : β₀ * β₀ = 1) :
    ∃ (a : MulAut ↥stdGroup) (y : ↥Eam), y * y = 1 ∧ a * β₀ * a⁻¹ = e6fix_rho y ∧
      (y ∈ NE ∨ y ∉ commutator ↥Eam) := by
  obtain ⟨a, y, hyy, hay⟩ := e6fix_exists_conj_rho β₀ h2
  by_cases hy : y ∈ commutator ↥Eam
  · obtain ⟨h, hh⟩ := involutionsIntoN1 ⟨y, hy⟩ (Subtype.ext hyy)
    refine ⟨e6fix_rho h * a, h * y * h⁻¹, ?_, ?_, Or.inl hh⟩
    · calc h * y * h⁻¹ * (h * y * h⁻¹) = h * (y * y) * h⁻¹ := by group
        _ = 1 := by rw [hyy]; group
    · rw [map_mul, map_mul, map_inv, ← hay]
      group
  · exact ⟨a, y, hyy, hay, Or.inr hy⟩

end CFSG.EvenSporadicStandard.Induction.Hyp
