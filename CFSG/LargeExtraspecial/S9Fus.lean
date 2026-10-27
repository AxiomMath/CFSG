module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LargeExtraspecial.S6Six
public import CFSG.LargeExtraspecial.S6ThreeE
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

section Lin

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {f : LinearMap.BilinForm (ZMod 2) V}

theorem exists_hyperbolic_perp (hf : f.IsAlt) (hnd : f.Nondegenerate)
    (h4 : 4 ≤ finrank (ZMod 2) V) {a : V} (ha : a ≠ 0) :
    ∃ u w : V, f a u = 0 ∧ f a w = 0 ∧ f u w = 1 := by
  have hF : (⊥ : Submodule (ZMod 2) V) ⊓ S2.spPerp f ⊥ = ⊥ := bot_inf_eq _
  obtain ⟨b, -, hab⟩ := S2.sp_exists_partner hf hnd hF
    (by rw [S2.spPerp_bot]; exact Submodule.mem_top) ha
  have haF : a ∈ S2.spPerp f ⊥ := by rw [S2.spPerp_bot]; exact Submodule.mem_top
  have hbF : b ∈ S2.spPerp f ⊥ := by rw [S2.spPerp_bot]; exact Submodule.mem_top
  have hK := S2.sup_span_pair_inf_spPerp_eq_bot hf hF haF hbF hab
  have hdim := S2.finrank_spPerp_sup_span_pair hf hnd hF haF hbF hab
  rw [S2.spPerp_bot, finrank_top] at hdim
  have hne : S2.spPerp f ((⊥ : Submodule (ZMod 2) V) ⊔ Submodule.span (ZMod 2) {a, b}) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hdim
    omega
  obtain ⟨u, huK, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨w, hwK, huw⟩ := S2.sp_exists_partner hf hnd hK huK hu0
  have haK : a ∈ (⊥ : Submodule (ZMod 2) V) ⊔ Submodule.span (ZMod 2) {a, b} :=
    Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert a {b}))
  exact ⟨u, w, S2.mem_spPerp.mp huK a haK, S2.mem_spPerp.mp hwK a haK, huw⟩

end Lin

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem fix_of_commSpace_le_isotropic {τ : S.O} {P : Submodule (ZMod 2) S.Qt}
    (hP : ∀ u ∈ P, ∀ v ∈ P, polar S.q u v = 0)
    (hτ : commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ P) :
    ∀ p ∈ P, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) p = p := by
  intro p hp
  rw [← sub_eq_zero]
  refine S.q_nondegenerate.1 _ fun v => ?_
  rw [polarBilin_apply_apply]
  set w := ((τ⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v with hw
  have hv : v = (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w := (apply_inv_apply_O τ v).symm
  have h1 : polar S.q p ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) = 0 :=
    hP p hp _ (hτ (sub_mem_commSpace _ w))
  rw [hv, polar_sub_left, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup τ.2]
  rw [polar_sub_right] at h1
  rw [← sub_eq_zero.mp h1, sub_self]

section Fus

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hSp : SpCase H C ht ht1 hVQ) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
  (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
include hCE H hNo C ht ht1 hVQ hSp hh hb

theorem commSpace_le_Wone_of_mem_Nbar {τ : S.O} (hτN : τ ∈ Nbar S g t) :
    commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Wone S g t g ((h : G) * g) := by
  intro w hw
  obtain ⟨u, rfl⟩ := mem_commSpace.mp hw
  rw [mem_Wone]
  intro v hv
  have hτv := Nbar_fix_Vone' hCE H hNo C ht ht1 hVQ hSp hh hb hτN hv
  rw [polar_sub_right, ← hτv,
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup τ.2, hτv, sub_self]

omit hNo in
theorem exists_add_mem_commSpace (hNo : NoA2 S g) {τ : S.O} (hτN : τ ∈ Nbar S g t)
    (hcN : ∀ n ∈ Nbar S g t, n * τ = τ * n) {u : S.Qt}
    (hu : u ∈ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) (huP : u ∉ S.clSub (S.QG ⊓ S.Qa g)) :
    ∃ p ∈ S.clSub (S.QG ⊓ S.Qa g), ∃ v ∈ Vone S g t g ((h : G) * g),
      v ∉ S.clSub (S.QG ⊓ S.Qa g) ∧ p + v ∈ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  have haQ := H.conj_mem
  have hth := mem_Lbar_of_pair H ht hh
  have huW := commSpace_le_Wone_of_mem_Nbar hCE H hNo C ht ht1 hVQ hSp hh hb hτN hu
  rw [← Wone_eq_sup hCE H hNo C ht ht1 hVQ hSp hh hb] at huW
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp huW
  by_cases hqV : q ∈ Vone S g t g ((h : G) * g)
  · refine ⟨p, hp.1, q, hqV, fun hqP => huP (add_mem hp.1 hqP), hu⟩
  have hpW1 := clSub_inf_Wt_le_Wone H C ht ht1 hVQ hh hb hp
  have h1 := pair_one (t := t) hb
  have hba : ((1 : S.M) : G) * g * S.z * (((1 : S.M) : G) * g)⁻¹ ∉ S.Qa ((h : G) * g) :=
    not_mem_Qa_symm h1.2
  have hfixB := clSub_inf_Vone_eq hCE H hNo C ht ht1 hVQ hSp hh h1.1 hba
  rw [Vone_comm] at hfixB
  simp only [OneMemClass.coe_one, one_mul] at hfixB
  have hqB : q ∉ fixSub S (S.Lbar ((h : G) * g) ⊓ Nbar S g t) := by
    intro hqf
    have : q ∈ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Vone S g t g ((h : G) * g) := by
      rw [hfixB]
      exact ⟨hq.1, hqf⟩
    exact hqV this.2
  rw [mem_fixSub] at hqB
  push Not at hqB
  obtain ⟨y, hyB, hyq⟩ := hqB
  have hbQ := conj_mem_QG' S h.2 haQ
  have hyq' : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q = S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) := by
    have := Lbar_apply_sub_mem_span' hbQ hq.1 hyB.1
    rcases mem_span_cl_iff.mp this with h0 | h0
    · exact absurd (sub_eq_zero.mp h0) hyq
    · exact h0
  have hyp1 : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p ∈ S.clSub (S.QG ⊓ S.Qa g) :=
    sub_mem (Nbar_apply_mem_clSub haQ H.conj_ne (cl_a_mem_Vt ht) hyB.2 hp.1) hp.1
  have hyp2 : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p ∈ Vone S g t g ((h : G) * g) :=
    Nbar_apply_sub_mem_Vone hCE H hNo C ht ht1 hVQ hSp hh hb hyB.2 hpW1
  have hbV1 : S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ Vone S g t g ((h : G) * g) :=
    Vt_le_Vone _ _ (cl_mem_Vt hth)
  refine ⟨0, zero_mem _, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p +
    S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹), add_mem hyp2 hbV1, fun hmem => ?_, ?_⟩
  · have := sub_mem hmem hyp1
    rw [add_sub_cancel_left] at this
    exact cl_b_not_mem H hb this
  · rw [zero_add, ← hyq']
    have e : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p + ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q) =
        (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (p + q) - (p + q) := by
      rw [map_add]
      abel
    rw [e]
    exact sub_mem (S6.apply_mem_commSpace_of_commute (hcN y hyB.2) hu) hu

end Fus

end CFSG.LargeExtraspecial.S9
