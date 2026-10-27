module

public import CFSG.LargeExtraspecial.S9RAStep1
public import CFSG.LargeExtraspecial.S9RACoverB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem cl_mem_commSpace_of_mem_Lbar_conj (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) {w : S.M} {σ : S.O}
    (hσL : σ ∈ S.Lbar ((w : G) * g)) (hσ : ∃ x ∈ S.Mbar, σ = x * t * x⁻¹) :
    S.cl ((w : G) * g * S.z * ((w : G) * g)⁻¹) ∈ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  have haQ := H.conj_mem
  obtain ⟨x, hxM, rfl⟩ := hσ
  have hmem : (S.ρ w)⁻¹ * (x * t * x⁻¹) * S.ρ w ∈ conjL S g t :=
    ⟨(mem_Lbar_mul_iff S w g).mp hσL, (S.ρ w)⁻¹ * x, S.Mbar.mul_mem (inv_mem ⟨w, rfl⟩) hxM,
      by group⟩
  obtain ⟨n, hnM, hnN, hn⟩ := exists_normalizer_conj_eq H C ht hmem
  have hfix := fix_of_mem_normalizer H hnN
  have h1 : S.cl (g * S.z * g⁻¹) ∈ commSpace ((n * t * n⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [S8.commSpace_conj, (commSpace_t_eq H C ht ht1 hVQ).1]
    exact ⟨_, cl_a_mem_Vt ht, hfix⟩
  rw [← hn] at h1
  have e : x * t * x⁻¹ = S.ρ w * ((S.ρ w)⁻¹ * (x * t * x⁻¹) * S.ρ w) * (S.ρ w)⁻¹ := by group
  rw [e, S8.commSpace_conj]
  refine ⟨_, h1, ?_⟩
  change ((S.ρ w : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = _
  rw [ρ_cl_conj_z S w haQ]

theorem conj_Fbar_eq_of_apply_eq (H : Hyp4 S g) {t w r : S.O} (hwM : w ∈ S.Mbar)
    (hrM : r ∈ S.Mbar)
    (hwr : (w : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) {f : S.O} (hf : f ∈ Fbar S g t) :
    ∃ f' ∈ Fbar S g t, w * f * w⁻¹ = r * f' * r⁻¹ := by
  have hnM : r⁻¹ * w ∈ S.Mbar := S.Mbar.mul_mem (inv_mem hrM) hwM
  have hfix : ((r⁻¹ * w : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl (((1 : S.M) : G) * g * S.z * (((1 : S.M) : G) * g)⁻¹)) =
        S.cl (((1 : S.M) : G) * g * S.z * (((1 : S.M) : G) * g)⁻¹) := by
    simp only [OneMemClass.coe_one, one_mul]
    rw [coe_mul_apply, hwr, inv_apply_apply_O]
  have hnN := mem_normalizer_of_fix H.conj_mem H.conj_ne (h := 1) hnM hfix
  simp only [OneMemClass.coe_one, one_mul] at hnN
  refine ⟨(r⁻¹ * w) * f * (r⁻¹ * w)⁻¹, conj_mem_Fbar hnM hnN hf, by group⟩

theorem typeII_symm (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (htr : ∀ v : Vt S g t, v ≠ 0 → ∃ x ∈ RmodN S g t, x (aV ht) = v)
    (hL : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x : S.O} (hxM : x ∈ S.Mbar) (hτt : x * t * x⁻¹ * t = t * (x * t * x⁻¹))
    (hβ : ∀ k : S.M, S.ρ k ∈ Rbar S g t → x * t * x⁻¹ ∉ S.Lbar ((k : G) * g) ⊓ Nbar S g t) :
    x⁻¹ * t * x⁻¹⁻¹ * t = t * (x⁻¹ * t * x⁻¹⁻¹) ∧
      ∀ k : S.M, S.ρ k ∈ Rbar S g t → x⁻¹ * t * x⁻¹⁻¹ ∉ S.Lbar ((k : G) * g) ⊓ Nbar S g t := by
  have haQ := H.conj_mem
  refine ⟨?_, fun k hk hkA => ?_⟩
  · calc x⁻¹ * t * x⁻¹⁻¹ * t = x⁻¹ * (t * (x * t * x⁻¹)) * x := by group
      _ = x⁻¹ * (x * t * x⁻¹ * t) * x := by rw [hτt]
      _ = t * (x⁻¹ * t * x⁻¹⁻¹) := by group
  have hinf := inf_commSpace_eq_bot H C ht ht1 hVQ htr hL hxM hβ
  have hc := cl_mem_commSpace_of_mem_Lbar_conj H C ht ht1 hVQ hkA.1
    ⟨x⁻¹, inv_mem hxM, rfl⟩
  rw [S8.commSpace_conj, (commSpace_t_eq H C ht ht1 hVQ).1] at hc
  obtain ⟨v, hvV, hv⟩ := hc
  have hcV : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t :=
    Submodule.subset_span ⟨k, mem_Lbar_mul_of_mem_Rbar H ht hk, rfl⟩
  have hv' : v = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) := by
    rw [← hv]
    exact (apply_inv_apply_O x v).symm
  have hmem : v ∈ Vt S g t ⊓ commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    refine ⟨hvV, ?_⟩
    rw [S8.commSpace_conj, (commSpace_t_eq H C ht ht1 hVQ).1, hv']
    exact ⟨_, hcV, rfl⟩
  rw [hinf, Submodule.mem_bot] at hmem
  apply cl_conj_z_ne_zero S (conj_mem_QG' S k.2 haQ) (conj_ne_z' S k.2 H.conj_ne)
  rw [hmem] at hv
  simpa using hv.symm

section N0

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hSp : SpCase H C ht ht1 hVQ) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
  (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
include hCE H hNo C ht ht1 hVQ hSp hh hb

theorem mul_eq_one_or_conj_of_caseB [hN : NQHyp S g t] (h4 : finrank (ZMod 2) (Vt S g t) = 4)
    (hL : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    (hr2 : finrank (ZMod 2) (nqSub S g t (Fbar S g t)) = 2) {r₁ r₂ : S.O}
    (hr₁ : r₁ ∈ Rbar S g t) (hr₂ : r₂ ∈ Rbar S g t) {f₁ f₂ : S.O} (hf₁ : f₁ ∈ Fbar S g t)
    (hf₂ : f₂ ∈ Fbar S g t) :
    r₁ * f₁ * r₁⁻¹ * (r₂ * f₂ * r₂⁻¹) = 1 ∨
      ∃ x ∈ S.Mbar, r₁ * f₁ * r₁⁻¹ * (r₂ * f₂ * r₂⁻¹) = x * t * x⁻¹ := by
  have haQ := H.conj_mem
  have hN0 := Nbar_eq_N0bar_of_spCase hCE H hNo C ht ht1 hVQ hSp
  have hD := timmesfeld_6_5_sp H hNo C ht ht1 hVQ hSp hN0 hh hb
  have hFN : conjL S g t ⊆ Nbar S g t := by
    rintro τ ⟨hτL, x, hxM, rfl⟩
    exact hL x hxM hτL
  have hkey : ∀ τ ∈ conjL S g t, τ ≠ t → ∃ y ∈ S.Mbar, y * τ * y⁻¹ = τ * t := by
    rintro τ ⟨hτL, x, hxM, rfl⟩ hne
    obtain ⟨n, hn, hnτ⟩ := exists_conj_eq_mul_t hCE H hNo C ht ht1 hVQ hSp hxM
      ⟨hτL, hL x hxM hτL⟩ hne
    exact ⟨n, Rbar_le_Mbar (Nbar_le_Rbar hn), hnτ⟩
  have hFle : Fbar S g t ≤ Nbar S g t := Fbar_le_of_subset hFN
  have hcov' := exists_cover_of_finrank_two (nqRep S g t hSp.eq_sp) (beta_isAlt H C ht ht1 hVQ)
    (beta_nondegenerate H C ht ht1 hVQ) h4 (beta_aV_bV H C ht ht1 hVQ hh hb) hD
    (nqSub_Fbar_le_fixOf hCE H hNo C ht ht1 hVQ hSp hh hb) hr2
    (fun e he u hu => nqRep_mem_nqSub_Fbar H C ht ht1 hVQ hSp he hu)
  obtain ⟨Z, hUZ, hZinv, hcov⟩ := hcov'
  have hcls : ∀ (r : Rbar S g t) (f : S.O) (hf : f ∈ Fbar S g t),
      nqMk (nConj r ⟨f, hFle hf⟩) ∈ Z := by
    intro r f hf
    have heR : resV haQ t r ∈ RmodN S g t := by rw [← range_resV haQ t]; exact ⟨r, rfl⟩
    rw [hSp.eq_sp] at heR
    rw [← nqRep_apply hSp.eq_sp (e := ⟨_, heR⟩) rfl]
    exact hZinv _ _ (hUZ ⟨⟨f, hFle hf⟩, hf, rfl⟩)
  have hz := add_mem (hcls ⟨r₁, hr₁⟩ f₁ hf₁) (hcls ⟨r₂, hr₂⟩ f₂ hf₂)
  rw [← nqMk_mul] at hz
  have hcz := hcov _ hz
  obtain ⟨e, u, hu, hue⟩ := hcz
  obtain ⟨x₃, hx₃F, hx₃u⟩ := hu
  have heR : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ RmodN S g t := by
    rw [hSp.eq_sp]; exact e.2
  rw [← range_resV haQ t] at heR
  obtain ⟨r₃, hr₃⟩ := heR
  subst hx₃u
  change nqRep S g t hSp.eq_sp e (nqMk x₃) = _ at hue
  rw [nqRep_apply hSp.eq_sp hr₃.symm, nqMk_eq_iff] at hue
  simp only [coe_nConj, Subgroup.coe_mul] at hue
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  have hr₃t := commute_of_mem_Rbar haQ r₃.2
  have hr₃t' : ((r₃ : S.O))⁻¹ * t = t * ((r₃ : S.O))⁻¹ := by
    calc ((r₃ : S.O))⁻¹ * t = ((r₃ : S.O))⁻¹ * (t * r₃) * ((r₃ : S.O))⁻¹ := by group
      _ = ((r₃ : S.O))⁻¹ * (r₃ * t) * ((r₃ : S.O))⁻¹ := by rw [hr₃t]
      _ = t * ((r₃ : S.O))⁻¹ := by group
  generalize hA : r₁ * f₁ * r₁⁻¹ * (r₂ * f₂ * r₂⁻¹) = A at hue ⊢
  have hf' : ∃ f' ∈ Fbar S g t, A = (r₃ : S.O) * f' * ((r₃ : S.O))⁻¹ := by
    rcases S8.eq_one_or_eq_of_mem_zpowers htt hue with h1 | h1
    · exact ⟨x₃, hx₃F, (inv_mul_eq_one.mp h1).symm⟩
    · refine ⟨x₃ * t, mul_mem hx₃F (self_mem_Fbar ht), ?_⟩
      calc A = (r₃ : S.O) * x₃ * ((r₃ : S.O))⁻¹ *
            (((r₃ : S.O) * x₃ * ((r₃ : S.O))⁻¹)⁻¹ * A) := by group
        _ = (r₃ : S.O) * x₃ * (((r₃ : S.O))⁻¹ * t) := by rw [h1]; group
        _ = (r₃ : S.O) * (x₃ * t) * ((r₃ : S.O))⁻¹ := by rw [hr₃t']; group
  obtain ⟨f', hf'F, hAf'⟩ := hf'
  have hcase := mem_conjL_of_mem_Fbar H C ht hkey hf'F
  rcases hcase with h1 | ⟨-, y, hyM, hy⟩
  · left
    rw [hAf', h1, mul_one, mul_inv_cancel]
  · right
    refine ⟨(r₃ : S.O) * y, S.Mbar.mul_mem (Rbar_le_Mbar r₃.2) hyM, ?_⟩
    rw [hAf', hy]
    group

end N0

end CFSG.LargeExtraspecial.S9
