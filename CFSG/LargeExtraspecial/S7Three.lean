module

public import CFSG.LargeExtraspecial.S7Basic
public import CFSG.LargeExtraspecial.S7Lin
public import CFSG.LargeExtraspecial.S5Fus
public import CFSG.LargeExtraspecial.S6SevenC
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S7

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S) in
@[expose] def Orbit67 (g : G) (t : S.O) : Prop :=
  ∀ h : S.M, S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ Vt S g t →
    S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ orbit S g t

theorem orbit67_of_omegaCase (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1} {hVQ : ¬ V S g t ≤ S.Qa g}
    (hΩ : OmegaCase H C ht ht1 hVQ) (h6 : 6 ≤ finrank (ZMod 2) (Vt S g t)) : Orbit67 S g t :=
  fun _ hh => cl_mem_orbit_of_omegaCase hCE H hNo C hΩ h6 hh

theorem inv_apply_cl (haQ : g * S.z * g⁻¹ ∈ S.QG) (k h : S.M) :
    (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)) =
      S.cl (((k⁻¹ * h : S.M) : G) * g * S.z * (((k⁻¹ * h : S.M) : G) * g)⁻¹) := by
  rw [← map_inv, ρ_cl_conj_z S (k⁻¹) (conj_mem_QG' S h.2 haQ)]
  congr 1
  simp [mul_assoc]

theorem conj_mem_Lbar_of_inv_apply_mem (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (h67 : Orbit67 S g t) (k h : S.M)
    (hmem : (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)) ∈ Vt S g t) :
    S.ρ k * t * (S.ρ k)⁻¹ ∈ S.Lbar ((h : G) * g) := by
  rw [inv_apply_cl H.conj_mem] at hmem
  obtain ⟨j, hj, hjc⟩ := exists_of_mem_orbit (h67 _ hmem) H.conj_mem
  have htj := mem_Lbar_mul_of_mem_Rbar H ht hj
  have hL : S.Lbar (((k⁻¹ * h : S.M) : G) * g) = S.Lbar ((j : G) * g) :=
    Lbar_eq_of_cl_eq S (conj_mem_QG' S j.2 H.conj_mem) (conj_ne_z' S j.2 H.conj_ne)
      (conj_mem_QG' S (k⁻¹ * h).2 H.conj_mem) hjc
  rw [← hL] at htj
  have h1 := conj_mem_Lbar_mul S k htj
  have e : (k : G) * (((k⁻¹ * h : S.M) : G) * g) = (h : G) * g := by simp [mul_assoc]
  rwa [e] at h1

theorem strongClosed_mul (H : Hyp4 S g) {t : S.O}
    (hSC : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ = t) {h : S.M}
    (hh : S.ρ h ∈ Rbar S g t) {x : S.O} (hx : x ∈ S.Mbar)
    (hxt : x * t * x⁻¹ ∈ S.Lbar ((h : G) * g)) : x * t * x⁻¹ = t := by
  rw [mem_Lbar_mul_iff] at hxt
  have hy : (S.ρ h)⁻¹ * x ∈ S.Mbar := mul_mem (inv_mem ⟨h, rfl⟩) hx
  have e1 : ((S.ρ h)⁻¹ * x) * t * ((S.ρ h)⁻¹ * x)⁻¹ = (S.ρ h)⁻¹ * (x * t * x⁻¹) * S.ρ h := by
    group
  have h1 := hSC _ hy (e1 ▸ hxt)
  have hc := commute_of_mem_Rbar H.conj_mem hh
  calc x * t * x⁻¹ = S.ρ h * (((S.ρ h)⁻¹ * x) * t * ((S.ρ h)⁻¹ * x)⁻¹) * (S.ρ h)⁻¹ := by group
    _ = S.ρ h * t * (S.ρ h)⁻¹ := by rw [h1]
    _ = t := by rw [hc, mul_assoc, mul_inv_cancel, mul_one]

theorem Nbar_eq_N0bar (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (hN : Nbar S g t = zpowers t) : Nbar S g t = N0bar S g t := by
  refine le_antisymm ?_ N0bar_le_Nbar
  rw [hN, zpowers_le]
  exact Lbar_inf_Nbar_le_N0bar ⟨ht, self_mem_Nbar H ht⟩

section Main

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hΩ : OmegaCase H C ht ht1 hVQ) (hN : Nbar S g t = zpowers t)
include hCE H hNo C ht ht1 hVQ hΩ hN

theorem conj_eq_of_mem_normalizer (h8 : 8 ≤ finrank (ZMod 2) (Vt S g t)) {k : S.M}
    (hk : S.ρ k ∈ normalizer (S.Lbar g : Set S.O)) : S.ρ k * t * (S.ρ k)⁻¹ = t := by
  have h67 := orbit67_of_omegaCase hCE H hNo C hΩ (by omega : 6 ≤ finrank (ZMod 2) (Vt S g t))
  set e : S.Qt ≃ₗ[ZMod 2] S.Qt := ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with he
  have hn := width_eq_finrank_of_omegaCase H hNo C ht ht1 hN hΩ
  have hdP := S.finrank_clSub_QG_inf_Qa H.conj_mem H.conj_ne C.card_QG_inf_Qa
  have hdPV := finrank_clSub_inf_Vt H C ht ht1 hVQ
  set P := S.clSub (S.QG ⊓ S.Qa g) with hP
  have hxa := fix_of_mem_normalizer H hk
  have hPx : ∀ v ∈ P, e v ∈ P := fun v hv =>
    apply_mem_clSub_of_fix H.conj_mem H.conj_ne ⟨k, rfl⟩ hxa hv
  have hPmap : P.map e.toLinearMap = P := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq e P)
    rintro _ ⟨v, hv, rfl⟩
    exact hPx v hv
  set Y := (Vt S g t).map e.toLinearMap with hY
  have hPY : (P ⊓ Vt S g t).map e.toLinearMap = P ⊓ Y := by
    rw [Submodule.map_inf _ e.injective, hPmap]
  have h1 : finrank (ZMod 2) ↥(P ⊓ Y) = finrank (ZMod 2) ↥(P ⊓ Vt S g t) := by
    rw [← hPY, LinearEquiv.finrank_map_eq]
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (P ⊓ Vt S g t) (P ⊓ Y)
  have h3 : finrank (ZMod 2) ↥((P ⊓ Vt S g t) ⊔ (P ⊓ Y)) ≤ finrank (ZMod 2) P :=
    Submodule.finrank_mono (sup_le inf_le_left inf_le_left)
  have h4 : finrank (ZMod 2) ↥((P ⊓ Vt S g t) ⊓ (P ⊓ Y)) ≤
      finrank (ZMod 2) ↥(Vt S g t ⊓ Y) :=
    Submodule.finrank_mono fun v hv => ⟨hv.1.2, hv.2.2⟩
  set U : Submodule (ZMod 2) (Vt S g t) := Y.comap (Vt S g t).subtype with hU
  have hdU : finrank (ZMod 2) U = finrank (ZMod 2) ↥(Vt S g t ⊓ Y) := by
    rw [← Submodule.finrank_map_subtype_eq, hU, Submodule.map_comap_subtype]
  obtain ⟨Q, hQ, hpol, -, -, hsing⟩ := hΩ.exists_form
  obtain ⟨α, hαU, β, hβU, hα0, hQα, hQβ, hαβ⟩ :=
    exists_hyperbolic_pair hQ (U := U) (by omega) (by omega)
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hαβ
    exact zero_ne_one hαβ
  have hαo := (hsing α hα0).mp hQα
  have hβo := (hsing β hβ0).mp hQβ
  rw [mem_orbitOf_RmodN_iff H.conj_mem ht] at hαo hβo
  obtain ⟨h₁, hh₁, hα⟩ := exists_of_mem_orbit hαo H.conj_mem
  obtain ⟨h₂, hh₂, hβ⟩ := exists_of_mem_orbit hβo H.conj_mem
  have htk₁ := mem_Lbar_mul_of_mem_Rbar H ht hh₁
  have htk₂ := mem_Lbar_mul_of_mem_Rbar H ht hh₂
  have hα' : α = bV htk₁ := Subtype.ext (by rw [coe_bV]; exact hα)
  have hβ' : β = bV htk₂ := Subtype.ext (by rw [coe_bV]; exact hβ)
  have hb : (h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹ ∉ S.Qa ((h₁ : G) * g) := by
    intro hmem
    have h0 : beta H C ht ht1 hVQ (bV htk₁) (bV htk₂) = 0 := by
      rw [beta_bV_eq_zero_iff H C ht ht1 hVQ hh₁ htk₁, coe_bV]
      exact S.cl_mem_clSub ⟨conj_mem_QG' S h₂.2 H.conj_mem, hmem⟩ (conj_mem_QG' S h₂.2 H.conj_mem)
    rw [← hα', ← hβ', ← hpol, polarBilin_apply_apply, hαβ] at h0
    exact one_ne_zero h0
  have hgen := Rbar_le_sup_of_omegaCase H C ht ht1 hVQ hh₁ hh₂ hb hNo hΩ
  have hinf := timmesfeld_6_5_inf H ht hh₁ hh₂ hgen (Nbar_eq_N0bar H ht hN) C ht1 hVQ
  have hinvY : ∀ {w : Vt S g t}, w ∈ U →
      (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Vt S g t := by
    intro w hw
    obtain ⟨v, hv, hvw⟩ := (show (w : S.Qt) ∈ Y from hw)
    rw [← hvw]
    change (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v)
      ∈ Vt S g t
    rw [inv_apply_apply_O]
    exact hv
  have hm₁ := conj_mem_Lbar_of_inv_apply_mem H ht h67 k h₁ (hα ▸ hinvY hαU)
  have hm₂ := conj_mem_Lbar_of_inv_apply_mem H ht h67 k h₂ (hβ ▸ hinvY hβU)
  have hmem : S.ρ k * t * (S.ρ k)⁻¹ ∈ zpowers t := hinf ▸ ⟨hm₁, hm₂⟩
  rcases (mem_zpowers_iff_of_mem_Lbar H ht).mp hmem with h0 | h0
  · exfalso
    apply ht1
    have := congrArg (fun y => (S.ρ k)⁻¹ * y * S.ρ k) h0
    simpa [mul_assoc] using this
  · exact h0

theorem strongClosed_of_omegaCase (h8 : 8 ≤ finrank (ZMod 2) (Vt S g t)) {x : S.O}
    (hx : x ∈ S.Mbar) (hxt : x * t * x⁻¹ ∈ S.Lbar g) : x * t * x⁻¹ = t := by
  have hcomm : ∀ l ∈ S.Lbar g, t * l = l * t := fun l hl => Lbar_comm S H.conj_mem ht hl
  have hcomm' : ∀ l ∈ S.Lbar g, x * t * x⁻¹ * l = l * (x * t * x⁻¹) := fun l hl =>
    Lbar_comm S H.conj_mem hxt hl
  obtain ⟨n, hnM, hnN, hn⟩ := S5.exists_mem_normalizer_conj H C hx hcomm hcomm'
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hnM
  rw [hn]
  exact conj_eq_of_mem_normalizer hCE H hNo C ht ht1 hVQ hΩ hN h8 hnN

theorem timmesfeld_7_3 (h6 : 6 ≤ finrank (ZMod 2) (Vt S g t)) :
    S.width = finrank (ZMod 2) (Vt S g t) ∧
      (finrank (ZMod 2) (Vt S g t) = 6 ∨
        (8 ≤ finrank (ZMod 2) (Vt S g t) ∧
          ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ = t)) := by
  refine ⟨width_eq_finrank_of_omegaCase H hNo C ht ht1 hN hΩ, ?_⟩
  obtain ⟨m, hm⟩ := even_finrank_Vt H C ht ht1 hVQ
  by_cases h8 : 8 ≤ finrank (ZMod 2) (Vt S g t)
  · exact Or.inr ⟨h8, fun x hx hxt =>
      strongClosed_of_omegaCase hCE H hNo C ht ht1 hVQ hΩ hN h8 hx hxt⟩
  · left
    omega

end Main

end CFSG.LargeExtraspecial.S7
