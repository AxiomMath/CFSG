module

public import CFSG.LargeExtraspecial.S8FusB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

section Beta

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g)
  (hA : Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) *
    2 ^ (finrank (ZMod 2) (Vt S g t) - 1) = 2 ^ S.width)
  (hN : ∀ x ∈ Nbar S g t, ∀ w ∈ Wt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t)
  {h : S.M} (hh : S.ρ h ∈ Rbar S g t) (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
  (hPab : S.clSub (S.QG ⊓ S.Qa g) ⊓ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ≤ Vt S g t)
include H C ht ht1 hVQ hA hN hh hb hPab

theorem false_of_fusion_beta {τ : S.O}
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hdim : finrank (ZMod 2) (commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      finrank (ZMod 2) (Vt S g t))
    (hcN : ∀ n ∈ Nbar S g t, n * τ = τ * n)
    (hanis : ∀ d ∈ Vt S g t ⊓ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt), d ∉ orbit S g t)
    (hAV1 : ∀ a' ∈ S.Lbar g ⊓ Nbar S g t, ∀ w ∈ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt),
      (a' : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w) : False := by
  set V1 := commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hV1
  have hth := mem_Lbar_of_pair H ht hh
  have hbV := cl_mem_Vt hth
  have hdec := sup_eq_Wt H C ht ht1 hVQ hh hb hPab
  have hfixA := clSub_inf_fixSub_Abar H C ht ht1 hVQ hA
  have hfixB := clSub_inf_fixSub_Abar (H.mul h) (C.mul h) hth ht1 (not_V_le_Qa_mul H hVQ hh)
    (card_Abar_mul H hh hA)
  rw [Nbar_mul, Vt_mul] at hfixB
  have hV1W : V1 ≤ Wt S g t := commSpace_le_Wt_of_fix hτV
  have hborb : S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ orbit S g t :=
    ⟨S.ρ h, hh, (ρ_cl_conj_z S h H.conj_mem).symm⟩
  have hV1V : V1 ≤ Vt S g t := by
    intro w hw
    obtain ⟨α, hα, β, hβ, rfl⟩ := Submodule.mem_sup.mp (hdec ▸ hV1W hw)
    have hAfix : ∀ a' ∈ S.Lbar g ⊓ Nbar S g t, (a' : S.Qt ≃ₗ[ZMod 2] S.Qt) α = α := by
      intro a' ha'
      have h1 := hAV1 a' ha' _ hw
      have h2 := Lbar_apply_sub_mem_span' H.conj_mem hα.1 ha'.1
      have h3 : (a' : S.Qt ≃ₗ[ZMod 2] S.Qt) β - β ∈ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) :=
        sub_mem (Nbar_apply_mem_clSub (conj_mem_QG' S h.2 H.conj_mem) (conj_ne_z' S h.2 H.conj_ne)
          hbV ha'.2 hβ.1) hβ.1
      have e : (a' : S.Qt ≃ₗ[ZMod 2] S.Qt) α - α =
          -((a' : S.Qt ≃ₗ[ZMod 2] S.Qt) β - β) := by
        rw [map_add] at h1
        rw [eq_neg_iff_add_eq_zero]
        calc (a' : S.Qt ≃ₗ[ZMod 2] S.Qt) α - α + ((a' : S.Qt ≃ₗ[ZMod 2] S.Qt) β - β) =
            ((a' : S.Qt ≃ₗ[ZMod 2] S.Qt) α + (a' : S.Qt ≃ₗ[ZMod 2] S.Qt) β) - (α + β) := by
              abel
          _ = 0 := by rw [h1, sub_self]
      rw [e] at h2
      have h4 := neg_mem h2
      rw [neg_neg] at h4
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h4
      rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
      · rw [zero_smul] at hc
        have := eq_neg_of_add_eq_zero_left (show (a' : S.Qt ≃ₗ[ZMod 2] S.Qt) α - α +
          ((a' : S.Qt ≃ₗ[ZMod 2] S.Qt) β - β) = 0 by rw [e]; abel)
        rw [← hc, neg_zero] at this
        exact sub_eq_zero.mp this
      · rw [one_smul] at hc
        exact absurd (hc ▸ h3) (cl_a_not_mem H hb)
    have hαV : α ∈ Vt S g t := by
      have hmem : α ∈ S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S (S.Lbar g ⊓ Nbar S g t) :=
        ⟨hα.1, (mem_fixSub S).mpr hAfix⟩
      rw [hfixA] at hmem
      exact hmem.2
    have hBfix : ∀ y ∈ S.Lbar ((h : G) * g) ⊓ Nbar S g t, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) β = β := by
      intro y hy
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
        (Lbar_apply_sub_mem_span' (H.mul h).conj_mem hβ.1 hy.1)
      rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
      · rw [zero_smul] at hc
        exact (sub_eq_zero.mp hc.symm)
      · exfalso
        rw [one_smul] at hc
        have hD : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (α + β) - (α + β) ∈ Vt S g t ⊓ V1 :=
          ⟨hN y hy.2 _ (hV1W hw),
            sub_mem (apply_mem_commSpace_of_commute (hcN y hy.2) hw) hw⟩
        have e : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (α + β) - (α + β) =
            S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) := by
          rw [map_add, (mem_Nbar.mp hy.2).2 α hαV, hc]; abel
        rw [e] at hD
        exact hanis _ hD hborb
    have hβV : β ∈ Vt S g t := by
      have hmem : β ∈ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓
          fixSub S (S.Lbar ((h : G) * g) ⊓ Nbar S g t) := ⟨hβ.1, (mem_fixSub S).mpr hBfix⟩
      rw [hfixB] at hmem
      exact hmem.2
    exact add_mem hαV hβV
  have heq : V1 = Vt S g t := Submodule.eq_of_le_of_finrank_le hV1V hdim.ge
  have ha : S.cl (g * S.z * g⁻¹) ∈ Vt S g t ⊓ V1 := ⟨cl_a_mem_Vt ht, heq ▸ cl_a_mem_Vt ht⟩
  exact hanis _ ha (cl_a_mem_orbit (S := S))

end Beta

end CFSG.LargeExtraspecial.S8
