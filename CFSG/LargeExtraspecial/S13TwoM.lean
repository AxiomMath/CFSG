module

public import CFSG.LargeExtraspecial.S13TwoL

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g g₁ : G} {K : Subgroup S.O}

section Four

variable (hCE : CentralExtInput.{u}) (Y : Hyp13 S g K) {h : S.M} (hg : g₁ = (h : G) * g)
  (hperp : ∀ u ∈ Fbar S g K, ∀ v ∈ Fbar S g₁ K, polar S.q u v = 0)
  (hne : Fbar S g₁ K ≠ Fbar S g K)
include hCE Y hg hperp hne

theorem false_of_pair (hbot : Ebar S g K ⊓ Ebar S g₁ K = ⊥) {s s' : S.O} (X : Hyp10 S g s)
    (X' : Hyp10 S g s') (hs : s ∈ Ebar S g K ⊓ ptStab S (Fbar S g K ⊔ Fbar S g₁ K))
    (hs'N : s' ∈ Nbar S g s) (hs's : s' ≠ s) : False := by
  set D := Fbar S g K ⊔ Fbar S g₁ K with hD
  have Y₁ : Hyp13 S g₁ K := Y.mul hg
  have hg' : g = ((h⁻¹ : S.M) : G) * g₁ := by rw [hg, Subgroup.coe_inv]; group
  have hperp' : ∀ u ∈ Fbar S g₁ K, ∀ v ∈ Fbar S g K, polar S.q u v = 0 := fun u hu v hv => by
    rw [QuadraticMap.polar_comm]; exact hperp v hv u hu
  have hne' : Fbar S g K ≠ Fbar S g₁ K := fun e => hne e.symm
  have hD' : (Fbar S g₁ K ⊔ Fbar S g K : Submodule (ZMod 2) S.Qt) = D := sup_comm _ _
  obtain ⟨hAT, hVs⟩ := Abar_eq_and_Vt_eq hCE Y hg hperp hne hbot X hs
  have hs'A : s' ∈ S.Lbar g ⊓ Nbar S g s := Subgroup.mem_inf.mpr ⟨X'.ht, hs'N⟩
  have hs'T : s' ∈ Ebar S g K ⊓ ptStab S D := hAT ▸ hs'A
  have hs'E : s' ∈ Ebar S g K := (Subgroup.mem_inf.mp hs'T).1
  have hinf := finrank_Vt_inf_Vt_le hCE X X' hs'N hs's
  have hFle : Fbar S g K ≤ Vt S g s ⊓ Vt S g s' :=
    le_inf (Y.Fbar_le_Vt (h₀ := 1) (by simp) (Subgroup.mem_inf.mp hs).1)
      (Y.Fbar_le_Vt (h₀ := 1) (by simp) hs'E)
  have hFeq : Fbar S g K = Vt S g s ⊓ Vt S g s' :=
    Submodule.eq_of_le_of_finrank_le hFle (by rw [Y.finrank_Fbar]; exact hinf)
  have hV'F₁ : Vt S g s' ⊓ Fbar S g₁ K = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv
    have hvF : v ∈ Fbar S g K := by
      rw [hFeq]
      exact Submodule.mem_inf.mpr ⟨hVs ▸ Submodule.mem_sup_right hv2, hv1⟩
    have := Fbar_inf_eq_bot Y Y₁ hne
    rw [← this]
    exact Submodule.mem_inf.mpr ⟨hvF, hv2⟩
  have hWs : Vt S g s' ≤ Wt S g s := Vt_le_Wt_symm (Vt_le_Wt_of_mem_Nbar X' hs'N)
  have hcomm' := commSpace_t_eq X'.H X'.C X'.ht X'.ht1 X'.hVQ
  have hfix : Vt S g s' ≤ fixSub S (Ebar S g₁ K ⊓ ptStab S (Fbar S g₁ K ⊔ Fbar S g K)) := by
    intro v hv y hy
    rw [hD'] at hy
    have hyc : s' * y = y * s' := comm_T₀_T₁ Y hg hperp hbot hs'T hy
    have hyv : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vt S g s' := by
      rw [← hcomm'.1] at hv ⊢
      obtain ⟨u, rfl⟩ := mem_commSpace.mp hv
      refine mem_commSpace.mpr ⟨(y : S.Qt ≃ₗ[ZMod 2] S.Qt) u, ?_⟩
      have e := congrArg (fun z : S.O => (z : S.Qt ≃ₗ[ZMod 2] S.Qt) u) hyc
      simp only [Subgroup.coe_mul, LinearEquiv.mul_apply] at e
      rw [map_sub, ← e]
    have hperpv : ∀ f ∈ Fbar S g₁ K, polar S.q v f = 0 := by
      intro f hf
      rw [QuadraticMap.polar_comm]
      exact mem_Wt.mp (hWs hv) f (hVs ▸ Submodule.mem_sup_right hf)
    have h1 := Y₁.Ebar_apply_sub_mem_Fbar hperpv (Subgroup.mem_inf.mp hy).1
    have h2 : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ Vt S g s' := sub_mem hyv hv
    have h3 : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ Vt S g s' ⊓ Fbar S g₁ K :=
      Submodule.mem_inf.mpr ⟨h2, h1⟩
    rw [hV'F₁, Submodule.mem_bot, sub_eq_zero] at h3
    exact h3
  rw [fixSub_T₀_eq Y₁ hg' hperp' hne', hD'] at hfix
  have hfix' : Vt S g s' ≤ Vt S g s := by rw [hVs]; exact hfix
  have heq : Vt S g s ⊓ Vt S g s' = Vt S g s' := inf_eq_right.mpr hfix'
  rw [heq, X'.h4] at hinf
  omega

theorem Ebar_inf_ne_bot : Ebar S g K ⊓ Ebar S g₁ K ≠ ⊥ := by
  intro hbot
  obtain ⟨t, τ, X, Xτ, Xτt, hτN, hτt⟩ := Y.exists_triple hCE
  set T₀ := Ebar S g K ⊓ ptStab S (Fbar S g K ⊔ Fbar S g₁ K) with hT₀
  have hAE := Y.Abar_le_Ebar hCE X
  have htE : t ∈ Ebar S g K := hAE (Subgroup.mem_inf.mpr ⟨X.ht, self_mem_Nbar X.H X.ht⟩)
  have hτE : τ ∈ Ebar S g K := hAE (Subgroup.mem_inf.mpr ⟨Xτ.ht, hτN⟩)
  have hcard := card_Ebar_eq_two_mul Y hg hperp hne
  by_cases htT : t ∈ T₀
  · exact false_of_pair hCE Y hg hperp hne hbot X Xτ htT hτN hτt
  by_cases hτT : τ ∈ T₀
  · exact false_of_pair hCE Y hg hperp hne hbot Xτ X hτT (mem_Nbar_symm X Xτ hτN) hτt.symm
  have hτtT : τ * t ∈ T₀ := mul_mem_of_card_eq_two_mul inf_le_left hcard hτE htE hτT htT
  have hτtN : τ * t ∈ Nbar S g t := mul_mem hτN (self_mem_Nbar X.H X.ht)
  refine false_of_pair hCE Y hg hperp hne hbot Xτt X hτtT (mem_Nbar_symm X Xτt hτtN) ?_
  intro e
  apply Xτ.ht1
  calc τ = τ * t * t⁻¹ := by group
    _ = 1 := by rw [← e, mul_inv_cancel]

theorem timmesfeld_13_2 :
    Nat.card (Ebar S g K) =
        2 * Nat.card (Ebar S g K ⊓ ptStab S (Fbar S g K ⊔ Fbar S g₁ K) : Subgroup S.O) ∧
      ∃ x ∈ Ebar S g K ⊓ Ebar S g₁ K, x ≠ 1 ∧ Hyp10 S g x ∧
        Vt S g x = Fbar S g K ⊔ Fbar S g₁ K := by
  refine ⟨card_Ebar_eq_two_mul Y hg hperp hne, ?_⟩
  obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Ebar_inf_ne_bot hCE Y hg hperp hne)
  have hx1' : x ≠ 1 := fun e => hx1 (Subtype.ext e)
  exact ⟨x, hx, hx1', hyp10_and_Vt_eq_of_mem_inf Y hg hne hx hx1'⟩

end Four

end CFSG.LargeExtraspecial.S13
