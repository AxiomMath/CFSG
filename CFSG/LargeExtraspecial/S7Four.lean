module

public import CFSG.LargeExtraspecial.S7Three
public import CFSG.LargeExtraspecial.S12Good
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureOddCoreTransport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S7

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open CFSG.Open

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem commSpace_conj (x t : S.O) :
    commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)).map
        ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) := by
  ext v
  constructor
  · intro hv
    obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
    refine ⟨(t : S.Qt ≃ₗ[ZMod 2] S.Qt) (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
      ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w, sub_mem_commSpace _ _, ?_⟩
    simp only [LinearEquiv.coe_coe, map_sub, coe_mul_apply, apply_inv_apply_O]
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨u, rfl⟩ := mem_commSpace.mp hw
    refine mem_commSpace.mpr ⟨(x : S.Qt ≃ₗ[ZMod 2] S.Qt) u, ?_⟩
    simp only [LinearEquiv.coe_coe, map_sub, coe_mul_apply, inv_apply_apply_O]

section Four

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hΩ : OmegaCase H C ht ht1 hVQ) (hN : Nbar S g t = zpowers t)
  (h8 : 8 ≤ finrank (ZMod 2) (Vt S g t))
include hCE H hNo C ht ht1 hVQ hΩ hN h8

theorem isolated_of_omegaCase {x : S.O} (hx : x ∈ S.Mbar)
    (hcomm : x * t * x⁻¹ * t = t * (x * t * x⁻¹)) : x * t * x⁻¹ = t := by
  by_contra hne
  have h67 := orbit67_of_omegaCase hCE H hNo C hΩ (by omega : 6 ≤ finrank (ZMod 2) (Vt S g t))
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hx
  set E : S.Qt ≃ₗ[ZMod 2] S.Qt := (t : S.Qt ≃ₗ[ZMod 2] S.Qt) with hE
  set E₁ : S.Qt ≃ₗ[ZMod 2] S.Qt :=
    ((S.ρ k * t * (S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with hE₁
  have hn := width_eq_finrank_of_omegaCase H hNo C ht ht1 hN hΩ
  obtain ⟨hcV, hfW⟩ := commSpace_t_eq H C ht ht1 hVQ
  have hWV : Wt S g t = Vt S g t := by
    have h1 := finrank_Wt (S := S) (g := g) (t := t)
    have h2 := S.finrank_Qt_eq_two_mul_width
    exact (Submodule.eq_of_le_of_finrank_le (Vt_le_Wt H ht1) (by omega)).symm
  have hSC : ∀ y ∈ S.Mbar, y * t * y⁻¹ ∈ S.Lbar g → y * t * y⁻¹ = t := fun y hy hyt =>
    strongClosed_of_omegaCase hCE H hNo C ht ht1 hVQ hΩ hN h8 hy hyt
  obtain ⟨Q, -, -, -, -, hsing⟩ := hΩ.exists_form
  set U : Submodule (ZMod 2) (Vt S g t) := (commSpace E₁).comap (Vt S g t).subtype with hU
  have hanis : ∀ w ∈ U, Q w = 0 → w = 0 := by
    intro w hw hQw
    by_contra hw0
    have hwo := (hsing w hw0).mp hQw
    rw [mem_orbitOf_RmodN_iff H.conj_mem ht] at hwo
    obtain ⟨h, hh, hwh⟩ := exists_of_mem_orbit hwo H.conj_mem
    have hw' : (w : S.Qt) ∈ commSpace E₁ := hw
    rw [hE₁, commSpace_conj] at hw'
    obtain ⟨v, hv, hvw⟩ := hw'
    have hmem : (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)) ∈ Vt S g t := by
      rw [← hwh, ← hvw, LinearEquiv.coe_coe, inv_apply_apply_O, ← hcV]
      exact hv
    exact hne (strongClosed_mul H hSC hh ⟨k, rfl⟩
      (conj_mem_Lbar_of_inv_apply_mem H ht h67 k h hmem))
  have hU2 := finrank_le_two_of_anisotropic Q hanis
  have hdU : finrank (ZMod 2) U = finrank (ZMod 2) ↥(Vt S g t ⊓ commSpace E₁) := by
    rw [← Submodule.finrank_map_subtype_eq, hU, Submodule.map_comap_subtype]
  have hd₁ : finrank (ZMod 2) (commSpace E₁) = finrank (ZMod 2) (Vt S g t) := by
    rw [hE₁, commSpace_conj, LinearEquiv.finrank_map_eq, hcV]
  have hEE : ∀ v, E (E₁ v) = E₁ (E v) := by
    intro v
    have := congrArg (fun y : S.O => (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v) hcomm
    simp only [coe_mul_apply] at this
    rw [hE, hE₁]
    simp only [coe_mul_apply]
    exact this.symm
  have hcomp : ((E : S.Qt →ₗ[ZMod 2] S.Qt) - 1).comp ((E₁ : S.Qt →ₗ[ZMod 2] S.Qt) - 1) =
      ((E₁ : S.Qt →ₗ[ZMod 2] S.Qt) - 1).comp ((E : S.Qt →ₗ[ZMod 2] S.Qt) - 1) := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearEquiv.coe_coe, map_sub, hEE]
    abel
  have hmap : (commSpace E₁).map ((E : S.Qt →ₗ[ZMod 2] S.Qt) - 1) =
      (Vt S g t).map ((E₁ : S.Qt →ₗ[ZMod 2] S.Qt) - 1) := by
    rw [← hcV, commSpace, commSpace, ← LinearMap.range_comp, ← LinearMap.range_comp, hcomp]
  have hle : (Vt S g t).map ((E₁ : S.Qt →ₗ[ZMod 2] S.Qt) - 1) ≤ Vt S g t ⊓ commSpace E₁ := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨?_, ⟨v, rfl⟩⟩
    rw [← hcV] at hv ⊢
    obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
    refine mem_commSpace.mpr ⟨E₁ w - w, ?_⟩
    have hEE' : ∀ v, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (E₁ v) = E₁ ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) v) :=
      hEE
    simp only [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, map_sub, hEE']
  have hrk := S2.finrank_map_sub_one_add E (commSpace E₁)
  rw [hmap, hfW, hWV, inf_comm] at hrk
  have h3 := Submodule.finrank_mono hle
  omega

theorem timmesfeld_7_4 :
    (∀ y : S.Mbar, y * ⟨t, S.Lbar_le_Mbar g ht⟩ * y⁻¹ * (⟨t, S.Lbar_le_Mbar g ht⟩ : S.Mbar)⁻¹ ∈
      timmesfeldOddCore S.Mbar) ∧ timmesfeldOddCore S.Mbar ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set tM : S.Mbar := ⟨t, S.Lbar_le_Mbar g ht⟩ with htM
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  have hto : orderOf tM = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext htt)
      (fun h => ht1 (congrArg Subtype.val h))
  have hiso : ∀ y : S.Mbar, (y * tM * y⁻¹) * tM = tM * (y * tM * y⁻¹) →
      y * tM * y⁻¹ = tM := by
    intro y hy
    apply Subtype.ext
    have h1 : (y : S.O) * t * (y : S.O)⁻¹ * t = t * ((y : S.O) * t * (y : S.O)⁻¹) :=
      congrArg Subtype.val hy
    exact isolated_of_omegaCase hCE H hNo C ht ht1 hVQ hΩ hN h8 y.2 h1
  have hZ := CFSG.ShultStronglyClosedTI.minimalLocalFailure_isolated_commutators_mem_oddCore hto
    hiso
  refine ⟨hZ, fun h0 => ?_⟩
  have hcen : ∀ y ∈ S.Mbar, y * t * y⁻¹ = t := by
    intro y hy
    have h1 : (⟨y, hy⟩ : S.Mbar) * tM * (⟨y, hy⟩ : S.Mbar)⁻¹ * tM⁻¹ ∈
        timmesfeldOddCore S.Mbar := hZ ⟨y, hy⟩
    rw [h0, mem_bot] at h1
    have h2 : y * t * y⁻¹ * t⁻¹ = 1 := congrArg Subtype.val h1
    exact mul_inv_eq_one.mp h2
  have hP := Setting.s12_noNormalTwo_Mbar S (zpowers t) (zpowers_le.mpr (S.Lbar_le_Mbar g ht))
    (IsPGroup.of_card (n := 1) (by rw [card_zpowers_eq_two H ht ht1, pow_one]))
    (fun m hm => S4.mem_normalizer_of_conj_le fun p hp => by
      rcases (mem_zpowers_iff_of_mem_Lbar H ht).mp hp with hp1 | hp1
      · rw [hp1, mul_one, mul_inv_cancel]
        exact one_mem _
      · rw [hp1, hcen m hm]
        exact mem_zpowers t)
  apply ht1
  have : t ∈ zpowers t := mem_zpowers t
  rwa [hP, mem_bot] at this

end Four

end CFSG.LargeExtraspecial.S7
