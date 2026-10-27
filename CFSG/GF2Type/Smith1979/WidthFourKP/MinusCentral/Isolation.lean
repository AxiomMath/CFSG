module

public import CFSG.GF2Type.Smith1979.WidthFourKP.MinusCentral.OmegaThree
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaMinusSchur

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4MinusC

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions Equiv
open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6
open CFSG.LargeExtraspecial.S7 CFSG.LargeExtraspecial.OrthoF2 CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

section Isolation

variable (hw : S.width = 4) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hΩ : OmegaCase H C ht ht1 hVQ) (h4 : finrank (ZMod 2) (Vt S g t) = 4)
  (h67 : Orbit67 S g t)
  (hSC : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ = t)
include hw H hNo C ht ht1 hVQ hΩ h4 h67 hSC

theorem isolated_w4 {x : S.O} (hx : x ∈ S.Mbar)
    (hcomm : x * t * x⁻¹ * t = t * (x * t * x⁻¹)) : x * t * x⁻¹ = t := by
  by_contra hne
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hx
  set E : S.Qt ≃ₗ[ZMod 2] S.Qt := (t : S.Qt ≃ₗ[ZMod 2] S.Qt) with hE
  set E₁ : S.Qt ≃ₗ[ZMod 2] S.Qt :=
    ((S.ρ k * t * (S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with hE₁
  obtain ⟨hcV, hfW⟩ := commSpace_t_eq H C ht ht1 hVQ
  have hWV : Wt S g t = Vt S g t := W4Minus.Wt_eq_Vt_w4 hw H ht1 h4
  obtain ⟨Q, -, -, -, -, hsing⟩ := hΩ.exists_form
  set U : Submodule (ZMod 2) (Vt S g t) := (commSpace E₁).comap (Vt S g t).subtype with hU
  have hanis : ∀ w ∈ U, Q w = 0 → w = 0 := by
    intro w hw' hQw
    by_contra hw0
    have hwo := (hsing w hw0).mp hQw
    rw [mem_orbitOf_RmodN_iff H.conj_mem ht] at hwo
    obtain ⟨h, hh, hwh⟩ := exists_of_mem_orbit hwo H.conj_mem
    have hw'' : (w : S.Qt) ∈ commSpace E₁ := hw'
    rw [hE₁, S7.commSpace_conj] at hw''
    obtain ⟨v, hv, hvw⟩ := hw''
    have hmem : (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)) ∈ Vt S g t := by
      rw [← hwh, ← hvw, LinearEquiv.coe_coe, inv_apply_apply_O, ← hcV]
      exact hv
    exact hne (strongClosed_mul H hSC hh ⟨k, rfl⟩
      (conj_mem_Lbar_of_inv_apply_mem H ht h67 k h hmem))
  have hU2 := finrank_le_two_of_anisotropic Q hanis
  have hdU : finrank (ZMod 2) U = finrank (ZMod 2) ↥(Vt S g t ⊓ commSpace E₁) := by
    rw [← Submodule.finrank_map_subtype_eq, hU, Submodule.map_comap_subtype]
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
  have hEE' : ∀ v, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (E₁ v) = E₁ ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := hEE
  have hle : (Vt S g t).map ((E₁ : S.Qt →ₗ[ZMod 2] S.Qt) - 1) ≤ Vt S g t ⊓ commSpace E₁ := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨?_, ⟨v, rfl⟩⟩
    rw [← hcV] at hv ⊢
    obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
    refine mem_commSpace.mpr ⟨E₁ w - w, ?_⟩
    simp only [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, map_sub, hEE']
  have hrk := S2.finrank_map_sub_one_add E (commSpace E₁)
  rw [hmap, hfW, hWV, inf_comm] at hrk
  have hd₁ : finrank (ZMod 2) (commSpace E₁) = finrank (ZMod 2) (Vt S g t) := by
    rw [hE₁, S7.commSpace_conj, LinearEquiv.finrank_map_eq, hcV]
  set t₁ : S.O := S.ρ k * t * (S.ρ k)⁻¹ with ht₁
  have ht₁C : t₁ ∈ S8.CMt S t :=
    S8.mem_CMt.mpr ⟨mul_mem (mul_mem (MonoidHom.mem_range.mpr ⟨k, rfl⟩) (S.Lbar_le_Mbar g ht))
      (inv_mem (MonoidHom.mem_range.mpr ⟨k, rfl⟩)), hcomm⟩
  set φ := S8.resCV S g H.conj_mem t ⟨t₁, ht₁C⟩ with hφ
  have hφO : φ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    W4As.resCV_mem_orthogonalGroup_omega H hNo C ht ht1 hVQ hΩ hsing _
  have htt : t * t = 1 := S4.mul_self_of_mem_Lbar S H.conj_mem ht
  have ht₁t₁ : t₁ * t₁ = 1 := by
    rw [ht₁]
    calc S.ρ k * t * (S.ρ k)⁻¹ * (S.ρ k * t * (S.ρ k)⁻¹) = S.ρ k * (t * t) * (S.ρ k)⁻¹ := by
          group
      _ = 1 := by rw [htt, mul_one, mul_inv_cancel]
  have hφ2 : φ * φ = 1 := by
    rw [hφ, ← map_mul]
    have : (⟨t₁, ht₁C⟩ : S8.CMt S t) * ⟨t₁, ht₁C⟩ = 1 := Subtype.ext ht₁t₁
    rw [this, map_one]
  set W' : Submodule (ZMod 2) (Vt S g t) :=
    ((Vt S g t).map ((E₁ : S.Qt →ₗ[ZMod 2] S.Qt) - 1)).comap (Vt S g t).subtype with hW'
  have hW'U : W' ≤ U := fun w hw' => (hle hw').2
  have hW'fin : finrank (ZMod 2) W' =
      finrank (ZMod 2) ((Vt S g t).map ((E₁ : S.Qt →ₗ[ZMod 2] S.Qt) - 1)) := by
    rw [← Submodule.finrank_map_subtype_eq, hW', Submodule.map_comap_subtype,
      inf_eq_right.mpr (hle.trans inf_le_left)]
  have hW'iso : ∀ w ∈ W', ∀ w' ∈ W', QuadraticMap.polar Q w w' = 0 := by
    have hform : ∀ w ∈ W', ∃ v : Vt S g t, w = φ v - v := by
      intro w hw'
      obtain ⟨v, hv, hvw⟩ := hw'
      refine ⟨⟨v, hv⟩, Subtype.ext ?_⟩
      have hvw' : (w : S.Qt) = ((E₁ : S.Qt →ₗ[ZMod 2] S.Qt) - 1) v := hvw.symm
      rw [hvw']
      rfl
    intro w hw' w' hw''
    obtain ⟨v, rfl⟩ := hform w hw'
    obtain ⟨v', rfl⟩ := hform w' hw''
    exact polar_sub_sub_eq_zero hφO hφ2 v v'
  have ha1 := finrank_le_one_of_anisotropic_of_isotropic (Q := Q)
    (fun w hw' => hanis w (hW'U hw')) hW'iso
  have h3 := Submodule.finrank_mono hle
  omega

theorem comm_mem_Obar_w4 {x : S.O} (hx : x ∈ S.Mbar) : x * t * x⁻¹ * t⁻¹ ∈ Obar S := by
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
    exact isolated_w4 hw H hNo C ht ht1 hVQ hΩ h4 h67 hSC y.2 h1
  have hZ := CFSG.ShultStronglyClosedTI.minimalLocalFailure_isolated_commutators_mem_oddCore hto
    hiso
  exact ⟨_, hZ ⟨x, hx⟩, rfl⟩

end Isolation

end CFSG.GF2Type.Smith1979.W4MinusC
