module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22BPf99

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.GX

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)
open scoped commutatorElement

section Frame




variable {n : ℕ}

theorem v3_secFrameU {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃)
    {K₄ : Subgroup Y} {a₃ a₄ y : Y} (fr : V3Frame R t K K' K₃ u₁ u₂ K₄ a₃ a₄ y) :
    ∃ (z τ : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)))
      (a b ε₀ : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) ⧸
          classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))),
      ((z : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y) = t ∧
      ((τ : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y) = y * t * y⁻¹ ∧
      TwinFrame (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
        (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃)
        (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄)
        (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) (conjSub y K₃))
        (QuotientGroup.mk' (classicalInvolutionOddCore
          ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) z) a b
        (QuotientGroup.mk' (classicalInvolutionOddCore
          ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) τ) ε₀ ∧
      QuotientGroup.mk' (classicalInvolutionOddCore
          ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) τ ≠
        QuotientGroup.mk' (classicalInvolutionOddCore
          ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) z ∧
      secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) (conjSub y K₄) ∈
        TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) ∧
      IsUniqueInvolution (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) (conjSub y K₄))
        (QuotientGroup.mk' (classicalInvolutionOddCore
          ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) τ) ∧
      secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) (conjSub y K₄) ≠
        secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) (conjSub y K₃) ∧
      (∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
        M ∈ omegaNbr (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
          (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) →
          M = secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄) ∧
      (∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
        M ∈ omegaNbr (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
          (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄) →
          M = secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) := by
  classical
  have hd := hStd.datum
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hd.hyp
  have hCd := CoreData.of_S hStd.perp.core
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.sq_12
  have h2 : ∀ M ∈ CoreAssembly.conjClass (tightCore R),
      IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hCd.datum.twoGroup)
  have hz₃ : IsUniqueInvolution K₃ t := hd.hzK₃
  have hz₄ : IsUniqueInvolution K₄ t := isUniqueInvolution_of_mem_twinSet hd.hz fr.hK₄
  have hz₃y : IsUniqueInvolution (conjSub y K₃) (y * t * y⁻¹) := hz₃.conj y
  have hz₄y : IsUniqueInvolution (conjSub y K₄) (y * t * y⁻¹) := hz₄.conj y
  obtain ⟨hK₃tq, hK₄tq⟩ := v3_tq_members_fr hStd fr
  have hK₃ytq : conjSub y K₃ ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) :=
    conjSub_mem_tqMembers3 hΩ.conjInvariant fr.hyc hK₃tq
  have hK₄ytq : conjSub y K₄ ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) :=
    conjSub_mem_tqMembers3 hΩ.conjInvariant fr.hyc hK₄tq
  have hcu3 : Commute (u₁ * u₂) a₃ :=
    (show Commute u₁ a₃ from fr.c13).mul_left (show Commute u₂ a₃ from fr.c23)
  have hcu4 : Commute (u₁ * u₂) a₄ :=
    (show Commute u₁ a₄ from fr.c14).mul_left (show Commute u₂ a₄ from fr.c24)
  have cut : (u₁ * u₂) * t = t * (u₁ * u₂) := by
    have h1 : Commute t u₁ := hd.comm_z₁
    have h2 : Commute t u₂ := hd.comm_z₂
    exact ((h1.symm).mul_left (h2.symm)).eq
  have hτ' : y * t * y⁻¹ = a₃ * a₄ * (u₁ * u₂) := by
    rw [fr.hy]
    calc u₁ * u₂ * a₃ * a₄ = a₃ * (u₁ * u₂) * a₄ := by rw [hcu3.eq]
      _ = a₃ * ((u₁ * u₂) * a₄) := by group
      _ = a₃ * (a₄ * (u₁ * u₂)) := by rw [hcu4.eq]
      _ = a₃ * a₄ * (u₁ * u₂) := by group
  have hcτ : Commute (u₁ * u₂) (y * t * y⁻¹) := by
    rw [fr.hy]
    exact ((Commute.refl (u₁ * u₂)).mul_right hcu3).mul_right hcu4
  have htC : t ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr cut.symm
  have ha₃C : a₃ ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcu3.eq.symm
  have ha₄C : a₄ ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcu4.eq.symm
  have hτC : y * t * y⁻¹ ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcτ.eq.symm
  have hτ2 : (y * t * y⁻¹) * (y * t * y⁻¹) = 1 := by
    calc y * t * y⁻¹ * (y * t * y⁻¹) = y * (t * t) * y⁻¹ := by group
      _ = 1 := by rw [hd.hz.sq]; group
  have hS := layer_q8Section hStd.perp hd.sq_12
  have hlt := card_layer_lt hStd.perp hd.mul_ne_one
  have hp3 : IsPGroup 2 (Subgroup.zpowers a₃) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, fr.o3]; norm_num)
  have hp4 : IsPGroup 2 (Subgroup.zpowers a₄) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, fr.o4]; norm_num)
  have hcoreT : t ∈ TwinADescent.coreAt (u₁ * u₂) K₃ :=
    le_tightCore_of_isPGroup (V := Subgroup.zpowers t)
      (le_inf (Subgroup.zpowers_le.mpr hz₃.mem) (Subgroup.zpowers_le.mpr htC))
      (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hz.sq)
      (Subgroup.mem_zpowers t)
  have hcoreA₃ : a₃ ∈ TwinADescent.coreAt (u₁ * u₂) K₃ :=
    le_tightCore_of_isPGroup (V := Subgroup.zpowers a₃)
      (le_inf (Subgroup.zpowers_le.mpr fr.h3) (Subgroup.zpowers_le.mpr ha₃C)) hp3
      (Subgroup.mem_zpowers a₃)
  have hcoreA₄ : a₄ ∈ TwinADescent.coreAt (u₁ * u₂) K₄ :=
    le_tightCore_of_isPGroup (V := Subgroup.zpowers a₄)
      (le_inf (Subgroup.zpowers_le.mpr fr.h4) (Subgroup.zpowers_le.mpr ha₄C)) hp4
      (Subgroup.mem_zpowers a₄)
  have hcoreτ : y * t * y⁻¹ ∈ TwinADescent.coreAt (u₁ * u₂) (conjSub y K₃) :=
    le_tightCore_of_isPGroup (V := Subgroup.zpowers (y * t * y⁻¹))
      (le_inf (Subgroup.zpowers_le.mpr hz₃y.mem) (Subgroup.zpowers_le.mpr hτC))
      (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hτ2)
      (Subgroup.mem_zpowers _)
  obtain ⟨wH, hwHv, hwHm⟩ := TwinPerp23.exists_hull_elt hK₃tq hcoreT
  obtain ⟨a₃H, ha₃Hv, ha₃Hm⟩ := TwinPerp23.exists_hull_elt hK₃tq hcoreA₃
  obtain ⟨a₄H, ha₄Hv, ha₄Hm⟩ := TwinPerp23.exists_hull_elt hK₄tq hcoreA₄
  obtain ⟨τH, hτHv, hτHm⟩ := TwinPerp23.exists_hull_elt hK₃ytq hcoreτ
  set N := classicalInvolutionOddCore
    ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) with hN
  have hv : ∀ x y' : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
      (((x * y' : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) :
        ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y) =
        ((x : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y) *
          ((y' : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y) := fun _ _ => rfl
  have hext : ∀ x y' : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
      ((x : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y) =
        ((y' : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y) → x = y' :=
    fun x y' h => Subtype.ext (Subtype.ext h)
  obtain ⟨eH, heH⟩ : ∃ eH : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
      eH = (a₃H * a₄H)⁻¹ * τH := ⟨_, rfl⟩
  have heHv : ((eH : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y) = u₁ * u₂ := by
    have h1 : (((a₃H * a₄H : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) :
        ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y) = a₃ * a₄ := by
      rw [hv, ha₃Hv, ha₄Hv]
    have h2 : ((((a₃H * a₄H)⁻¹ : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) :
        ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y) = (a₃ * a₄)⁻¹ := by
      rw [← h1]; rfl
    rw [heH]
    show ((((a₃H * a₄H)⁻¹ : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) :
        ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y) *
      ((τH : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y) = u₁ * u₂
    rw [h2, hτHv, hτ']
    group
  have hrelH : τH = a₃H * a₄H * eH := by rw [heH]; group
  have hecen : QuotientGroup.mk' N eH ∈ Subgroup.center (↥(coreHull (CoreAssembly.conjClass
      (tightCore R)) (u₁ * u₂)) ⧸ N) := by
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective N x
    rw [← map_mul, ← map_mul]
    congr 1
    apply hext
    rw [hv, hv, heHv]
    exact Subgroup.mem_centralizer_singleton_iff.mp y'.1.2
  have he2' : eH * eH = 1 := by
    apply hext
    rw [hv, heHv]
    exact hd.sq_12
  have he1' : QuotientGroup.mk' N eH ≠ 1 := by
    intro h1
    have hmem : eH ∈ N := (QuotientGroup.eq_one_iff _).mp h1
    have := CFSG.ClassicalInvolution.Asc77.T7H.eq_one_of_mem_odd_of_sq
      (CFSG.ComponentClassification.OddCore.odd_card _) hmem he2'
    apply hd.mul_ne_one
    have := congrArg (fun x : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) =>
      ((x : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y)) this
    simpa [heHv] using this
  obtain ⟨htC₁, htY₁, hzA⟩ := isUniqueInvolution_secImg hΩ hc2 hK₃tq hz₃
  obtain ⟨htC₂, htY₂, hzA'⟩ := isUniqueInvolution_secImg hΩ hc2 hK₄tq hz₄
  obtain ⟨hτC₃, hτY₃, hτA⟩ := isUniqueInvolution_secImg hΩ hc2 hK₃ytq hz₃y
  obtain ⟨hτC₄, hτY₄, hτA'⟩ := isUniqueInvolution_secImg hΩ hc2 hK₄ytq hz₄y
  have hwHeq : wH = ⟨⟨t, htC₁⟩, htY₁⟩ := hext _ _ hwHv
  have hτHeq : τH = ⟨⟨y * t * y⁻¹, hτC₃⟩, hτY₃⟩ := hext _ _ hτHv
  have hzA₁ : IsUniqueInvolution (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃)
      (QuotientGroup.mk' N wH) := by rw [hwHeq]; exact hzA
  have hzA₂ : IsUniqueInvolution (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄)
      (QuotientGroup.mk' N wH) := by rw [hwHeq]; exact hzA'
  have hτA₃ : IsUniqueInvolution
      (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) (conjSub y K₃))
      (QuotientGroup.mk' N τH) := by rw [hτHeq]; exact hτA
  have hτA₄ : IsUniqueInvolution
      (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) (conjSub y K₄))
      (QuotientGroup.mk' N τH) := by rw [hτHeq]; exact hτA'
  have hta₃ : Commute t a₃ := hz₃.commute_of_mem fr.h3
  have hta₄ : Commute t a₄ := hz₄.commute_of_mem fr.h4
  have htτ : t * (y * t * y⁻¹) = (y * t * y⁻¹) * t := by
    rw [fr.hy]
    exact ((((show Commute t (u₁ * u₂) from cut.symm).mul_right hta₃).mul_right hta₄)).eq
  have hτne : QuotientGroup.mk' N τH ≠ QuotientGroup.mk' N wH := by
    intro h
    have := TwinPerp23.eq_of_mk_eq_of_involutions (x := τH) (y := wH)
      (hext _ _ (by rw [hv, hτHv]; exact hτ2)) (hext _ _ (by rw [hv, hwHv]; exact hz₃.sq))
      (hext _ _ (by rw [hv, hv, hτHv, hwHv]; exact htτ.symm)) h
    have hval := congrArg
      (fun x : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) =>
        ((x : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y)) this
    simp only [hτHv, hwHv] at hval
    exact fr.hne hval
  have hperp3 := kPerp_datum hStd.perp hd.hK₃.1 hd.hzK₃
  have hK₄ := fr.hK₄
  have h41 := fr.h41
  have h42 := fr.h42
  have h43 := fr.h43
  have hp3' := v3_perp_tq hStd hd.hK₃ hK₄ (Ne.symm h43) hd.hK₃K hd.hK₃K' h41 h42
  have hp4' := v3_perp_tq hStd hK₄ hd.hK₃ h43 h41 h42 hd.hK₃K hd.hK₃K'
  have hnb : ∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      M ∈ omegaNbr (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
        (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) →
      M = secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄ := by
    intro M hM hn
    obtain ⟨J, hJq, rfl⟩ := exists_of_mem_secFam hM
    exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2 hK₃tq hJq (K' := K₄)
      (fun J₀ hJ₀ hJ₀p => hp3' J₀ hJ₀ (by rw [hperp3] at *; exact hJ₀p)) hn
  have hnb' : ∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      M ∈ omegaNbr (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
        (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄) →
      M = secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃ := by
    intro M hM hn
    obtain ⟨J, hJq, rfl⟩ := exists_of_mem_secFam hM
    exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2 hK₄tq hJq (K' := K₃)
      (fun J₀ hJ₀ hJ₀p => hp4' J₀ hJ₀ hJ₀p) hn
  have hBA : secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) (conjSub y K₃) ≠
      secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃ := by
    intro h
    rw [h] at hτA₃
    exact hτne (hτA₃.eq hzA₁)
  have hBA' : secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) (conjSub y K₃) ≠
      secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄ := by
    intro h
    rw [h] at hτA₃
    exact hτne (hτA₃.eq hzA₂)
  have hne_img : secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃ ≠
      secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄ :=
    TwinPerp23.secImg_ne_of_twins hΩ hc2 hK₃tq hK₄tq h43 hz₃ hz₄
  have hne_img' : secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) (conjSub y K₃) ≠
      secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) (conjSub y K₄) :=
    TwinPerp23.secImg_ne_of_twins hΩ hc2 hK₃ytq hK₄ytq (fun h => h43 (by
      have := congrArg (conjSub y⁻¹) h
      rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this)) hz₃y hz₄y
  have sq₃ : a₃ * a₃ = t := T7A.sq_eq_of_orderOf_four hd.hzK₃ fr.h3 fr.o3
  have sq₄ : a₄ * a₄ = t := T7A.sq_eq_of_orderOf_four hz₄ fr.h4 fr.o4
  refine ⟨wH, τH, QuotientGroup.mk' N a₃H, QuotientGroup.mk' N a₄H, QuotientGroup.mk' N eH, hwHv, hτHv,
    ⟨secImg_mem_secFam hK₃tq, secImg_mem_secFam hK₄tq, secImg_mem_secFam hK₃ytq, hne_img, hzA₁, hzA₂,
      ha₃Hm, ha₄Hm, ?_, ?_, hτA₃, hecen, ?_, he1', ?_⟩, hτne, secImg_mem_secFam hK₄ytq, hτA₄,
    hne_img'.symm, hnb, hnb'⟩
  · rw [← map_mul]
    congr 1
    apply hext
    rw [hv, ha₃Hv, hwHv]
    exact sq₃
  · rw [← map_mul]
    congr 1
    apply hext
    rw [hv, ha₄Hv, hwHv]
    exact sq₄
  · rw [← map_mul, he2', map_one]
  · rw [← map_mul, ← map_mul, ← hrelH]

end Frame

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.GX
