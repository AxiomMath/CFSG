module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22Q

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

section

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

variable {n : ℕ}

@[expose] def V3LayerGenExConjAd (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y), V3Std n Y R S t K K' K₃ u₁ u₂ u₃ →
      ∀ (K₄ : Subgroup Y) (a₃ a₄ y : Y), V3Frame R t K K' K₃ u₁ u₂ K₄ a₃ a₄ y →
        ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)), u₁ ∈ W → u₂ ∈ W → a₃ ∈ W → a₄ ∈ W →
        ¬ SecNoExitAt (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) →
          (∃ x : LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
            conjSub x (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) =
              secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄) →
          rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) ≤
            ((rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) ⊓
                Subgroup.centralizer ({t} : Set Y)) ⊔
              (rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) ⊓
                Subgroup.centralizer ({y * t * y⁻¹} : Set Y))) ⊔
              oddCoreOf (rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))

theorem v3LayerGen_of_nonconj (h4 : Thm4RTwinBelow 3 n) {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y}
    (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃) {K₄ : Subgroup Y} {a₃ a₄ y : Y}
    (fr : V3Frame R t K K' K₃ u₁ u₂ K₄ a₃ a₄ y)
    (hnc : ¬ ∃ x : LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
        conjSub x (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) =
          secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄) :
    rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) ≤
      ((rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) ⊓
          Subgroup.centralizer ({t} : Set Y)) ⊔
        (rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) ⊓
          Subgroup.centralizer ({y * t * y⁻¹} : Set Y))) ⊔
        oddCoreOf (rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) := by
  classical
  have hd := hStd.datum
  have hΩ := hd.hyp
  have hCd := CoreData.of_S hStd.perp.core
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.sq_12
  have h2 : ∀ M ∈ CoreAssembly.conjClass (tightCore R),
      IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hCd.datum.twoGroup)
  have hmap := coreHull_map_eq_rLayer hΩ hc2 h2
  obtain ⟨hmem, hmem4⟩ := v3_tq_members_fr hStd fr
  have hz3 : IsUniqueInvolution K₃ t := hd.hzK₃
  have hz4 : IsUniqueInvolution K₄ t := isUniqueInvolution_of_mem_twinSet hd.hz fr.hK₄
  have hM' : conjSub y K₃ ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) :=
    conjSub_mem_tqMembers3 hΩ.conjInvariant fr.hyc hmem
  obtain ⟨htC, htY, hinv3⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2 hmem hz3
  obtain ⟨htC4, htY4, hinv4⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2 hmem4 hz4
  obtain ⟨hτC, hτY, hinvτ⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2 hM' (hz3.conj y)
  have hτ2 : (y * t * y⁻¹) * (y * t * y⁻¹) = 1 := by
    calc y * t * y⁻¹ * (y * t * y⁻¹) = y * (t * t) * y⁻¹ := by group
      _ = 1 := by rw [hd.hz.sq]; group
  have hS := layer_q8Section hStd.perp hd.sq_12
  have hlt := card_layer_lt hStd.perp hd.mul_ne_one
  have hp3 := v3_perp_tq hStd hd.hK₃ fr.hK₄ (Ne.symm fr.h43) hd.hK₃K hd.hK₃K' fr.h41 fr.h42
  have hp4 := v3_perp_tq hStd fr.hK₄ hd.hK₃ fr.h43 fr.h41 fr.h42 hd.hK₃K hd.hK₃K'
  have hperp3 := kPerp_datum hStd.perp hd.hK₃.1 hd.hzK₃
  have hnb : ∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      M ∈ omegaNbr (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
        (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) →
      M = secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄ := by
    intro M hM hn
    obtain ⟨J, hJq, rfl⟩ := exists_of_mem_secFam hM
    exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2 hmem hJq (K' := K₄)
      (fun J₀ hJ₀ hJ₀p => hp3 J₀ hJ₀ (by rw [hperp3] at *; exact hJ₀p)) hn
  have hnb' : ∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      M ∈ omegaNbr (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
        (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄) →
      M = secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃ := by
    intro M hM hn
    obtain ⟨J, hJq, rfl⟩ := exists_of_mem_secFam hM
    exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2 hmem4 hJq (K' := K₃)
      (fun J₀ hJ₀ hJ₀p => hp4 J₀ hJ₀ hJ₀p) hn
  have h4' := h4 _ hlt _ hS.hyp hS.two hS.q8 hS.aEmpty hS.oddFree
  have hA := secImg_mem_secFam hmem
  have hA' := secImg_mem_secFam hmem4
  have hcA : ∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      (¬ ∃ g : LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
        conjSub g (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) = M) →
      M = secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄ := by
    intro M hM hnot
    have hMA : M ≠ secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃ :=
      fun h => hnot ⟨1, by rw [conjSub_one, h]⟩
    exact hnb M hM (MuTab.mem_omegaNbr_of_commutes hM hMA (h4' _ hA M hM hnot))
  have hcA' : ∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      (¬ ∃ g : LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
        conjSub g (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄) = M) →
      M = secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃ := by
    intro M hM hnot
    have hMA : M ≠ secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄ :=
      fun h => hnot ⟨1, by rw [conjSub_one, h]⟩
    exact hnb' M hM (MuTab.mem_omegaNbr_of_commutes hM hMA (h4' _ hA' M hM hnot))
  have hall : ∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      M = secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃ ∨
        M = secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄ := by
    intro M hM
    by_cases hg : ∃ g : LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
        conjSub g (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) = M
    · left
      obtain ⟨g, hg⟩ := hg
      apply hcA' M hM
      rintro ⟨g', hg'⟩
      exact hnc ⟨g'⁻¹ * g, by rw [conjSub_mul, hg, ← hg', conjSub_inv_conjSub]⟩
    · right
      exact hcA M hM hg
  have hcentA : ∀ w ∈ secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃,
      (QuotientGroup.mk (⟨⟨t, htC⟩, htY⟩ :
          ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) :
        LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) * w = w * QuotientGroup.mk
          (⟨⟨t, htC⟩, htY⟩ : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) :=
    fun w hw => hinv3.commute_of_mem hw
  have hcentA' : ∀ w ∈ secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄,
      (QuotientGroup.mk (⟨⟨t, htC⟩, htY⟩ :
          ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) :
        LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) * w = w * QuotientGroup.mk
          (⟨⟨t, htC⟩, htY⟩ : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) :=
    fun w hw => hinv4.commute_of_mem hw
  have hle : (⊤ : Subgroup (LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) ≤
      Subgroup.centralizer ({(QuotientGroup.mk (⟨⟨t, htC⟩, htY⟩ :
          ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) :
        LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))} :
        Set (LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) := by
    rw [← hS.gen]
    unfold omegaGen
    refine iSup₂_le fun M hM => ?_
    rcases hall M hM with rfl | rfl
    · intro w hw
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hcentA w hw).symm
    · intro w hw
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hcentA' w hw).symm
  refine layer_le_of_sec_gen hmap (⟨⟨t, htC⟩, htY⟩ :
      ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)))
    (⟨⟨y * t * y⁻¹, hτC⟩, hτY⟩ : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) rfl rfl
    hd.hz.sq hτ2 ?_
  intro g
  exact Subgroup.mem_sup_left (hle (Subgroup.mem_top g))

theorem v3LayerGenExAd_of_conj (h4 : Thm4RTwinBelow 3 n) (h : V3LayerGenExConjAd n) :
    V3LayerGenExAd n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ hStd K₄ a₃ a₄ y fr W hW hu₁ hu₂ ha₃ ha₄ hno
  by_cases hc : ∃ x : LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      conjSub x (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) =
        secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄
  · exact h Y R S t K K' K₃ u₁ u₂ u₃ hStd K₄ a₃ a₄ y fr W hW hu₁ hu₂ ha₃ ha₄ hno hc
  · exact v3LayerGen_of_nonconj h4 hStd fr hc

theorem v3LayerGenAllC_of_exitConj (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (h4 : Thm4RTwinBelow 3 n) (h : V3LayerGenExConjAd n) : V3LayerGenAllC n :=
  v3LayerGenAllC_of_exit hcit hP h4 (v3LayerGenExAd_of_conj h4 h)

end

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
