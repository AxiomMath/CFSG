module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf5Gen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)

section Trans





variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem secImgR_eq_secImg (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {J : Subgroup G}
    (hJ : J ∈ tqMembers3 Ω c) {R : Subgroup G} (hR : IsSylow2In R J)
    (hRc : R ≤ Subgroup.centralizer ({c} : Set G)) (h2 : IsPGroup 2 (secImg Ω c J)) :
    secImgR Ω c R = secImg Ω c J := by
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set H := coreHull Ω c with hH
  have hN : Odd (Nat.card (classicalInvolutionOddCore ↥H)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥H
  have hRs : IsSylow2In R (TwinADescent.coreAt c J) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hJ.2).mpr ⟨hR, hRc⟩
  have hsP : IsSylow2In ((R.subgroupOf C).subgroupOf H)
      (((TwinADescent.coreAt c J).subgroupOf C).subgroupOf H) :=
    (hRs.subgroupOf (TwinADescent.coreAt_le_centralizer c J)).subgroupOf (le_coreHull hJ)
  have hs := isSylow2In_map_mk hN hsP
  exact (hs.2.2 _ le_rfl h2 hs.1).symm

variable {n : ℕ}

@[expose] def V3LayerTransitive (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y), V3Std n Y R S t K K' K₃ u₁ u₂ u₃ →
      ∀ K₄ : Subgroup Y,
        FourthTwin (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ K₄ →
          SecNoExitAt (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) →
            (∀ J ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂), IsPGroup 2 J) →
            HasLifts (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) →
            ExactSylow (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) →
            Nonempty (OmegaLieU 3 1 (liftFam (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R))
              (u₁ * u₂)))) →
              (∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
                ∀ N ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
                  ∃ x : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) ⧸
                      classicalInvolutionOddCore
                        ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
                    conjSub x M = N) ∧
                secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃ ≠
                  secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄

theorem v3LayerTrans_of_transitive (hT : V3LayerTransitive n) : V3LayerTrans n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ hStd K₄ hF hno h2' hl hex hLie R₃ R₄ h3 h4 c3 c4
  obtain ⟨htr, -⟩ := hT Y R S t K K' K₃ u₁ u₂ u₃ hStd K₄ hF hno h2' hl hex hLie
  have hd := hStd.datum
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.sq_12
  obtain ⟨hmem, hmem4⟩ := v3_tq_members hStd hF
  have e3 := secImgR_eq_secImg hc2 hmem h3 c3 (h2' _ (secImg_mem_secFam hmem))
  have e4 := secImgR_eq_secImg hc2 hmem4 h4 c4 (h2' _ (secImg_mem_secFam hmem4))
  refine ⟨fun M hM => ?_, ?_⟩
  · obtain ⟨x, hx⟩ := htr _ (secImg_mem_secFam hmem) M hM
    rw [e3]
    exact hx ▸ le_iSup (fun x => conjSub x (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃)) x
  · obtain ⟨x, hx⟩ := htr _ (secImg_mem_secFam hmem) _ (secImg_mem_secFam hmem4)
    exact ⟨x, by rw [e3, e4]; exact hx⟩

end Trans

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
