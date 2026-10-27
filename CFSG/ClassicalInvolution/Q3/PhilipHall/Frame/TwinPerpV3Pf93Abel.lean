module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf40Abel
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf4Layer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf81Conn

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Balance (oddQuotMk)
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)

section Abel


variable {n : ℕ}

theorem tightInO2_of_central {X : Type} [Group X] {z : X} (hz2 : z * z = 1)
    (hc : ∀ y, y * z = z * y) : TightInO2 z := by
  refine ⟨Subgroup.zpowers z, ?_, CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hz2,
    Subgroup.mem_zpowers z⟩
  refine ⟨fun m hm g => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
  have h : g * z ^ k = z ^ k * g := ((show Commute g z from hc g).zpow_right k).eq
  rw [h, mul_assoc, mul_inv_cancel, mul_one]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) k

@[expose] def V3AbelianO2Tr (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypS n Y R S t → ¬ TwoTwins R → ¬ TwinE4 Y →
      ∀ (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y),
        A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ →
          ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
            DbarConnected (CoreAssembly.conjClass (tightCore R)) W →
              ∀ (htC : t ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y))
                (htH : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) ∈
                  coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
                (∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
                  ∀ N ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
                    ∃ g, conjSub g M = N) →
                ¬ T3.DStarConnected
                  (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) →
                  TightInO2 (QuotientGroup.mk'
                    (classicalInvolutionOddCore
                      ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)))
                    (⟨⟨t, htC⟩, htH⟩ :
                      ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))))

theorem v3AbelianO2_of_tr (h4 : Thm4RTwinBelow 3 n) (h : V3AbelianO2Tr n) : V3AbelianO2 n := by
  classical
  intro Y _ _ R S t hP h3 hE K K' K₃ u₁ u₂ u₃ d W hW hconnW htC htH
  have hC := CoreData.of_S hP.core
  have hPG := hC.partIHypG
  have hΩ := d.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one d.sq_12
  have hK₃tq := tq_of_hyp22G d
  have hperp3 := kPerp_datum hP d.hK₃.1 d.hzK₃
  have hSig := dstarComp_subset_twinSet_of_conn hPG d.hK₃.1 d.hzK₃ hperp3 hW hconnW
  have hS := layer_q8Section hP d.sq_12
  have hlt := card_layer_lt hP d.mul_ne_one
  have hex : ∀ J ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      ∃ u' : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) ⧸
        classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
      IsUniqueInvolution (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) J) u' := by
    intro J hJ
    obtain ⟨⟨z, hz⟩, -⟩ := hS.hyp.omega1 _ (secImg_mem_secFam hJ)
    exact ⟨z, hz⟩
  have hcent : (∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      IsUniqueInvolution M (QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)))
        (⟨⟨t, htC⟩, htH⟩ :
          ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))))) →
      TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)))
        (⟨⟨t, htC⟩, htH⟩ :
          ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)))) := fun hall =>
    tightInO2_of_central
      (isUniqueInvolution_secImg_mk hK₃tq (hex K₃ hK₃tq) d.hzK₃ htC).sq
      (central_of_allMembers hS.gen hall)
  rcases dichotomy_of_thm4RTwin h4 hlt hS.hyp hS.two hS.q8 hS.aEmpty hS.oddFree
      (secImg_mem_secFam hK₃tq) with hd | htr
  · exact hcent (allMembers_involution_of_connected hΩ hc2 hex hK₃tq d.hzK₃ htC htH hSig hd)
  by_cases hconn : T3.DStarConnected (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
  · exact hcent (allMembers_involution_of_connected hΩ hc2 hex hK₃tq d.hzK₃ htC htH hSig
      (fun M hM => hconn _ (secImg_mem_secFam hK₃tq) M hM))
  have htrans : ∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      ∀ N ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
        ∃ g, conjSub g M = N := by
    intro M hM N hN
    obtain ⟨a, ha⟩ := htr M hM
    obtain ⟨b, hb⟩ := htr N hN
    refine ⟨b * a⁻¹, ?_⟩
    rw [← hb, ← ha, ← conjSub_mul]
    congr 1
    group
  exact h Y R S t hP h3 hE K K' K₃ u₁ u₂ u₃ d W hW hconnW htC htH htrans hconn

end Abel

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
