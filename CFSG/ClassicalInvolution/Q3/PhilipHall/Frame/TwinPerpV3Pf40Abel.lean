module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf17Exit
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf15Three
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMuPerp
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf8Class
public import CFSG.ClassicalInvolution.SmallCases.A7T22H51

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
open scoped commutatorElement

section Abel




variable {n : ℕ}

@[expose] def V3AbelianO2 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypS n Y R S t → ¬ TwoTwins R → ¬ TwinE4 Y →
      ∀ (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y),
        A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ →
          ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
            DbarConnected (CoreAssembly.conjClass (tightCore R)) W →
              ∀ (htC : t ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y))
                (htH : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) ∈
                  coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
                TightInO2 (QuotientGroup.mk'
                  (classicalInvolutionOddCore
                    ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)))
                  (⟨⟨t, htC⟩, htH⟩ :
                    ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))))

theorem v3Hyp51U3E8_of_abelianO2 (h : V3AbelianO2 n) : V3Hyp51U3E8 n := by
  intro Y _ _ R S t hP h3 hE K K' K₃ u₁ u₂ u₃ d _ W hW _ hconn
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one d.sq_12
  have hmem := tq_of_hyp22G d
  have htC : t ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    symm
    calc u₁ * u₂ * t = u₁ * (u₂ * t) := by group
      _ = u₁ * (t * u₂) := by rw [← d.comm_z₂]
      _ = (u₁ * t) * u₂ := by group
      _ = (t * u₁) * u₂ := by rw [← d.comm_z₁]
      _ = t * (u₁ * u₂) := by group
  have htcore : t ∈ TwinADescent.coreAt (u₁ * u₂) K₃ := by
    have hle : Subgroup.zpowers t ≤ K₃ ⊓ Subgroup.centralizer ({u₁ * u₂} : Set Y) :=
      Subgroup.zpowers_le.mpr ⟨d.hzK₃.mem, htC⟩
    exact le_tightCore_of_isPGroup hle
      (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one d.hz.sq)
      (Subgroup.mem_zpowers t)
  have htH : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) ∈
      coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) :=
    le_coreHull hmem (Subgroup.mem_subgroupOf.mpr htcore)
  exact hyp51At_of_tightInO2 d.hyp hc2 d.isElemAbelian_B (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp)) d.mul_ne_one d.hz.ne_one (Ne.symm d.mul_ne_z) htC htH
    (h Y R S t hP h3 hE K K' K₃ u₁ u₂ u₃ d W hW hconn htC htH)

@[expose] def V3ZStarSec (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypS n Y R S t → ¬ TwoTwins R → ¬ TwinE4 Y →
      ∀ (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y),
        A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ →
          (∃ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
            DbarConnected (CoreAssembly.conjClass (tightCore R)) W) →
            ∀ (htC : t ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y))
              (htH : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) ∈
                coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
              TightInO2 (QuotientGroup.mk'
                (classicalInvolutionOddCore
                  ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)))
                (⟨⟨t, htC⟩, htH⟩ :
                  ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)))) →
                t ∈ zStarOf (Subgroup.centralizer ({u₁ * u₂} : Set Y))

theorem v3ZStar_of_abelianO2 (hA : V3AbelianO2 n) (hZ : V3ZStarSec n) : V3ZStar n := by
  intro Y _ _ R S t hP h3 hE K K' K₃ u₁ u₂ u₃ d hμ
  have hC := CoreData.of_S hP.core
  have hPG := hC.partIHypG
  have hperp := kPerp_datum hP d.mem d.hz
  push Not at hμ
  obtain ⟨W, hW, hnW⟩ := hμ
  have hconn := dbarConnected_of_not_wyl hPG d hperp hW hnW
  have htC : t ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    symm
    calc u₁ * u₂ * t = u₁ * (u₂ * t) := by group
      _ = u₁ * (t * u₂) := by rw [← d.comm_z₂]
      _ = (u₁ * t) * u₂ := by group
      _ = (t * u₁) * u₂ := by rw [← d.comm_z₁]
      _ = t * (u₁ * u₂) := by group
  have hmem := tq_of_hyp22G d
  have htcore : t ∈ TwinADescent.coreAt (u₁ * u₂) K₃ := by
    have hle : Subgroup.zpowers t ≤ K₃ ⊓ Subgroup.centralizer ({u₁ * u₂} : Set Y) :=
      Subgroup.zpowers_le.mpr ⟨d.hzK₃.mem, htC⟩
    exact le_tightCore_of_isPGroup hle
      (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one d.hz.sq)
      (Subgroup.mem_zpowers t)
  have htH : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) ∈
      coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) :=
    le_coreHull hmem (Subgroup.mem_subgroupOf.mpr htcore)
  exact hZ Y R S t hP h3 hE K K' K₃ u₁ u₂ u₃ d ⟨W, hW, hconn⟩ htC htH
    (hA Y R S t hP h3 hE K K' K₃ u₁ u₂ u₃ d W hW hconn htC htH)

end Abel

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
