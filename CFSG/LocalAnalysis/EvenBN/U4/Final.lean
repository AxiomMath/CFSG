module

public import CFSG.LocalAnalysis.EvenBN.U4.Main
public import CFSG.LocalAnalysis.EvenBN.U4.CaseOneFinal
public import CFSG.LocalAnalysis.EvenBN.U4.CaseTwoCenter
public import CFSG.LocalAnalysis.EvenBN.U4.CaseTwoEleven
public import CFSG.LocalAnalysis.EvenBN.U4.CaseTwoRootTwo
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate119
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate122
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate3951
public import Certificates.Certificate9130

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped MatrixGroups


namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem false_of_case_two (hS : Setting h L η t Q T) {k : Type} [Field k] [Fintype k]
    (hk : Fintype.card k = 2 ^ f) (ψ : miyamotoM2G h L η t Q ≃* SL(2, k) × SL(2, k))
    (α : miyamotoN2G h L η ≃* SL(2, k))
    (hψα : ∀ (a : miyamotoN2G h L η) (x : miyamotoM2G h L η t Q), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM2G h L η t Q) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁)) : False := by
  obtain ⟨k₁, _, _, hk₁, ψ₁, α₁, hψA, hψt₁⟩ := hS.sec3_15_iso
  have hZ := hS.card_centerIn_U_gt_of_case_two hk₁ hψA hψt₁ hk ψ
  obtain ⟨D, hWD, hr₂, hcomm, hinf, hδ⟩ := hS.exists_D hk₁ hψA hψt₁ hZ hk ψ α hψα hψt
  exact hS.false_of_D hk₁ hψA hψt₁ hZ hWD hr₂ hcomm hinf hδ

end Setting

theorem simpleStatement : SimpleStatement := by
  intro G _ _ _ hnonab L f hf hL _ hcore S hS hm
  obtain ⟨K, _, h, η, t, Q, T, hSet⟩ := exists_setting hnonab hf hL hcore S hS hm
  rcases hSet.sec3_12_two_iso_all.or with ⟨k, _, _, hk, ψ, α, hψα, hψt⟩ |
      ⟨k₂, _, _, hk₂, ψ₂, -, -⟩
  · exact hSet.false_of_case_two hk ψ α hψα hψt
  · exact hSet.false_of_case_one hk₂ ψ₂

theorem bnFamily_PSU4 :
    ComponentInitial.EvenResidual.BNFamilyStatement
      fun X _ => ∃ f : ℕ, 2 ≤ f ∧ CFSG.Blueprint.LieModel X .PSU 4 2 f :=
  bnFamily_PSU4_of_simple simpleStatement

end CFSG.LocalAnalysis.EvenBN.U4
