module

public import CFSG.ClassicalInvolution.SmallCases.NDBStmt
public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootTwinMain
public import CFSG.ClassicalInvolution.Asc77.WP3SCVPart
import CFSG.ClassicalInvolution.Asc77.WP3SCVTag
import CFSG.ClassicalInvolution.Asc77.WP3SCVOrthC
import CFSG.ClassicalInvolution.Asc77.WP3SCUVCtx
import CFSG.ClassicalInvolution.Asc77.WP3ChainVGen3
import CFSG.ClassicalInvolution.Asc77.WP3SCUVertex
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.WP3SCUModel4
import CFSG.ClassicalInvolution.Asc77.WP3SCURank
import CFSG.ClassicalInvolution.Asc77.WP3SCUNG
import CFSG.ClassicalInvolution.Asc77.WP3FrameBootNoTwins
import CFSG.ClassicalInvolution.Asc77.WP3SCRBoot
import CFSG.ClassicalInvolution.Asc77.AscFusionS14
import CFSG.ClassicalInvolution.Asc77.WP3SCUProved
import CFSG.ClassicalInvolution.Asc77.WP3SCSGenT
import CFSG.ClassicalInvolution.Asc77.WP3FrameStarE
import CFSG.ClassicalInvolution.Asc77.WP3FrameStar
import CFSG.ClassicalInvolution.Asc77.WP3L52Main
import CFSG.ClassicalInvolution.Asc77.AscT3UMain
import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinU
import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinRowsOuter
import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Outer
import CFSG.ClassicalInvolution.ModelFacts.Orth15RFixLift
import CFSG.ClassicalInvolution.ModelFacts.Orth15SSec
import CFSG.ClassicalInvolution.RouteD.G2D4Ih8Free
import CFSG.ClassicalInvolution.Balance.BootstrapExoticG2D4
import CFSG.ClassicalInvolution.Balance.BootstrapExoticE6
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952
public import CFSG.ClassicalInvolution.Asc77.WP3ChainVToral
public import CFSG.ClassicalInvolution.Asc77.WP3SCUBGU
public import CFSG.ClassicalInvolution.Balance.StrongPowSuMain
import CFSG.ClassicalInvolution.Asc77.AscE187Cop
import CFSG.ClassicalInvolution.Asc77.AscT7CExit25
import CFSG.ClassicalInvolution.Asc77.AscT7CWz
import CFSG.ClassicalInvolution.Asc77.AscT7D242
import CFSG.ClassicalInvolution.Asc77.AscT7EC23
import CFSG.ClassicalInvolution.Asc77.AscT7HX23
import CFSG.ClassicalInvolution.Asc77.AscT7K3
import CFSG.ClassicalInvolution.Asc77.AscT7K4
import CFSG.ClassicalInvolution.Asc77.AscT8Setup
import CFSG.ClassicalInvolution.Asc77.AscThmABasic
import CFSG.ClassicalInvolution.AschTight.C195Wreath
import CFSG.ClassicalInvolution.AschTight.Hall196Idx
import CFSG.ClassicalInvolution.AschTight.Sec6Gen64Main
import CFSG.ClassicalInvolution.AschTight.Sec7L98J
import CFSG.ClassicalInvolution.RouteD.G2D4Ih8
import CFSG.RankThree.PartTwo.KFacts.K72OmegaL2

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance.Bootstrap

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime]

theorem exoticLeviBlock : ExoticLeviBlock p f := by
  intro G _ _ Ω hΩ x _ h9 D i hi
  rcases hi with hi | hi | hi
  · exact Balance.exists_member_leviBlockImage_of_g2d4 hΩ h9 D i (Or.inl hi)
  · exact Balance.exists_member_leviBlockImage_of_twistedE6 (by rw [h9]; norm_num) D i hi
  · exact Balance.exists_member_leviBlockImage_of_g2d4 hΩ h9 D i (Or.inr hi)

section Class

variable {G : Type} [Group G]

theorem conjClass_eq_of_mem {K L : Subgroup G} (hL : L ∈ 𝒞 K) : 𝒞 L = 𝒞 K := by
  obtain ⟨g₀, rfl⟩ := hL
  ext M
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g * g₀, by show conjSub (g * g₀) K = conjSub g (conjSub g₀ K); rw [conjSub_mul]⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g * g₀⁻¹, by
      show conjSub (g * g₀⁻¹) (conjSub g₀ K) = conjSub g K
      rw [conjSub_mul, conjSub_inv_conjSub]⟩

theorem Setting.of_mem [Finite G] {K L : Subgroup G} {z w : G} (h : Setting p f K z)
    (hL : L ∈ 𝒞 K) (hw : IsClassicalMember p f L w) : Setting p f L w := by
  have e := conjClass_eq_of_mem hL
  exact ⟨h.nonabelian, h.odd, h.five, hw, h.below, h.rank, h.notFourGenerated, e ▸ h.dconn,
    e ▸ h.noBoot⟩

end Class

theorem pspCaseP1_of_pieces (h1 : AxisExists p f) (h2 : AxisHyp51Classical p f)
    (h3 : AxisFrameSide p f) (h5 : AxisHyp51S p f) (h6 : AxisP1 p f) : PSpCaseP1 p f := by
  intro G _ _ _ K z hS hE
  obtain ⟨K₂, K₃, z₂, z₃, t₁, t₂, t₃, w₁, w₂, hA⟩ := h1 G K z hS hE
  have h51 : Asc77.Hyp51 (TypeCSetup.axis z z₂ t₁ t₂ t₃) := by
    refine ⟨hA.elem, hA.card, fun c hc hc1 => ?_⟩
    by_cases hcB : c ∈ Subgroup.closure ({z, z₂} : Set G)
    · exact h2 G K z hS hE K K₂ K₃ z z₂ z₃ t₁ t₂ t₃ w₁ w₂ hA c hcB hc1
    · exact h5 G K z hS hE K K₂ K₃ z z₂ z₃ t₁ t₂ t₃ w₁ w₂ hA c hc hcB
  have htop := Asc77.rankTwoSpan_eq_top_of_dConnected_star hS.odd hS.five
    (inClass_conjugates hS.member) (h3 G K z hS hE K K₂ K₃ z z₂ z₃ t₁ t₂ t₃ w₁ w₂ hA) hS.dconn
  exact h6 G K z hS hE K K₂ K₃ z z₂ z₃ t₁ t₂ t₃ w₁ w₂ hA (Asc77.lemma52 G _ h51) htop

theorem pspCaseP1Core_of_pieces (h1 : AxisExistsCore p f) (h2 : AxisHyp51ClassicalCore p f)
    (h3 : AxisFrameSideCore p f) (h5 : AxisHyp51SCore p f) (h6 : AxisP1Core p f) :
    PSpCaseP1Core p f := by
  intro G _ _ _ K z hS hE
  obtain ⟨K₂, K₃, z₂, z₃, t₁, t₂, t₃, w₁, w₂, hA⟩ := h1 G K z hS hE
  have h51 : Asc77.Hyp51 (TypeCSetup.axis z z₂ t₁ t₂ t₃) := by
    refine ⟨hA.elem, hA.card, fun c hc hc1 => ?_⟩
    by_cases hcB : c ∈ Subgroup.closure ({z, z₂} : Set G)
    · exact h2 G K z hS hE K K₂ K₃ z z₂ z₃ t₁ t₂ t₃ w₁ w₂ hA c hcB hc1
    · exact h5 G K z hS hE K K₂ K₃ z z₂ z₃ t₁ t₂ t₃ w₁ w₂ hA c hc hcB
  have htop := Asc77.rankTwoSpan_eq_top_of_dConnected_star hS.odd hS.five
    (inClass_conjugates hS.member) (h3 G K z hS hE K K₂ K₃ z z₂ z₃ t₁ t₂ t₃ w₁ w₂ hA) hS.dconn
  exact h6 G K z hS hE K K₂ K₃ z z₂ z₃ t₁ t₂ t₃ w₁ w₂ hA (Asc77.lemma52 G _ h51) htop

end CFSG.ClassicalInvolution.NDB
