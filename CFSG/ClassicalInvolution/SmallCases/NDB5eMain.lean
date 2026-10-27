module

public import CFSG.ClassicalInvolution.SmallCases.NDB5eAlp
public import CFSG.ClassicalInvolution.SmallCases.NDB5Glue
import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51
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
public import CFSG.ClassicalInvolution.SmallCases.NDB5eG2

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.ExactLayer

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable (p f : ℕ) [Fact p.Prime]

theorem sAlphaCore_proved : SAlphaCore p f := by
  intro G _ _ _ K z hS _ K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ hax L₁ L₂ hL₁ hL₂ hN D j₀ R₁ R₂ hSC _
    hmov
  have hp2 := hS.odd
  have hq := hS.five
  set B := Subgroup.closure ({z₁, z₂, t₁ * t₂ * t₃} : Set G) with hB
  have hA : IsElemAbelian 2 B := hax.elem
  have hA8 : Nat.card B = 8 := hax.card
  have hsB : t₁ * t₂ * t₃ ∈ B := Subgroup.subset_closure (by simp)
  have hz₁B : z₁ ∈ B := Subgroup.subset_closure (by simp)
  have hz₂B : z₂ ∈ B := Subgroup.subset_closure (by simp)
  have hne1 : ∀ {x : G}, orderOf x = 2 → x ≠ 1 := fun hx h1 => by
    rw [h1, orderOf_one] at hx
    exact absurd hx (by decide)
  have hz₁1 := hne1 hax.cls₁.orderOf_eq_two
  have hz₂1 := hne1 hax.cls₂.orderOf_eq_two
  have hz₃1 := hne1 hax.cls₃.orderOf_eq_two
  have hz₁2 : z₁ * z₁ = 1 := hax.cls₁.isCentralInvolution.sq
  have hz₂2 : z₂ * z₂ = 1 := hax.cls₂.isCentralInvolution.sq
  have hz₁₂ : z₁ ≠ z₂ := by
    intro h
    apply hz₃1
    rw [← hax.prod, h, hz₂2]
  have hzz : z₁ * z₂ = z₂ * z₁ :=
    congrArg Subtype.val (hA.1.is_comm.comm (⟨z₁, hz₁B⟩ : B) ⟨z₂, hz₂B⟩)
  have hs1 : t₁ * t₂ * t₃ ≠ 1 := by
    intro h1
    have hpair := T7A.isElemAbelian2_closure_pair hz₁2 hz₂2 hz₁1 hz₂1 hz₁₂ hzz
    have hle : B ≤ Subgroup.closure ({z₁, z₂} : Set G) := by
      rw [hB, Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx | hx
      · exact Subgroup.subset_closure (by simp [hx])
      · exact Subgroup.subset_closure (by simp [hx])
      · rw [hx, h1]
        exact Subgroup.one_mem _
    have := Subgroup.card_le_of_le hle
    rw [hA8, hpair.1] at this
    omega
  have hz₁R : ∀ h, oddQuotMk (t₁ * t₂ * t₃) ⟨z₁, h⟩ ∈ (secComponentHom hN D j₀).range :=
    fun h => Subgroup.map_le_range _ R₁ (hSC.img₁ ▸ hSC.mem₁ h)
  have hz₂R : ∀ h, oddQuotMk (t₁ * t₂ * t₃) ⟨z₂, h⟩ ∈ (secComponentHom hN D j₀).range :=
    fun h => Subgroup.map_le_range _ R₂ (hSC.img₂ ▸ hSC.mem₂ h)
  have htag := WC.tag_of_sComponent_core hS hax hL₁ hN D j₀ R₁ R₂ hSC
  obtain ⟨hN₁, D₁, i₀, i₁, R₂', R₃', r₂, r₃, ι, VL₁⟩ := hL₁
  obtain ⟨hN₂, D₂, i₀', i₁', R₂'', R₃'', r₂', r₃', ι', VL₂⟩ := hL₂
  have hU₁ : ∀ h, IsUniqueInvolution (modOdd (t₁ * t₂ * t₃) L₁)
      (oddQuotMk (t₁ * t₂ * t₃) ⟨z₁, h⟩) := fun h =>
    S.isUniqueInvolution_modOdd_of_sec hp2 hq VL₁.sec h
  have e₂ : t₁ * t₂ * t₃ = t₂ * t₁ * t₃ := by rw [hax.ct₁₂]
  have hsec₂ : IsSectionMember p f (Subgroup.centralizer ({t₁ * t₂ * t₃} : Set G)) L₂ z₂ := by
    rw [e₂]
    exact VL₂.sec
  have hU₂ : ∀ h, IsUniqueInvolution (modOdd (t₁ * t₂ * t₃) L₂)
      (oddQuotMk (t₁ * t₂ * t₃) ⟨z₂, h⟩) := fun h =>
    S.isUniqueInvolution_modOdd_of_sec hp2 hq hsec₂ h
  have hz₂L₁ : ∀ h, conjSub (oddQuotMk (t₁ * t₂ * t₃) ⟨z₂, h⟩) (modOdd (t₁ * t₂ * t₃) L₁) =
      modOdd (t₁ * t₂ * t₃) L₁ := by
    intro h
    have hz₂z₁ : z₂ ∈ Subgroup.centralizer ({z₁} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hzz.symm
    rw [← Asc77.modOdd_conjSub_of_mem_centralizer h L₁, VL₁.normal z₂ ⟨hz₂z₁, h⟩]
  show alphaOf (inducedImage (secComponentHom hN D j₀).range (modOdd (t₁ * t₂ * t₃) B)) = ⊥
  rcases htag with ⟨ht, hn⟩ | ⟨ht, hn⟩ | ht | ht
  · exact Alpha.alpha_toral hp2 hq hA hA8 hs1 hN D j₀ (Or.inl ht)
      (fun h => absurd (hn.symm.trans h.2) (by decide)) hSC.ker hSC.fund₁ hSC.fund₂ hSC.img₁
      hSC.img₂ hU₁ hU₂ hz₂L₁ hmov
  · exact Alpha.alpha_toral hp2 hq hA hA8 hs1 hN D j₀ (Or.inr ht)
      (fun h => absurd (ht.symm.trans h.1) (by decide)) hSC.ker hSC.fund₁ hSC.fund₂ hSC.img₁
      hSC.img₂ hU₁ hU₂ hz₂L₁ hmov
  · exact Alpha.alpha_g2d4 hp2 hq hA hz₁1 hz₂1 hz₁₂ hN D j₀ (Or.inl ht) hz₁R hz₂R
  · exact Alpha.alpha_g2d4 hp2 hq hA hz₁1 hz₂1 hz₁₂ hN D j₀ (Or.inr ht) hz₁R hz₂R

theorem sAlpha_proved : SAlpha p f :=
  SAlpha.of_core p f (sAlphaCore_proved p f)

theorem pspCaseP1_proved : PSpCaseP1 p f :=
  pspCaseP1_of_sAlpha p f (sAlpha_proved p f)

theorem pspCaseP1Core_proved : PSpCaseP1Core p f :=
  pspCaseP1Core_of_sAlphaCore p f (sAlphaCore_proved p f)

end CFSG.ClassicalInvolution.NDB
