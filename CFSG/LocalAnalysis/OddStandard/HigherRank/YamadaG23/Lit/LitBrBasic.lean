module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitDefs
public import CFSG.GH74.GLS.Basic
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three CFSG.OddStandard.HigherRank.G2Three.Sec1
  CFSG.GH74.GLS
open scoped commutatorElement

variable {Γ : Type} [Group Γ] {Gh Zh Ah : Subgroup Γ}

theorem lit_normal_Z (hZc : ∀ x ∈ Gh, ∀ z ∈ Zh, x * z = z * x) : (Zh.subgroupOf Gh).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hZc (g : Γ) g.2 (n : Γ) hn]
  simpa using hn

theorem lit_normalizer_eq (hAG : Ah ≤ Gh) :
    normalizer ((Ah.subgroupOf Gh : Subgroup ↥Gh) : Set ↥Gh) = (normIn Gh Ah).subgroupOf Gh := by
  rw [normIn, Subgroup.inf_subgroupOf_left, Subgroup.subgroupOf_normalizer_eq hAG]

private lemma mem_normalizer_of_centralizes {c : Γ} (hc : c ∈ Gh)
    (hZc : ∀ x ∈ Gh, ∀ z ∈ Zh, x * z = z * x) : c ∈ normalizer (Zh : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    rw [hZc c hc z hz]
    simpa using hz
  · intro hz
    have h1 : z = c⁻¹ * (c * z * c⁻¹) * c := by group
    rw [h1, hZc c⁻¹ (Gh.inv_mem hc) (c * z * c⁻¹) hz]
    simpa using hz

theorem lit_litC_eq [(Zh.subgroupOf Gh).Normal] (hZc : ∀ x ∈ Gh, ∀ z ∈ Zh, x * z = z * x)
    (hAG : Ah ≤ Gh) :
    litC (Zh.subgroupOf Gh) (Ah.subgroupOf Gh) =
      (Gh ⊓ centralizerSection Ah Zh).subgroupOf Gh := by
  ext c
  simp only [mem_litC, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · rintro ⟨hcN, hc⟩
    have hcA : (c : Γ) ∈ normalizer (Ah : Set Γ) := by
      have h := hcN
      simp only [lit_normalizer_eq hAG, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
        normIn] at h
      exact h.2
    have hcComm : ∀ k ∈ Ah, ⁅k, (c : Γ)⁆ ∈ Zh := by
      intro k hk
      have ha : (⟨k, hAG hk⟩ : ↥Gh) ∈ Ah.subgroupOf Gh := by
        rw [Subgroup.mem_subgroupOf]
        exact hk
      have h := hc ⟨k, hAG hk⟩ ha
      simpa [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using h
    exact ⟨c.2, hcA, mem_normalizer_of_centralizes c.2 hZc, hcComm⟩
  · rintro ⟨-, hcA, -, hcComm⟩
    constructor
    · simp only [lit_normalizer_eq hAG, Subgroup.mem_subgroupOf, Subgroup.mem_inf, normIn]
      exact ⟨c.2, hcA⟩
    · intro a ha
      have h := hcComm (a : Γ) ha
      simpa [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using h

theorem lit_nonab_subgroupOf (hAG : Ah ≤ Gh) (hnab : ¬ ∀ a ∈ Ah, ∀ b ∈ Ah, a * b = b * a) :
    ¬ ∀ a ∈ Ah.subgroupOf Gh, ∀ b ∈ Ah.subgroupOf Gh, a * b = b * a := by
  intro h
  apply hnab
  intro a ha b hb
  have ha' : (⟨a, hAG ha⟩ : ↥Gh) ∈ Ah.subgroupOf Gh := by
    rw [Subgroup.mem_subgroupOf]
    exact ha
  have hb' : (⟨b, hAG hb⟩ : ↥Gh) ∈ Ah.subgroupOf Gh := by
    rw [Subgroup.mem_subgroupOf]
    exact hb
  have hh := h ⟨a, hAG ha⟩ ha' ⟨b, hAG hb⟩ hb'
  have := congrArg (fun x : ↥Gh => (x : Γ)) hh
  simpa [Subgroup.coe_mul] using this

end CFSG.OddStandard.HigherRank.YamadaG23
