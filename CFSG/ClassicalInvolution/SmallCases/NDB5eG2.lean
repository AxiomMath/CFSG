module

public import CFSG.ClassicalInvolution.SmallCases.NDB5dTag
import CFSG.ClassicalInvolution.Asc77.AscT3UG2D4
import CFSG.ClassicalInvolution.Asc77.AscT3ULayer
import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51
import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinT
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
import CFSG.ClassicalInvolution.Asc77.AscT7CExit25
import CFSG.ClassicalInvolution.Asc77.AscT7CWz
import CFSG.ClassicalInvolution.Asc77.AscT7D242
import CFSG.ClassicalInvolution.Asc77.AscT7EC23
import CFSG.ClassicalInvolution.Asc77.AscT7HX23
import CFSG.ClassicalInvolution.Asc77.AscT7K3
import CFSG.ClassicalInvolution.Asc77.AscT7K4
import CFSG.ClassicalInvolution.Asc77.AscThmABasic
import CFSG.ClassicalInvolution.AschTight.Sec6Gen64Main
import CFSG.ClassicalInvolution.ModelFacts.Orth15SSec

public section

namespace CFSG.ClassicalInvolution.NDB.Alpha

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.ExactLayer

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem alpha_g2d4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {z₁ z₂ s : G}
    (hA : IsElemAbelian 2 (Subgroup.closure ({z₁, z₂, s} : Set G))) (hz₁1 : z₁ ≠ 1)
    (hz₂1 : z₂ ≠ 1) (hz₁₂ : z₁ ≠ z₂) {Φ : Set (Subgroup G)} (hN : NormalizesLayer Φ s)
    (D : LocalLieSystemAt p f Φ s) (j₀ : Fin D.card)
    (ht : D.tag j₀ = .G2 ∨ D.tag j₀ = .trialityD4)
    (hz₁R : ∀ h, oddQuotMk s ⟨z₁, h⟩ ∈ (secComponentHom hN D j₀).range)
    (hz₂R : ∀ h, oddQuotMk s ⟨z₂, h⟩ ∈ (secComponentHom hN D j₀).range) :
    alphaOf (inducedImage (secComponentHom hN D j₀).range
      (modOdd s (Subgroup.closure ({z₁, z₂, s} : Set G)))) = ⊥ := by
  set ψ := secComponentHom hN D j₀ with hψ
  set B := Subgroup.closure ({z₁, z₂, s} : Set G) with hB
  have hsB : s ∈ B := Subgroup.subset_closure (by simp)
  have hz₁B : z₁ ∈ B := Subgroup.subset_closure (by simp)
  have hz₂B : z₂ ∈ B := Subgroup.subset_closure (by simp)
  have hBC : B ≤ Subgroup.centralizer ({s} : Set G) := Lemma52Proof.le_centralizer_of_mem hA hsB
  have hS : ({z₁, z₂, s} : Set G) ⊆ Subgroup.centralizer ({s} : Set G) := fun x hx =>
    hBC (Subgroup.subset_closure hx)
  have hz₁C := hBC hz₁B
  have hz₂C := hBC hz₂B
  set a := oddQuotMk s ⟨z₁, hz₁C⟩ with ha
  set b := oddQuotMk s ⟨z₂, hz₂C⟩ with hb
  have hsq : ∀ {x : G} (hxB : x ∈ B) (hxC : x ∈ Subgroup.centralizer ({s} : Set G)),
      oddQuotMk s ⟨x, hxC⟩ * oddQuotMk s ⟨x, hxC⟩ = 1 := by
    intro x hxB hxC
    rw [← map_mul]
    have e : (⟨x, hxC⟩ * ⟨x, hxC⟩ : ↥(Subgroup.centralizer ({s} : Set G))) = 1 :=
      Subtype.ext (Lemma52Proof.mul_self_eq_one_of_mem hA hxB)
    rw [e, map_one]
  have hne1 : ∀ {x : G} (hxB : x ∈ B) (hxC : x ∈ Subgroup.centralizer ({s} : Set G)), x ≠ 1 →
      oddQuotMk s ⟨x, hxC⟩ ≠ 1 := by
    intro x hxB hxC hx1 h
    apply hx1
    have h' : oddQuotMk s ⟨x, hxC⟩ = oddQuotMk s ⟨1, Subgroup.one_mem _⟩ := by
      rw [h]
      exact (map_one _).symm
    exact eq_of_oddQuotMk_eq hA hxB (Subgroup.one_mem _) hxC (Subgroup.one_mem _) h'
  have hab : a ≠ b := fun h => hz₁₂ (eq_of_oddQuotMk_eq hA hz₁B hz₂B hz₁C hz₂C h)
  have hzz : z₁ * z₂ = z₂ * z₁ :=
    congrArg Subtype.val (hA.1.is_comm.comm (⟨z₁, hz₁B⟩ : B) ⟨z₂, hz₂B⟩)
  have habc : a * b = b * a := by
    rw [ha, hb, ← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext hzz)
  have hD := T7A.isElemAbelian2_closure_pair (hsq hz₁B hz₁C) (hsq hz₂B hz₂C)
    (hne1 hz₁B hz₁C hz₁1) (hne1 hz₂B hz₂C hz₂1) hab habc
  set A' : Subgroup (OddQuot s) := Subgroup.closure ({a, b} : Set (OddQuot s)) with hA'
  have haR : a ∈ ψ.range := hz₁R hz₁C
  have hbR : b ∈ ψ.range := hz₂R hz₂C
  have hAL : A' ≤ ψ.range := by
    rw [hA', Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact haR
    · exact hbR
  have key : alphaOf (inducedImage ψ.range A') = ⊥ :=
    T3CII.T3U.alphaOf_inducedImage_eq_bot_of_g2d4 hp2 hq ht (D.isFundTag j₀) (D.admissible j₀)
      (D.exp_eq j₀) ψ (secComponentHom_ker_le_center hN D j₀) hD.1 hD.2 hAL
  refine (congrArg alphaOf (le_antisymm ?_ ?_)).trans key
  · have hgen : ∀ (x : G) (hx : x ∈ ({z₁, z₂, s} : Set G)),
        ∃ hn : oddQuotMk s ⟨x, hS hx⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot s)),
          toInducedAutOn ψ.range ⟨oddQuotMk s ⟨x, hS hx⟩, hn⟩ ∈ inducedImage ψ.range A' := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨Subgroup.le_normalizer haR, ⟨⟨_, Subgroup.le_normalizer haR⟩,
          Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure (by simp [ha])), rfl⟩⟩
      · exact ⟨Subgroup.le_normalizer hbR, ⟨⟨_, Subgroup.le_normalizer hbR⟩,
          Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure (by simp [hb])), rfl⟩⟩
      · obtain ⟨hcn, hc1⟩ := oddQuotSelf_induced _ ψ.range
        refine ⟨hcn, ?_⟩
        show toInducedAutOn ψ.range ⟨Lemma52Proof.oddQuotSelf _, hcn⟩ ∈ _
        rw [hc1]
        exact Subgroup.one_mem _
    exact inducedImage_modOdd_closure_le hS ψ.range (inducedImage ψ.range A') hgen
  · refine T3CII.T3U.inducedImage_mono ψ.range ?_
    rw [hA', Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact oddQuotMk_mem_modOdd hz₁B hz₁C
    · exact oddQuotMk_mem_modOdd hz₂B hz₂C

end CFSG.ClassicalInvolution.NDB.Alpha
