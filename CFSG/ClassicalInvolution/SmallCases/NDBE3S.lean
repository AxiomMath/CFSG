module

public import CFSG.ClassicalInvolution.SmallCases.NDBE2SFrame
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinT
import CFSG.ClassicalInvolution.SmallCases.NDB5Sec
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
public import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51Cases
public import CFSG.ClassicalInvolution.Asc77.WP2Thompson
import CFSG.ClassicalInvolution.AschTight.S1911C8c
import CFSG.ClassicalInvolution.AschTight.S1911Case2a
import CFSG.ClassicalInvolution.AschTight.S1911E2c
import CFSG.ClassicalInvolution.AschTight.S1911FusA
import CFSG.ClassicalInvolution.AschTight.Sec19Targets3
import CFSG.ClassicalInvolution.AschTight.Thm6Tight3
import CFSG.ClassicalInvolution.SmallCases.NDB5Layer
import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Outer
import CFSG.Timmesfeld.ARS.CaseEFrame
import CFSG.Timmesfeld.ARS.CaseMLevi
import CFSG.Timmesfeld.ARS.Sec12Center
import CFSG.Timmesfeld.ARS.Sec13Closed
import CFSG.Timmesfeld.ARS.Sec13Maximal
import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.LowTwoRank

local notation "𝒞" => Generic.CoreAssembly.conjClass

theorem Exotic.inducedImage_closure_eq {G : Type} [Group G] [Finite G] {s z₁ z₂ : G}
    (hA : IsElemAbelian 2 (Subgroup.closure ({z₁, z₂, s} : Set G))) (L : Subgroup (OddQuot s))
    (h₁ : z₁ ∈ Subgroup.centralizer ({s} : Set G)) (h₂ : z₂ ∈ Subgroup.centralizer ({s} : Set G))
    (hn₁ : oddQuotMk s ⟨z₁, h₁⟩ ∈ Subgroup.normalizer (L : Set (OddQuot s)))
    (hn₂ : oddQuotMk s ⟨z₂, h₂⟩ ∈ Subgroup.normalizer (L : Set (OddQuot s))) :
    inducedImage L (modOdd s (Subgroup.closure ({z₁, z₂, s} : Set G))) =
      Subgroup.closure ({toInducedAutOn L ⟨_, hn₁⟩, toInducedAutOn L ⟨_, hn₂⟩} :
        Set ↥(inducedAutOn L)) := by
  set B := Subgroup.closure ({z₁, z₂, s} : Set G) with hB
  have hsB : s ∈ B := Subgroup.subset_closure (by simp)
  have hz₁B : z₁ ∈ B := Subgroup.subset_closure (by simp)
  have hz₂B : z₂ ∈ B := Subgroup.subset_closure (by simp)
  have hBC : B ≤ Subgroup.centralizer ({s} : Set G) := Lemma52Proof.le_centralizer_of_mem hA hsB
  have hS : ({z₁, z₂, s} : Set G) ⊆ Subgroup.centralizer ({s} : Set G) := fun x hx =>
    hBC (Subgroup.subset_closure hx)
  refine le_antisymm ?_ ?_
  · refine inducedImage_modOdd_closure_le hS L _ fun x hx => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨hn₁, Subgroup.subset_closure (Set.mem_insert _ _)⟩
    · exact ⟨hn₂, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
    · obtain ⟨hcn, hc1⟩ := oddQuotSelf_induced x L
      refine ⟨hcn, ?_⟩
      show toInducedAutOn L ⟨Lemma52Proof.oddQuotSelf _, hcn⟩ ∈ _
      rw [hc1]
      exact Subgroup.one_mem _
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨⟨_, hn₁⟩, Subgroup.mem_subgroupOf.mpr (oddQuotMk_mem_modOdd hz₁B h₁), rfl⟩
    · exact ⟨⟨_, hn₂⟩, Subgroup.mem_subgroupOf.mpr (oddQuotMk_mem_modOdd hz₂B h₂), rfl⟩

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G}

namespace ExoticLiftS


variable {C : ExoticCtxS p f K z} (L : ExoticLiftS C)

abbrev B : Subgroup G := Subgroup.closure ({z, L.t, L.z'} : Set G)

theorem z_mem_B : z ∈ L.B := Subgroup.subset_closure (Set.mem_insert _ _)

theorem t_mem_B : L.t ∈ L.B :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

theorem z'_mem_B : L.z' ∈ L.B :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

theorem B_elem : IsElemAbelian 2 L.B :=
  L.frameData₁.isElemAbelian C.hS.odd C.X.hΩ

theorem B_card : Nat.card L.B = 8 :=
  L.frameData₁.natCard_eight C.hS.odd C.hS.five C.X.hΩ

theorem hyp51At_z : Hyp51At L.B z := by
  have hz1 : z ≠ 1 := C.X.hKz.ne_one
  have hmov : ∀ M : Subgroup (OddQuot z), CFSG.IsComponent M → MovedByAll L.B z M →
      M = (C.psi C.i₁).range := fun M hM hm =>
    S.moved_eq_range C.hS.odd C.hS.five C.X.hs C.D L.B_elem L.z_mem_B hz1 L.t_mem_B
      L.uJ.ne_one L.t_ne_z (fun hb => ⟨L.τ₁, L.htbar.symm⟩) hM hm
  refine ⟨fun M₁ M₂ h₁ h₂ m₁ m₂ => (hmov M₁ h₁ m₁).trans (hmov M₂ h₂ m₂).symm, ?_⟩
  intro M hM hm
  rw [hmov M hM hm]
  have hset : ({L.t, L.z', z} : Set G) = {z, L.t, L.z'} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hA : IsElemAbelian 2 (Subgroup.closure ({L.t, L.z', z} : Set G)) := by
    rw [hset]
    exact L.B_elem
  have hn₁ : oddQuotMk z ⟨L.t, L.ht⟩ ∈ Subgroup.normalizer ((C.psi C.i₁).range : Set (OddQuot z)) :=
    Subgroup.le_normalizer ⟨L.τ₁, L.htbar.symm⟩
  have hn₂ : oddQuotMk z ⟨L.z', L.hz'⟩ ∈
      Subgroup.normalizer ((C.psi C.i₁).range : Set (OddQuot z)) :=
    Subgroup.le_normalizer ⟨_, L.hz'bar.symm⟩
  rw [show L.B = Subgroup.closure ({L.t, L.z', z} : Set G) by rw [hset],
    Exotic.inducedImage_closure_eq hA _ L.ht L.hz' hn₁ hn₂]
  have h := L.alpha (OddQuot z) (C.psi C.i₁) (C.X.psi_ker C.i₁)
  have e₁ : toInducedAutOn (C.psi C.i₁).range ⟨oddQuotMk z ⟨L.t, L.ht⟩, hn₁⟩ =
      toInducedAutOn (C.psi C.i₁).range ⟨C.psi C.i₁ L.τ₁, Subgroup.le_normalizer ⟨L.τ₁, rfl⟩⟩ :=
    congrArg _ (Subtype.ext L.htbar)
  have e₂ : toInducedAutOn (C.psi C.i₁).range ⟨oddQuotMk z ⟨L.z', L.hz'⟩, hn₂⟩ =
      toInducedAutOn (C.psi C.i₁).range
        ⟨C.psi C.i₁ (L.k * L.τ₁ * L.k⁻¹), Subgroup.le_normalizer ⟨_, rfl⟩⟩ :=
    congrArg _ (Subtype.ext L.hz'bar)
  rw [e₁, e₂]
  exact h

end ExoticLiftS

end CFSG.ClassicalInvolution.NDB
