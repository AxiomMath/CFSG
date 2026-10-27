module

public import CFSG.ClassicalInvolution.RouteD.TWT4TrichD4
public import CFSG.ClassicalInvolution.RouteD.TWZLinkSu4
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

public section

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.RouteD.TWZ
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.RouteD.TWT4

section Linked

variable (p f : ℕ) [Fact p.Prime]

theorem twinYLinkedSU4_of_mod_three (hmod : (p ^ f) % 4 = 3) : TWS.TwinYLinkedSU4 p f := by
  intro G _ _ _ hnab K z S hshape Λ K₂ hK₂ hK₂Λ w hw hex
  obtain ⟨T, e, hT, clsT, hP1, hty⟩ := hex
  have hrow : TwinRow .PSU 4 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))))
  have hMF : TwinMFGeneration p f .PSU 4 := twinMFGeneration_psu4 S.odd S.five
  have hK₂K : K₂ ≠ K := ne_of_mem_range_su S.odd S.p1 Λ hK₂ hK₂Λ
    (CoreAssembly.mem_conjClass_self K) S.cls S.five
  have hK₂T : K₂ ≠ T := ne_of_mem_range_su S.odd S.p1 Λ hK₂ hK₂Λ hT.mem.1 clsT S.five
  obtain ⟨D, hcard, i, ht, hr, -⟩ := hty
  have hcard1 : D.card = 1 := by omega
  have hmod' : twinYModel (p ^ f) .PSU 4 = (.POmegaPlus, 4) := by simp [twinYModel, hmod]
  rw [hmod'] at ht hr
  have ht' : D.tag i = .POmegaPlus := ht
  have hr' : D.rank i = 4 := hr
  have hDi : D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4 := by
    rw [ht']
    exact ⟨by decide, by decide⟩
  have hnc : ¬ (D.tag i = .PSL ∧ D.rank i = 2) := by
    rintro ⟨h1, -⟩
    rw [ht'] at h1
    exact absurd h1 (by decide)
  obtain ⟨hexp, -, -, -⟩ := component_package S.odd S.five D hcard1 i hDi
  have hmodel : SqTrichotomyOn (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out) := by
    have hadm := D.admissible i
    rw [ht', hr', hexp] at hadm ⊢
    exact sqTrichotomyOn_plus4 S.odd S.five hadm
  exact linked_of_model hnab S hrow hshape hT clsT e hMF hP1 D hcard1 i hDi hnc hmodel hK₂ hK₂K
    hK₂T hw

end Linked

end CFSG.ClassicalInvolution.RouteD.TWT4
