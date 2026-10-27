module

public import CFSG.ClassicalInvolution.RouteD.TypeE8Excl
public import CFSG.ClassicalInvolution.RouteD.TwinSL4BridgeBase
public import CFSG.ClassicalInvolution.Balance.Q27FuzzyMain
public import CFSG.ClassicalInvolution.Balance.Q27Layers
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairFinalAll
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalTwAll
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
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourBasic

public section

namespace CFSG.ClassicalInvolution.RouteD.TypeE8

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly

variable {p f : ℕ} [Fact p.Prime]

theorem e8P1x : E8P1x p f := by
  intro G _ _ _ hnab K z S W₁ W₂ w₁ w₂ hW₁ hW₂ hw₁ hw₂ hKW₁ hKW₂ hW₁₂ hcard
  have hlay : Balance.Theorem5.TriangleLayers p f :=
    Balance.Q27.triangleLayers_of_hybrid_free (Balance.Bootstrap.layerGenerationHybrid p)
  have hMFC : ModelFacts.CommutingFundamentalFactsFive p :=
    ModelFacts.commutingFundamentalFactsFive_all S.odd
  have hcl : conjClass W₁ = conjClass K := conjClass_eq_of_mem hW₁
  have hz2 : z * z = 1 := DeltaClosure.sq_eq_one S.cls
  have hw₁2 : w₁ * w₁ = 1 := DeltaClosure.sq_eq_one hw₁
  have hw₂2 : w₂ * w₂ = 1 := DeltaClosure.sq_eq_one hw₂
  have hzw₁ : z * w₁ = w₁ * z := hKW₁ z S.cls.mem w₁ hw₁.mem
  have hzw₂ : z * w₂ = w₂ * z := hKW₂ z S.cls.mem w₂ hw₂.mem
  have hw₁₂ : w₁ * w₂ = w₂ * w₁ := hW₁₂ w₁ hw₁.mem w₂ hw₂.mem
  have hrange : Subgroup.closure (Set.range (![z, w₁, w₂] : Fin 3 → G)) =
      Subgroup.closure ({z, w₁, w₂} : Set G) := by
    congr 1
    ext x
    simp
    tauto
  have hind : IndepTriple p f (conjClass K) := by
    refine ⟨![K, W₁, W₂], ![z, w₁, w₂], ?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact ⟨mem_conjClass_self K, S.cls⟩
      · exact ⟨hW₁, hw₁⟩
      · exact ⟨hW₂, hw₂⟩
    · intro i j hij x hx y hy
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hKW₁ x hx y hy
      · exact hKW₂ x hx y hy
      · exact (hKW₁ y hy x hx).symm
      · exact absurd rfl hij
      · exact hW₁₂ x hx y hy
      · exact (hKW₂ y hy x hx).symm
      · exact (hW₁₂ y hy x hx).symm
      · exact absurd rfl hij
    · rw [hrange]
      refine Balance.Theorem5.isElemAbelian_closure_of_commuting_involutions ?_ ?_
      · rintro s (rfl | rfl | rfl)
        · exact hz2
        · exact hw₁2
        · exact hw₂2
      · rintro s (rfl | rfl | rfl) t (rfl | rfl | rfl)
        · rfl
        · exact hzw₁
        · exact hzw₂
        · exact hzw₁.symm
        · rfl
        · exact hw₁₂
        · exact hzw₂.symm
        · exact hw₁₂.symm
        · rfl
    · rw [hrange]
      exact hcard
  have hne : w₁ ≠ w₂ := by
    intro h
    have hle := Balance.Theorem5.card_closure_pair_le_four (a := z) (b := w₁) hz2 hw₁2 hzw₁
    have hset : ({z, w₁, w₂} : Set G) = {z, w₁} := by
      subst h
      ext y
      simp
    rw [hset] at hcard
    omega
  have hS₁ : RouteDSetup p f W₁ w₁ := S.of_mem_conjClass hW₁ hw₁
  have := Balance.Q27.productOfTwoP1_of_indepTriple_free hlay hMFC G hnab W₁ w₁ hS₁
    (hcl ▸ hind) W₂ (hcl ▸ hW₂) w₂ hw₂ hW₁₂ hne
  rwa [hcl] at this

end CFSG.ClassicalInvolution.RouteD.TypeE8
