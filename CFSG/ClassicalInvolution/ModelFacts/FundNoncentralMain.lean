module

public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralSimple
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralSp
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralG2
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralD4
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralPSU
public import CFSG.ClassicalInvolution.Generic.Induction
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
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.Models.LinearFrames.Frame
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.Pairs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank

theorem fundNoncentral_core (t : StatedLieTag) (n p e : ℕ) [hp : Fact p.Prime]
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e) (hne : ¬ (t = .PSL ∧ n = 2)) :
    ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D, ∀ r ∈ R,
      (∀ y : (modelUniv t n p e hp.out).K,
        r * y * r⁻¹ * y⁻¹ ∈ Subgroup.center (modelUniv t n p e hp.out).K) → r = 1 := by
  intro R hR r hrR hr
  have hK := isQuasisimple_modelUniv t n p e hp.out hfund hadm
  have hrc := mem_center_of_commutators_mem_center hK hr
  by_cases hPSp : t = .PSp
  · subst hPSp
    exact eq_one_of_mem_center_PSp n p e hp.out hfund hadm hR hrR hrc
  by_cases hPSU : t = .PSU
  · subst hPSU
    exact eq_one_of_mem_center_PSU n e hfund hadm R hR r hrR hrc
  by_cases hG2 : t = .G2
  · subst hG2
    exact eq_one_of_mem_center_G2 n p e hp.out hfund hadm hR hrR hrc
  by_cases hD4 : t = .trialityD4
  · subst hD4
    exact eq_one_of_mem_center_D4 n p e hp.out hfund hadm hR hrR hrc
  exact eq_one_of_mem_center_of_easy t n p e hp.out hfund hadm hne hPSp hPSU hG2 hD4 hR hrR hrc

theorem fundNoncentral_generic (p : ℕ) [Fact p.Prime] :
    ∀ (t : StatedLieTag) (n e : ℕ), CFSG.ClassicalInvolution.Generic.IsFundTag t →
      StatedLieAdmissible t n p e → ¬ (t = .PSL ∧ n = 2) →
      ∀ R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups t
          (CFSG.ClassicalInvolution.Generic.modelUniv t n p e Fact.out).D,
        ∀ r ∈ R,
          (∀ y : (CFSG.ClassicalInvolution.Generic.modelUniv t n p e Fact.out).K,
            r * y * r⁻¹ * y⁻¹ ∈
              Subgroup.center (CFSG.ClassicalInvolution.Generic.modelUniv t n p e Fact.out).K) →
          r = 1 := by
  intro t n e hfund hadm hne
  have hfund' : IsFundTag t := by
    cases t <;> trivial
  exact fundNoncentral_core t n p e hfund' hadm hne

end CFSG.ClassicalInvolution.ModelFacts
