module

public import CFSG.ClassicalInvolution.ModelFacts.E8ExclRowStmt
public import CFSG.ClassicalInvolution.ModelFacts.E8D8RowFund
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpOrth
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

public section

namespace CFSG.ClassicalInvolution.RouteD.TypeE8

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.RouteD.NonClassical

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

variable (p f : ℕ) [Fact p.Prime]

theorem card_fund12_mul (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    Nat.card (Fund12 p f) *
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField p f))) =
      2 * Nat.card (OFrame (quadPlus 6 (GaloisField p f))) := by
  obtain ⟨hodd, -⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      simp at hq
    · exact h
  have hn4 : 4 ≤ 6 := by norm_num
  have hn3 : 3 ≤ 6 := by norm_num
  have hadm : StatedLieAdmissible .POmegaPlus 6 p f := ⟨Fact.out, hf1, hn4⟩
  have hperf : RouteD.Gaps.FundPerfect .POmegaPlus (modelUniv .POmegaPlus 6 p f Fact.out).D :=
    RouteD.Gaps.fundPerfect_modelUniv hp2 trivial hadm (by omega)
  have hcorr := fundCorr_plus hp2 hq hn4
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus 6 (GaloisField p f)),
      plusDatum 6 (GaloisField p f) hn3⟩ → RouteD.Gaps.FundPerfect .POmegaPlus M.D →
      Nat.card {R : Subgroup M.K // R ∈ fundamentalSubgroups .POmegaPlus M.D} *
          Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField p f))) =
        2 * Nat.card (OFrame (quadPlus 6 (GaloisField p f))) := by
    intro M hM hperf
    subst hM
    exact ModelFacts.E8D8.card_fund_mul_of_central hodd
      (spinAction (quadPlus 6 (GaloisField p f))) (ker_spinAction_le_center _)
      (fun R hR => eq_commutator_of_le (hperf R hR)) hcorr.1 hcorr.2
  exact key _ (ModelFacts.modelUniv_POmegaPlus hn3) hperf

end CFSG.ClassicalInvolution.RouteD.TypeE8
