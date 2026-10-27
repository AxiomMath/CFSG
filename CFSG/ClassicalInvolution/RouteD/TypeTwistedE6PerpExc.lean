module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpClassical

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {p : ℕ} [Fact p.Prime]

theorem noTE6Config_of_hasQuasisimpleLayer (hp2 : p ≠ 2) {t : StatedLieTag} {n e : ℕ}
    (hq : 4 ≤ p ^ e) (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (hlayer : HasQuasisimpleLayer p t n e) :
    NoTE6Config (fundamentalSubgroups t (modelUniv t n p e Fact.out).D) := by
  intro R₀ hR₀ R₁ hP _
  have hperf : Gaps.FundPerfect t (modelUniv t n p e Fact.out).D :=
    Gaps.fundPerfect_modelUniv hp2 hfund hadm hq
  refine false_of_universalPartner_of_layer
    (fun R hR g => conjSub_mem_fundamentalSubgroups hR g) hperf (fun R hR hab => ?_) hP
    (hlayer R₀ hR₀)
  apply fundamentalSubgroups_ne_bot hfund hadm hR
  refine eq_bot_iff.mpr ((hperf R hR).trans (Subgroup.commutator_le.mpr fun x hx y hy => ?_))
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact hab x hx y hy

end CFSG.ClassicalInvolution.RouteD.NonClassical
