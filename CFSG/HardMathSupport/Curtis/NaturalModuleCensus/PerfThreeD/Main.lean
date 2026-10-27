module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeD.Residual

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Curtis.Coordinator

section Void


theorem fixPerfThreeVoid_d_inner (Y : Type) [Group Y] [Finite Y]
    (L J : Subgroup Y) (u : Y) (hyp : FixPerfThreeHyp L J u)
    (hu : u ∈ L ⊔ Subgroup.centralizer (L : Set Y))
    (hX : IsLieOf IdxD (↥L ⧸ Subgroup.center ↥L)) : False := by
  obtain ⟨r, hr, hmodel, h8⟩ := exists_model_of_fixPerfThreeHyp_idxD hyp hX
  obtain ⟨l, hl3, hlfix⟩ := exists_decomp_of_mem_sup_centralizer hu hyp.pow hyp.fix
  have hv3 : (QuotientGroup.mk' (Subgroup.center ↥L) l) ^ 3 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 hl3
  by_cases h5 : 5 ≤ r
  · exact false_of_perfThreeCent hyp.perf hlfix
      (perfThreeCent_of_model_pomegaPlus h5 hmodel _ hv3)
  · by_cases hP : PerfThreeCent (QuotientGroup.mk' (Subgroup.center ↥L) l)
    · exact false_of_perfThreeCent hyp.perf hlfix hP
    · exact fixPerfThreeResidualD Y L J hyp.parab hyp.perf l hl3 hlfix (h8 (by omega)) hP

theorem fixPerfThreeVoid_d (hTri : FixPerfThreeTrialityD) : FixPerfThreeVoid (IsLieOf IdxD) := by
  intro Y _ _ L J u hyp hX
  by_cases hu : u ∈ L ⊔ Subgroup.centralizer (L : Set Y)
  · exact fixPerfThreeVoid_d_inner Y L J u hyp hu hX
  · obtain ⟨r, hr, hmodel, h8⟩ := exists_model_of_fixPerfThreeHyp_idxD hyp hX
    by_cases h5 : 5 ≤ r
    · have hq : CFSG.Open.IsQuasisimple ↥L := hyp.parab.comp.2.2
      have : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hq.1
      exact hu (mem_sup_centralizer_of_model_pomegaPlus this h5 hmodel hyp.norm hyp.pow)
    · exact hTri Y L J u hyp hu (h8 (by omega))

end Void

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
