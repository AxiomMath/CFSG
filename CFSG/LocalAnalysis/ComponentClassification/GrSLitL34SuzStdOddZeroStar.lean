module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroFixed
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroMoved

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G]

theorem star_of_l34PartnerConfig
    (hcat : L34CyclicProperFixedCatalog)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hG : L34BaseSetting G) (hhost : L34ZeroHostFree G) {V P Q : Subgroup G}
    (hcfg : L34PartnerConfig V P Q) :
    CGT.PushingUpLit.CGT6.Nine7.Star P := by
  intro b hb hPb
  have hbP : b ∈ centralizer (P : Set G) :=
    mem_centralizer_iff.mpr fun p hp => mem_centralizer_singleton_iff.mp (hPb hp)
  by_cases hbQ : Q.map (MulAut.conj b).toMonoidHom = Q
  · exact (isComponent_of_map_conj_eq_of_l34PartnerConfig hcat hSch hU hheld hG hhost hcfg hb hbP
      hbQ).2.2
  · exact (isComponent_of_map_conj_ne_of_l34PartnerConfig hcat hSch hU hheld hG hhost hcfg hb hbP
      hbQ).2.2

end CFSG.ComponentClassification.GrSLit.L34Sec5S
