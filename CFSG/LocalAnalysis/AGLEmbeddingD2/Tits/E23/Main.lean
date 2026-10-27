module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.Clauses
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.Baumann
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.BaumannGen
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.MinPar

public section

namespace CFSG.AGLEmbeddingD2.Tits.E23

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Open CFSG.QuasithinUnique CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.BHS5

section Ambient

variable {G : Type} [Group G] [Finite G] {H T M : Subgroup G}
  (hV : IsElemAbelian 2 (VZ T H)) (hmin : MinParabolic H T M) (hmp : MinPar H T M)
  (hF : CharTwo H) (hred : IsTwoReducedIn H (VZ T H))
  (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T H : Set G))

include hmin hmp hF hred hJ


theorem natCase_baum_res
    (hall : ∀ L ∈ famI M hV, ∃ n : ℕ, E2.IsL2Natural L (fixV (autI hV (twoResidual H))) n) :
    IsSylowTwoOf (baum T) (twoResidual H ⊔ baum T) := by
  obtain ⟨h1, h2⟩ := natCase_baum_sylow hV hmin hmp hF hred hJ hall
  obtain ⟨g, hgL, hgen, hrank⟩ :=
    exists_baumannGen_of_nat hV hmin hmp hF hred hJ (hnat_of_all hV hmin hmp hF hred hJ hall)
  exact isSylowTwoOf_baum_of_nat hV hmin hred hJ
    (not_strong_of_hyp51 (hyp51_of_e23 hV hmin hmp hF hred hJ) (fun v => IntMod.sq_eq_one v)
      (autI_mono hV hmin.isSylow.1))
    h1 h2 (autI_mono hV (E2.twoResidual_le_thompsonJ hmin hred hJ)) hgL hgen hrank

theorem famI_e23FamGen : GN.E23FamGen H T (VZ T H) hV (famI M hV) := by
  obtain ⟨h1, h2, h3, h4⟩ := famI_basic hV hmin hmp hF hred hJ
  refine ⟨h1, h2, h3, h4, famI_type hV hmin hmp hF hred hJ, fun hall => ?_,
    fun m hm hall => symCase hV hmin hmp hF hred hJ hm hall⟩
  obtain ⟨hb, hs⟩ := natCase_baum_sylow hV hmin hmp hF hred hJ hall
  exact ⟨hb, hs, natCase_baum_res hV hmin hmp hF hred hJ hall⟩

end Ambient

theorem e23NonsolvGen : GN.E23NonsolvGen := by
  intro G _ _ H T M hV hmin hF hred hJ _
  exact ⟨famI M hV, famI_e23FamGen hV hmin (minPar_of_minParabolic hmin) hF hred hJ⟩

end CFSG.AGLEmbeddingD2.Tits.E23
