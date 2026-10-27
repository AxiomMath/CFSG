module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroPartner
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroEight
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroClean

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G]

theorem isComponent_of_map_conj_eq_of_l34PartnerConfig
    (hcat : L34CyclicProperFixedCatalog)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hG : L34BaseSetting G) (hhost : L34ZeroHostFree G) {V P Q : Subgroup G}
    (hcfg : L34PartnerConfig V P Q) {b : G}
    (hb : orderOf b = 2) (hbP : b ∈ centralizer (P : Set G))
    (hbQ : Q.map (MulAut.conj b).toMonoidHom = Q) :
    P ≤ centralizer ({b} : Set G) ∧ IsComponent (P.subgroupOf (centralizer ({b} : Set G))) := by
  have hPb : P ≤ centralizer ({b} : Set G) := fun p hp =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hbP p hp)
  refine ⟨hPb, ?_⟩
  have hQP : Q ≤ centralizer (P : Set G) := le_centralizer_iff.mp hcfg.le_centralizer
  obtain ⟨x, hxY, hx⟩ := exists_involution_mem_commutator_inf_centralizer_of_l34Odd
    hcfg.isQuasisimple_right hcfg.odd_card_center_right hcfg.isL34Type_right hb hbQ
  have hYY : ⁅Q ⊓ centralizer ({b} : Set G), Q ⊓ centralizer ({b} : Set G)⁆ ≤
      Q ⊓ centralizer ({b} : Set G) :=
    Subgroup.commutator_le.mpr fun a ha c hc => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hc) (inv_mem ha)) (inv_mem hc)
  have hxQb := hYY hxY
  obtain ⟨hPx, hcompx⟩ :=
    isComponent_of_mem_of_l34PartnerConfig hcat hSch hU hheld hG hhost hcfg hxQb.1 hx
  obtain ⟨F, hFP, hFb, hF, hF8⟩ :=
    exists_elemAbelian_eight_of_mem_normalizer_of_l34PartnerConfig hcfg hb hbP hbQ
  have hW := wGroup_eq_bot_of_le_centralizer_of_l34 hG hcfg.isQuasisimple_left
    hcfg.odd_card_center_left hcfg.isL34Type_left hcfg.wGroup_left hFP hF hF8
  rcases isComponent_or_swappedBar_of_l34 hcat hSch hU hheld hG hhost hx hb hxQb.2 hPx hPb hcompx
      hcfg.odd_card_center_left hcfg.isL34Type_left hFP hFb hF hF8 hW with h | h
  · exact h
  · exact (false_of_l34ZeroSwappedBar_of_mem_commutator h (inf_le_left.trans hQP) inf_le_right
      hxY).elim

end CFSG.ComponentClassification.GrSLit.L34Sec5S
