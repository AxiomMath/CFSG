module

public import CFSG.Quasithin.EmptyFaithful.SBd4Five
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S153D50
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S153G24

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

namespace SBd4

theorem input15324M_of_narrow_F4 (h113 : StageLemma14113) (h4 : L4Four_F4) (h5 : L4FiveMin) :
    Input15324M_F4 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hc
  refine ⟨fun hq => ?_, fun hq => h5 G T Mc M V₁ V₂ Yp I L t c hc hq⟩
  obtain ⟨hU, hLC⟩ := h4 G T Mc M V₁ V₂ Yp I L t c.toCtx15316 hc hq
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.toCtx15313L.ctx.hyp
  have hLc : L ∈ cComp (thompsonJ I) := c.toCtx15313L.conc.1
  have hLn : ¬ L ≤ M ⊓ I := c.toCtx15313L.conc.2.1
  have hLle : L ≤ I := le_of_mem_cComp (S153D.mem_cComp_of_mem_cComp_thompsonJ hLc)
  have hNM : Subgroup.normalizer (V₁ : Set G) ≤ M :=
    (Hyp153.normalizer_V_le h113 hh.hyp hh.decomp hU.1).1
  exact hLn (le_inf (fun l hl => hNM (Subgroup.centralizer_le_normalizer _ (hLC hl))) hLle)

end SBd4

end CFSG.Quasithin
