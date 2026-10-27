module

public import CFSG.CGT.L5R.Assembly
public import CFSG.CGT.L5R.Model
public import CFSG.CGT.L5R.WrapTop
public import CFSG.CGT.M24S.CaseL
public import CFSG.CGT.L5R.WrapCtx

public section

namespace CFSG.CGT.L5R

open CFSG.CGT.Timmesfeld75 CFSG.CGT.M24S

theorem caseLInput_of_parts (hN8 : N8StatementL) (hL2 : N8StatementL → L2StatementL)
    (hR3 : R3StatementL) (hR5 : R5Statement) (hHolt : CFSG.Holt.H78.HoltTheorem1) :
    CFSG.CGT.M24S.CaseLInput := by
  intro G _ _ _ hna T H hTH hT hN hodd h4
  have h : Hyp T H := ⟨hTH, hT, hN, hodd⟩
  have hL := h.localFacts
  have hC : Subgroup.centralizer (T : Set G) = T := centralizer_eq_self hna hHolt h hL
  obtain ⟨T₁, hyp⟩ := exists_l52CtxHyp hHolt h hL hC (hasComplement_of_hyp hHolt h hL hC) h4
  obtain ⟨c, hle, φ, hφ⟩ := exists_mulEquiv_l52_of_parts hN8 hL2 hR3 hR5 hyp
  have htop := eq_top_of_mulEquiv_l52 hHolt h hL h4 (le_sup_left.trans hle) φ
    (fun j : Fin 4 => c.gens ⟨6 + j.val, by omega⟩) (fun _ => Subgroup.subset_closure ⟨_, rfl⟩)
    c.eq_closure_t (fun j => (hφ _).trans (l52M_six_add j))
  exact statedClassicalModel_psl52_of_mulEquiv
    ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans φ⟩

end CFSG.CGT.L5R
