module

public import CFSG.Quasithin.EmptyFaithful.S153D16
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S153DC27

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

namespace S153D

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

section Setting

theorem lemma_15_3_16_F4
    (hC27 : ASC27Statement_F4 G) (hin : Input15316One) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (c : Ctx15313L T Mc M V₁ V₂ Yp I L t) : Concl15316 T M V₁ Yp I L := by
  obtain ⟨hLc, hLn, hL3, -, -, hLq⟩ := c.conc
  have hLI : L ∈ cComp I := mem_cComp_of_mem_cComp_thompsonJ hLc
  obtain ⟨hYL, hRL, -⟩ :=
    lemma_15_3_12_one h37 h38 c.ctx.hyp c.ctx.inH c.facts c.ctx.rank hLI hL3
  have hO := pCoreOf_sup_R153_le c.facts hLI hLq hRL
  have hcharL : CharTwo L :=
    charTwo_of_isSubnormal_of_charTwo c.ctx.charTwo (subnormal_of_mem_cComp hLI)
  have hdesc := c27Concl_of_statement_F4 hC27 (lemma_15_3_15_one c.ctx.hyp c.ctx.inH c.facts) hLI hLq
    hcharL hLn hRL rfl
  have hRp : IsPGroup 2 (R153 T V₁ Yp) := pCoreOf_isPGroup 2 _
  have hLeq := comm_thompsonJ_eq hLI.2.1 hLq hRp hRL hO hdesc.2.1.1
  obtain ⟨hR1, hR2⟩ := hin G T Mc M V₁ V₂ Yp I L t c hRL hO hdesc
  exact ⟨hR1, hR2, isQuasisimple_autOn_WL c.ctx.hyp c.ctx c.facts hLI hLn hLq hRL hO, hYL, hRL,
    hLeq, hdesc⟩

end Setting

end S153D

end CFSG.Quasithin
