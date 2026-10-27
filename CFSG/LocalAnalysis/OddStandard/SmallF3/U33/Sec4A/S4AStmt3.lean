module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL45
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL46
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL47C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL47D
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL47E

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem lemma4_5 (hc : Ctx4 t L S x₁ x₂ lam rho tau) : Lemma4_5Concl t S x₁ x₂ tau :=
  S4A.lemma4_5_of hc.toCtx hc.l42 hc.l43 hc.l44.1

theorem lemma4_6 (hc : Ctx4 t L S x₁ x₂ lam rho tau) : Lemma4_6Concl t S x₁ x₂ tau :=
  S4A.lemma4_6_of hc.toCtx hc.l43 hc.l44.1

theorem lemma4_7 (hc : Ctx4 t L S x₁ x₂ lam rho tau) : Lemma4_7Concl t S x₁ x₂ lam tau :=
  ⟨S4A.lemma4_7a_of hc.toCtx hc.l43 hc.l44.1, S4A.lemma4_7b_of hc.toCtx hc.l43 hc.l44.1,
    S4A.lemma4_7c_of hc.toCtx hc.l43 hc.l44.1, S4A.lemma4_7d_of hc.toCtx hc.l43 hc.l44.1,
    S4A.lemma4_7e_of hc.toCtx hc.l43 hc.l44.1⟩

end CFSG.OddStandard.SmallF3.HarrisU33
