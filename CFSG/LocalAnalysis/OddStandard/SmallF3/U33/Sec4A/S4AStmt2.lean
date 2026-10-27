module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL42
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL44

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem lemma4_2 (hG : Sec4Glob G) (hc : Ctx t L S x₁ x₂ lam rho tau) : Lemma4_2Concl S :=
  S4A.lemma4_2_of_simple hG.simple ((by norm_num : 4 ∣ 2 ^ 11).trans hG.dvd) hc

theorem lemma4_4 (hc : Ctx t L S x₁ x₂ lam rho tau) (h2 : Lemma4_2Concl S)
    (h3 : Lemma4_3Concl t) : Lemma4_4Concl t tau :=
  S4A.lemma4_4_of hc h2 h3

end CFSG.OddStandard.SmallF3.HarrisU33
