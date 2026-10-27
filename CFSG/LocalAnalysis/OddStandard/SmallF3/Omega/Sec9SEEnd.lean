module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEFin2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SCMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SF5

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Sec9_false_of_inputs (hsh : Asc82Shapes) (h36 : Asc82Lemma36) (h37 : Asc82Lemma37)
    (h66 : Asc82Lemma66) (h68 : Asc82Lemma68) (h82 : Asc82Lemma82) (hB8 : Asc82Sec8B)
    (h6 : Asc82Tab6M) (hT9 : Asc82Tab9M) (hN : Asc82NormA6) (hCos : Asc82Sec9Cos) :
    ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G)
      (t₀ : G), Sec9Ctx G t L S z g B t₀ → False :=
  asc82Sec9_false (asc82Lemma91_of_tab h36 h37 h66 h82 h6 hB8)
    (asc82Fink9E1_of h36 h68 hB8 hT9 h6 hN)
    (asc82Sec9NoE1_of hsh h36 h68 hB8 hT9 h6 hN hCos)

end CFSG.OddStandard.SmallF3.Omega
