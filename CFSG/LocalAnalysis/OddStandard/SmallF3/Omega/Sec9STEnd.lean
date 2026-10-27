module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9STOut
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9STTr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEEnd

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Tab9M_of (hT6 : Asc82Tab6M) : Asc82Tab9M :=
  ⟨sec9t_i3_outer, sec9t_cent_B_i3 hT6⟩

theorem asc82Sec9_false_of_tab6 (hsh : Asc82Shapes) (h36 : Asc82Lemma36) (h37 : Asc82Lemma37)
    (h66 : Asc82Lemma66) (h68 : Asc82Lemma68) (h82 : Asc82Lemma82) (hB8 : Asc82Sec8B)
    (h6 : Asc82Tab6M) (hN : Asc82NormA6) (hCos : Asc82Sec9Cos) :
    ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G)
      (t₀ : G), Sec9Ctx G t L S z g B t₀ → False :=
  asc82Sec9_false_of_inputs hsh h36 h37 h66 h68 h82 hB8 h6 (asc82Tab9M_of h6) hN hCos

end CFSG.OddStandard.SmallF3.Omega
