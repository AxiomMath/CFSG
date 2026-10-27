module

public import CFSG.GH74.Generic.S1.KL3Disp
public import CFSG.GH74.Generic.S1.KL3L2
public import CFSG.GH74.Generic.S1.KL3L3
public import CFSG.GH74.Generic.S1.KL3G2
public import CFSG.GH74.Generic.S1.KL3ClForms
public import CFSG.GH74.Generic.S1.KL3ClLin

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

namespace CFSG.GH74.Generic.S1

theorem kl3Table_of_survL4 (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hL4 : KL3SurvL4) : KL3Table := by
  exact kl3Table_of_families
    ⟨kl3FamL2, kl3FamL3, kl3FamU3, kl3FamPSp4 hGA, kl3FamL4 hGA, kl3FamU4 hGA, kl3FamL5 hGA,
      kl3FamU5 hGA, kl3FamG2, kl3FamD4⟩ (kl3Surv_of_parts hL4 kl3SurvG2)

end CFSG.GH74.Generic.S1
