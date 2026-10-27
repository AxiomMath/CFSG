module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentSocleQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieG2

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

theorem tabIdentFor_coverG24
    : TabIdentFor @Ident.FamCoverG24 := by
  intro G _ _ X K t hs hX
  obtain ⟨-, hZc, hmodel⟩ := hX
  exfalso
  have hπ : Function.Surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) :=
    QuotientGroup.mk'_surjective _
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥X)).ker = Subgroup.center ↥X := by
    rw [QuotientGroup.ker_mk', hZc]
  have hK := hs.hasKComponent_fix_quot hs.ktype (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) hπ hker
  exact g2Even_core (f := 2) le_rfl hmodel
    (Tab.quotAct (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) hπ hker hs.tN)
    (Tab.quotAct_mul_self (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) hπ hker hs.tN hs.sq) hK

end CFSG.QuasithinUnique.Id2519
