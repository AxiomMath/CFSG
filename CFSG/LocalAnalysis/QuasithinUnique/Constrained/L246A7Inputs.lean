module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246A7Main

public section

namespace CFSG.QuasithinUnique

structure Lemma246InputsNoA7 : Prop where
  c127 : ∀ (G : Type) [Group G] [Finite G], L238.C127StatementCat (G := G)
  c123 : ∀ (G : Type) [Group G] [Finite G], L238.C123TwoCgsStatement (G := G)
  b42 : ∀ (G : Type) [Group G] [Finite G], L238.AltBlockStatementJCat (G := G)
  a38 : Vol2Native.A38ForSQTKCat

theorem lemma246Inputs_of_noA7 (hMB : MinParabolicBlocks) (h : Lemma246InputsNoA7) :
    Lemma246Inputs :=
  ⟨h.c127, h.c123, h.b42,
    fun G _ _ => L246A7.c129A7_of_inputs hMB (h.c127 G) (h.c123 G) (h.b42 G) h.a38, h.a38⟩

end CFSG.QuasithinUnique
