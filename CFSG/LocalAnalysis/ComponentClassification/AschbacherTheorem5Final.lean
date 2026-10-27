module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Assembly
public import CFSG.Goldschmidt.Final

public section

open CFSG.Open

namespace CFSG.ComponentClassification.AschbacherTheorem5

theorem conclusion_holds :
    ∀ (G : Type) [Group G] [Finite G] (D : Subgroup G) (r : ℕ)
      (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)),
      Hyp61 G D r Abar → Subgroup.normalizer (D : Set G) ≠ ⊤ → Conclusion G D r Abar :=
  conclusion_of_topStatement CFSG.Goldschmidt.topStatement

end CFSG.ComponentClassification.AschbacherTheorem5
