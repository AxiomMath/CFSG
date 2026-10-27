module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13g
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma137b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input185
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input223
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma136
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

section Comp133

namespace Bridges2

theorem lemma133_comp_holds : Sec13g.Lemma133_compStatement := by
  intro G _ _ m p B M E A D T h L hL
  have hp : p.Prime := h.standing.prime
  obtain ⟨g, hg, L0, hL0, rfl⟩ := Lemma137b.istar_component' hp hL
  exact glaPComponent_conj_mem hL0.1 hg

end Bridges2

end Comp133

theorem lemma114_of_inputs' (hI : Input185.Input7_10_1) : Lemma114Statement :=
  lemma114_of_inputs (Input185.input18_5_of_I710 hI)

section Layer183

theorem lemma136_of_inputs' (hP95 : Prop95) (h111 : Prop111Statement)
    (h121 : Prop121_of_cexStatement) (hcomp : Sec13_compStatement) (hP1 : Lemma136.P1BarInput)
    (hO2 : Cex134_O2Statement) (h121c : Prop121_corStatement) (hII : Lemma136.IIHardInput) :
    Lemma136Statement :=
  lemma136_of_inputs hP95 h111 h121 hcomp input22_3_2_holds hP1 hO2 h121c hII

end Layer183

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
