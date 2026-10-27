module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTSp8
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTResGUIso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTResGUComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

theorem guBlockFacts_holds : GUBlockFacts := by
  intro E _ hE W _ _ _ Hf hHs hHl
  haveI : Finite E := hE.finite
  have hE4 : Nat.card E = 4 := by rw [hE.card]; norm_num
  obtain ⟨e⟩ := resGU_mulEquiv hE Hf hHs hHl
  refine ⟨fun hn => ?_, fun hn K hK => ?_⟩
  · haveI := resGU_solvable hE (Module.finrank E W) hn
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  · exact resGU_comp_four hE4 (resTau_apply hE) (resTau_invol hE) hn e K hK

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end
