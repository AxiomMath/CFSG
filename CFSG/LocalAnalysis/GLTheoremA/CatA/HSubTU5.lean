module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTM5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KSubTFacts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU

theorem u5_holds : KSubT.CompFact S9.isU5two S9.isU4two := by
  intro H _ _ J B d hJq hcat hdB hI hd3 hdJ K hK
  obtain ⟨e0⟩ := bridge_u5two_stated hcat
  haveI := M5_nontrivial
  exact comp_of_inner hJq (hI.1 hdB) hd3 hdJ e0
    (fun α h => exists_conj_of_pow_three α h)
    (fun s h3 h1 L hL => M5_comp h3 h1 hL) K hK

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end
