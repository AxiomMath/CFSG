module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcF4Vanish
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpine
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Transport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Cover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Layer
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs95
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma95A

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LocalAnalysis.GLTheoremA.T173
  CFSG.LocalAnalysis.GLTheoremA.T173X

section Assembly


theorem i173OOn_famExcSplit : I173OOn famExcSplit := by
  intro p Ω _ _ S B N D K x lab hcfg hlab hfam hmark
  obtain ⟨htag, hpq, hp3⟩ := hfam
  have hE6 : lab.tag = .E6 → p ≠ 3 ∨ lab.n = 1 := fun h => Or.inl (hp3 h)
  obtain ⟨τ, F, hF, hFin, hFinAdj, hτlab, hcard, hZ, ⟨M⟩⟩ :=
    exists_model_exc hcfg hlab htag hE6 hmark
  letI : Field F := hF
  letI : Finite F := hFin
  letI : Finite ↥(adjointGroup τ F) := hFinAdj
  rcases hτlab with ⟨h4, rfl⟩ | ⟨h6, rfl⟩ | ⟨h7, rfl⟩ | ⟨h8, rfl⟩
  · exact concl_of_modelFactO hcfg M hZ (ModelFactV.modelFactO
      (modelFactExcSplit_F4 F lab.n p hcard hcfg.prime hcfg.odd hpq (fun h => by cases h)))
  · exact concl_of_modelFactO hcfg M hZ (ModelFactV.modelFactO
      (modelFactExcSplit_E6 F lab.n p hcard hcfg.prime hcfg.odd hpq (fun _ => hp3 h6)))
  · exact concl_of_modelFactO hcfg M hZ (ModelFactV.modelFactO
      (modelFactExcSplit_E7 F lab.n p hcard hcfg.prime hcfg.odd hpq (fun h => by cases h)))
  · exact concl_of_modelFactO hcfg M hZ (ModelFactV.modelFactO
      (modelFactExcSplit_E8 F lab.n p hcard hcfg.prime hcfg.odd hpq (fun h => by cases h)))

end Assembly

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
