module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.Abelian
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.ReeG2Outer

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower

section


open CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc in
theorem p1OffCharAlmostSimpleNonNormalAt_reeG2 {m : ℕ}
    (hv : (TauCeti.LieTypeIndex.reeG2 m).Valid) :
    CFSG.AGLEmbedding.P1OffCharAlmostSimpleNonNormalAt ⟨.reeG2 m, hv⟩ := by
  have hiso : CFSG.RankThree.PartOne.Census3.IsoLie
      (TauCeti.CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group (.reeG2 m) :=
    ⟨hv, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨X, _, _, _, hm1, hXcard, ⟨e⟩⟩ := exists_reeG2_model hiso
  have hcyc := isCyclic_outer_reeG2 hm1 hXcard
  exact p1OffCharAlmostSimpleNonNormalAt_of_outerComm
    (OuterComm.of_mulEquiv e (outerComm_of_isCyclic_outer hcyc))

end

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower
