module

public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpEFour
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58NFm

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup

theorem evenAltPumpUp_of_inputs (hcore : EvenAltPumpInput) (hHN : HNPumpInput)
    (hA10 : A10PumpInput) : GSThmB.EvenAltPumpUp := by
  intro H _ _ hK M hM E hE hEN hE2 hEk T hTM hTE hT ⟨eT⟩
  obtain ⟨L, _, _, hLK, hLq, hLO, ⟨eL⟩, Q, hQ2, hQc, Tb, hTbF, hTb, ⟨eTb⟩⟩ :=
    exists_reduced_pump hK hM hE hEN hE2 hEk hTM hTE hT
  rcases evenAltAut_le_four hcore hHN hA10 hLK hLq hLO hQ2 hQc hTbF hTb (eTb.symm.trans eT) with
    ⟨n, h10, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact Or.inl ⟨n, h10, ⟨eL.symm.trans e⟩⟩
  · obtain ⟨eMS⟩ := GrSLit.nonempty_quotient_center_equiv_fusionZStar ↥M
    exact Or.inr ⟨eMS.symm.trans ((Sol78.centerQuotCongr eL).symm.trans e)⟩

end CFSG.ComponentClassification.EvenPump
