module

public import CFSG.HardMathSupport.Foote.E27.LieThree.SpSpecP
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeCCarrier

public section

namespace CFSG.HardMathSupport.Foote.E27

open TauCeti CFSG.Assembly.LowTwoRank

section Certificates

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem E27Config.false_of_typeC_three_three (h : E27Config X K R T z) (hz : z ∈ K)
    (q : PrimePower) (hv : (LieTypeIndex.C 3 q).Valid) (hq : q.p = 3 ∧ q.exponent = 1)
    (e : ↥K ≃* (CFSGIndex.lie ⟨.C 3 q, hv⟩).Group) : False := by
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC 3 q hv e
  rw [hq.1, hq.2] at hm
  obtain ⟨-, F, hF, hFin, hFcard, ⟨eK⟩⟩ := hm
  exact h.false_of_psp_three_three hz (by simpa using hFcard) eK

end Certificates

end CFSG.HardMathSupport.Foote.E27
