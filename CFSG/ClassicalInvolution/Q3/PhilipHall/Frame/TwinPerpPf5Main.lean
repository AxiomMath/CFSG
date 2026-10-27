module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5Stmt
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5Std
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPfMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf2Conj

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame


theorem twinPerp25A_of_9_fourP {n : ℕ} (hE : TwinThmE.EIHAll n) (h9 : Q8P.Asc77.C25_9P)
    (h4 : Q8P.Asc77.C25_11FourP) : TwinPerp25A n := by
  intro Y _ _ R S t hP h2 hE4
  have hC := CoreData.of_S hP.core
  have := Q8P.coreLike_of_core hC
  obtain ⟨W, hW, htW⟩ := hC.exists_wset_mem
  have hall := muIsoE4_all hC.hyp (CoreAssembly.mem_conjClass_self _)
    (Inner.isUniqueInvolution_core hC.datum) hE4
  exact Q8P.tf4_of_le (genFittingFStar Y)
    (Q8P.tf4_of_core_E4 (Q8P.Asc77.c25_11_of_9_fourP h9 h4) hC hE hP.disc hP.perp h2 hW htW hall)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
