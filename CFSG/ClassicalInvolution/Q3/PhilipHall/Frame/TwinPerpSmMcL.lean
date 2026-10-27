module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmPair
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafMcL
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafBasic

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf


theorem leaf_mcl {n : ℕ} : TwinLeafS n fun F _ => NativeSporadic.IsSporadic F .McL :=
  TwinLeafS.of_no fun Y _ _ R S t h _ hF => by
    haveI := h.core.simple
    obtain ⟨e⟩ := hF
    exact false_of_outTwoCyclic_of_noTwinPair h
      (Nobq.OutTwoCyclic.of_mulEquiv e outTwoCyclic_mcl) (not_twinPair_mcl ⟨e⟩)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small
