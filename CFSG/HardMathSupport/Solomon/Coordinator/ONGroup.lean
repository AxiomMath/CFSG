module

public import CFSG.Sporadic.ON
public import CFSG.Sporadic.Bridge.ONSurj
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open

theorem inputONGroup_holds :
    UniquenessMaximal.InputONGroup := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have b' : CFSG.Blueprint.NativeSporadic.Carrier .ONan ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group := b
  have hs : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .ONan) :=
    CFSG.Sporadic.ON.isSimpleGroup_ON
  refine ⟨@MulEquiv.isSimpleGroup _ _ _ _ hs b'.symm, ?_⟩
  have h1 : Nat.card (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group = 460815505920 := by
    rw [← Nat.card_congr b'.toEquiv]
    exact CFSG.Sporadic.ON.card_ON
  rw [h1]
  unfold orderON
  norm_num

end CFSG.HardMathSupport.Solomon.Coordinator
