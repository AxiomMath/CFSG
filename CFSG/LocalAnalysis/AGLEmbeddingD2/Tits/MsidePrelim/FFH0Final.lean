module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.FFH0
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.InvariantCyclic

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsidePrelim

theorem invariantCyclicSupplement : InvariantCyclicSupplement :=
  fun _ _ _ _ _ _ _ hDN₀ hN₀W hWD hWN₀ h3 hodd hS hSW hSN₀ hSD =>
    OrdinaryProofs.InvariantCyclic.exists_invariant_cyclic_supplement hDN₀ hN₀W hWD hWN₀
      h3 hodd hS hSW hSN₀ hSD

theorem ffH0Data : FFH0Data := ffH0Data_of_supplement invariantCyclicSupplement

end CFSG.AGLEmbeddingD2.Tits.MsidePrelim
