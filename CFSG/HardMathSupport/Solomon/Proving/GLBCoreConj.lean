module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.SylowTransport

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.Open

theorem GLBCore_gLBConj {p k : ℕ} {G : Type} [Group G] [Finite G] (g : G) (P : Subgroup G) :
    GLBCore p k (GLBConj g P) = GLBConj g (GLBCore p k P) :=
  CFSG.AGLEmbedding.Norton.OrdinaryProofs.GLBCore_map_conj (p := p) (k := k) g⁻¹ P

end CFSG.HardMathSupport.Solomon.Proving

end
