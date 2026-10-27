module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralPerfectLifts

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

namespace AltThreeRank

open Equiv

theorem sign_viaEmbeddingHom {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (ι : α ↪ β) (e : Perm α) :
    Perm.sign (Perm.viaEmbeddingHom ι e) = Perm.sign e :=
  @Perm.sign_extendDomain α _ β _ _ _ e (fun b => b ∈ Set.range ι)
    (fun _ => Classical.propDecidable _) (Equiv.ofInjective ι.1 ι.2)

end AltThreeRank

end CFSG.AGLEmbeddingD2
