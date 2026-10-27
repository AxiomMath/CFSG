module

public import Certificates.Certificate9554

public section

namespace CFSG.AGLEmbedding.KFactProofs.Fi22Five

open CFSG.Monster.B.Co2

theorem card_closure_ge {G₁ G₂ : Equiv.Perm (Fin 3510)}
    (h₁ : Rep 3510 g1A G₁) (h₂ : Rep 3510 g2A G₂) :
    1045094400 ≤ Nat.card (Subgroup.closure ({G₁, G₂} : Set (Equiv.Perm (Fin 3510)))) :=
  Certificates.certificate9554 G₁ G₂ h₁ h₂

end CFSG.AGLEmbedding.KFactProofs.Fi22Five
