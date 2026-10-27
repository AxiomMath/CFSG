
module


public import Certificates.Certificate17030

public section

namespace CFSG.QuasithinUnique.A5.Kc3Cover

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5

variable {G : Type} [Group G] (K : Subgroup G)

theorem fixed_alt_zero' : ∀ v : Fin 5 → ZMod 2, isEven v →
    (∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 → pact σ v = v) → v = 0 :=
  Certificates.certificate17030

end CFSG.QuasithinUnique.A5.Kc3Cover

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Kc3Cover

end CFSG.QuasithinUnique.A5
