module

public import Certificates.Certificate4999

public section

namespace CFSG.QuasithinUnique.Ch1.AltSix
open Equiv Equiv.Perm CFSG.QuasithinUnique

theorem total_inj : ∀ i j : Fin 6, total i = total j → i = j :=
  Certificates.certificate4999.1

theorem total_closed_gen : ∀ (a : Fin 5) (i : Fin 6),
    ∃ j : Fin 6, act (swap a.castSucc a.succ) (total i) = total j :=
  Certificates.certificate4999.2

end CFSG.QuasithinUnique.Ch1.AltSix
