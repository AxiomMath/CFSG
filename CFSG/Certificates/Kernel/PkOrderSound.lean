module

public import Certificates.Data.Kernel.PkOrder
public import CFSG.Certificates.Kernel.FootePkSound
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum

public section

namespace CFSG.Certificates.Kernel.FootePk

open CFSG.Certificates.Kernel.PkEnum CFSG.Sporadic.Schreier

variable {n : Nat}

theorem orderIs_pkp (a : VP n) (m : Nat) : orderIs (pkp a) m = orderIsV a m := by
  simp only [orderIs, orderIsV, ← pkp_oneV, ← pkp_powV, decide_eq_eqV]

theorem filter_length_pkp (L : List (VP n)) (p : Equiv.Perm (Fin n) → Bool) (q : VP n → Bool)
    (h : ∀ a, p (pkp a) = q a) : ((L.map pkp).filter p).length = (L.filter q).length := by
  rw [List.filter_map, List.length_map]
  congr 2
  funext a
  exact h a

end CFSG.Certificates.Kernel.FootePk

end
