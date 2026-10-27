module

public import CFSG.Certificates.Kernel.Spor.PCountWSound

public section

namespace CFSG.KS.PCnt

open CFSG.KC.Enum CFSG.KS.PK CFSG.Sporadic.Schreier

variable {n : Nat}

theorem pkw_one {w : Nat} (hn : n ≤ 2 ^ 24) (hw : n ≤ 2 ^ w) :
    pkw w (1 : Equiv.Perm (Fin n)) = pidn n w := by
  rw [pidn_eq hn hw]
  exact enc_congr fun i hi => by simp [pv, hi]

end CFSG.KS.PCnt

end
