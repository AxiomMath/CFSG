module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM23Data

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.M23Insp
open scoped Pointwise
open CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1

@[expose] def enc (x : Fin 5 → Fin 23) : ℕ :=
  (x 0 : ℕ) + 23 * ((x 1 : ℕ) + 23 * ((x 2 : ℕ) + 23 * ((x 3 : ℕ) + 23 * (x 4 : ℕ))))

end CFSG.QuasithinUnique.Vol2Native.L239.M23Insp
