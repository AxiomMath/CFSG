module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM22Data

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.M22Insp
open scoped Pointwise
open CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.QuasithinUnique.Setup.X1

@[expose] def enc (x : Fin 4 → Fin 22) : ℕ :=
  (x 0 : ℕ) + 22 * ((x 1 : ℕ) + 22 * ((x 2 : ℕ) + 22 * (x 3 : ℕ)))

end CFSG.QuasithinUnique.Vol2Native.L239.M22Insp
