module

public import Certificates.Data.Kernel.Misc.Ree2

public section

namespace CFSG.KC.Misc.Ree2

open CFSG.Walter.Ree.Bombieri

@[expose] def shapeEnt (i j : ℕ) : PE :=
  if shapeL >>> (5 * (12 * i + j)) % 32 = 0 then 0
  else coefL.getD (shapeL >>> (5 * (12 * i + j)) % 32 - 1) 0

theorem atomL_getD (k : ℕ) (hk : k < 7) : atomL.getD k 0 = Elim.atomDef k := by
  interval_cases k <;> rfl

theorem ent_eq (i j : Fin 12) : Elim.ent i j = shapeEnt i j := by
  fin_cases i <;> fin_cases j <;> rfl

end CFSG.KC.Misc.Ree2

end
