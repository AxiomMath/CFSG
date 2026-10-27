
module

public import CFSG.GH74.GLS.Stage4.Q9.ModelBaseBase

public import Mathlib
public meta import Mathlib
public import CFSG.GH74.GLS.Stage4.Q9.ModelBaseInputs
public meta import CFSG.GH74.GLS.Stage4.Q9.ModelBaseInputs
public import Certificates.Certificate5100

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.GLS.Stage4.Q9

theorem ordL_ne_zero : ∀ l : Lg, ordL l ≠ 0 :=
  Certificates.certificate5100.1

theorem orderOf_Lg (l : Lg) : orderOf l = ordL l :=
  ordLAux_spec l 16 1 (normL l) (by rw [normL_eq, pow_one]) le_rfl
    (fun j hj1 hj => by omega) (ordL_ne_zero l)

end CFSG.GH74.GLS.Stage4.Q9
