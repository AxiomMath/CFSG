module

public import Certificates.Data.Kernel.Misc.PermGH23
public import Certificates.Data.GH23Perm

public section

namespace CFSG.KC.Misc.GH23

open CFSG.OddStandard.SmallF3.HarrisU33.GH23Data

theorem mul8_eq (a b : Nat) : mul8 a b = mulC a b := rfl

theorem one8_eq : one8 = oneC := rfl

end CFSG.KC.Misc.GH23

end
