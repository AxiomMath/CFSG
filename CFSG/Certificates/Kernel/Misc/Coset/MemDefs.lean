module

public import Certificates.Data.Kernel.Misc.Coset.Mem
public import Certificates.Data.Kernel.Bounds.Table
public import CFSG.Certificates.Kernel.CosetBounds

public section

namespace CFSG.KC.MiscCoset.Mem

@[expose] def codeN (l : ℕ × Bool) : ℕ := 2 * l.1 + (if l.2 then 0 else 1)

end CFSG.KC.MiscCoset.Mem

end
