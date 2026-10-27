module

public import CFSG.Quasithin.Background.H12OneHatM22PfInputs
public import CFSG.Certificates.Kernel.M22KSound

public section

namespace CFSG.KC.H12K

open CFSG.Quasithin.H13.MatNCert CFSG.Quasithin.H13.M22Cert CFSG.KC.Mat8P CFSG.KC.MatNK
  CFSG.KC.M22K

theorem orbL_toT : CFSG.Quasithin.H.Mathieu.H12Cert.orbL =
    (orbBfsT CFSG.Quasithin.H.Mathieu.H12Cert.gG 100
      (insP (.tip []) CFSG.Quasithin.H.Mathieu.H12Cert.v0)
      [(CFSG.Quasithin.H.Mathieu.H12Cert.v0, [])]
      [(CFSG.Quasithin.H.Mathieu.H12Cert.v0, [])]).reverse := by
  rw [CFSG.Quasithin.H.Mathieu.H12Cert.orbL, orbBfs_toT]
  intro y
  rw [Std.HashSet.contains_insert, memP_insP, Std.HashSet.contains_empty, memP_empty]

end CFSG.KC.H12K

end
