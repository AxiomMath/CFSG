module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CFSG.KC.McL.TC

#kc_repo #kc_nat_items_gz CFSG.KC.McL.TC
  "CFSG/Certificates/Kernel/McL/Data/TC.items.gz" 572 9654946854117562533
  R[15]

@[expose] noncomputable def list : List Nat := [R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, R12, R13, R14]

end CFSG.KC.McL.TC

end

#kc_select CFSG.KC.McL.TC sel R 15
