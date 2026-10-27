
module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.Centralization
public import CFSG.LocalAnalysis.SectionRank.Induction

@[expose] public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.Blueprint

theorem oddKernelCentralization : OddKernelCentralization :=
  fun _ _ _ hX C _ hC hodd hquot hrank =>
    Ccomm.odd_nilpotent_kernel_centralization hX C hC hodd hquot hrank

end CFSG.SectionRank
