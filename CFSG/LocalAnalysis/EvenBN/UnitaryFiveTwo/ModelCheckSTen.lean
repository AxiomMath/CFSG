module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckSSix
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckSThree

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer

theorem normalizer_Ssub_le_normalizer_A₁sub :
    normalizer (Ssub : Set SU52) ≤ normalizer (A₁sub : Set SU52) := fun n hn => by
  rw [normalizer_A₁sub]
  exact mem_centralizer_singleton_iff.2 (comm_zSU_of_mem (mul_mem (inv_mem zSU_mem)
    (normalizer_Ssub_conj_mem_ZX₄sub hn zSU_mem)))

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
