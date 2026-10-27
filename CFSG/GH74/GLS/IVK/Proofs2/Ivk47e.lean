module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47eG2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47eD4
public import CFSG.GH74.GLS.IVK.Statements.Sec4c

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG.GH74.GLS.IVK Ivk47

theorem ivk_4_7e : IVK_4_7e := by
  intro K _ _ p n hp _ hK P
  refine ⟨?_, fun hG2 => (sylow_G2 hp (untwisted_of_lieModel_G2 hG2) P).2⟩
  rcases hK with hG2 | hD4
  · exact (sylow_G2 hp (untwisted_of_lieModel_G2 hG2) P).1
  · exact sylow_D4 hp (twisted_of_lieModel_D4 hD4) P

end CFSG.GH74.GLS.IVK.Proofs2
