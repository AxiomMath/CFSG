module

public import Certificates.Certificate25240

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open CFSG.Sporadic.Fi22

@[expose] noncomputable def fuseEb0 : Subgroup J :=
  Subgroup.closure {x | x ∈ D ∧ x ∈ slvl 0}

theorem exists_conj_mem_fuseEb0
    {x : J} (hx : orderOf x = 2) :
    ∃ c : J, c * x * c⁻¹ ∈ fuseEb0 :=
  Certificates.certificate25240 hx

end CFSG.EvenSporadicStandard.TwoFi22.DS81
