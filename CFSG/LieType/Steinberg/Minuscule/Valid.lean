module

public import CFSG.LieType.Steinberg.Minuscule.ValidInputs
public import Certificates.Certificate116

public import CFSG.LieType.Steinberg.Minuscule.Ops
public import CFSG.LieType.Steinberg.Basic
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115

public noncomputable section

namespace CFSG.LieType.Steinberg.Minuscule

open CFSG.Blueprint.Chevalley

namespace MinData

variable {τ : Tag} (D : MinData τ)

namespace Valid

variable {D} (hV : D.Valid)
include hV

end Valid

end MinData

theorem e6Data_checkExtra : e6Data.checkExtra = true := by
  exact Certificates.certificate116.1

theorem e7Data_checkExtra : e7Data.checkExtra = true := by
  exact Certificates.certificate116.2

theorem e6Data_valid : e6Data.Valid := ⟨e6Data_check, e6Data_checkExtra⟩

theorem e7Data_valid : e7Data.Valid := ⟨e7Data_check, e7Data_checkExtra⟩

end CFSG.LieType.Steinberg.Minuscule
