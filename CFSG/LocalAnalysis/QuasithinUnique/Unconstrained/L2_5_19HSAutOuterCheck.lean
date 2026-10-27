module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutClass
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutData
public import CFSG.Sporadic.SmallOddCore.HSAut
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutClass
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutData
public meta import CFSG.Sporadic.SmallOddCore.HSData
public meta import CFSG.Sporadic.SmallOddCore.CentData
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import Certificates.Data.CFSGNative.SmallOddCore.Check
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutOuterCheckInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutOuterE
public import Certificates.Certificate4064

public section

namespace CFSG.QuasithinUnique.Id2519.HSAut

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Th.Native

theorem outerE_facts :
    (allBelow 4 fun l => CFSG.Sporadic.SmallOddCore.permOK 3850 (qGenT l) &&
      (qGenT l).size == 3850) = true ∧
    qPerm 1 ∉ outerE ∧
    ∃ ρ : outerE →* Equiv.Perm (Fin 35), Nat.card ρ.range = 20160 ∧
      ∃ e : Fin classSizes.size ≃ ConjClasses ρ.range,
        (∀ l, Nat.card (e l).carrier = classSizes[l.val]!) ∧
        ∃ l₀ : Fin classSizes.size, l₀.val = 0 ∧ e l₀ = ConjClasses.mk 1 :=
  Certificates.certificate4064

end CFSG.QuasithinUnique.Id2519.HSAut
