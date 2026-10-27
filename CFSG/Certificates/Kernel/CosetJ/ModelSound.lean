module

public import Certificates.Data.Kernel.CosetJ.Model
public import Certificates.Data.HePresCheck
public import CFSG.Certificates.Kernel.Misc.Coset.PG
import CFSG.Certificates.Kernel.CosetJ.ModelKS

public section

namespace CFSG.KC.CosetJ.Model

open CFSG.ComponentClassification.AS81.HePres.Native CFSG.KC.MiscCoset

theorem modelK_sound {k n : ℕ} {gens : Array (Array ℕ)} {rels : List (List (Fin k × Bool))}
    {I : List (List ℕ)} (h : modelK n k (gens.toList.map Array.toList) I (rels.map encW) = true) :
    modelCheck n gens rels = true := by
  exact ModelKS.modelCheck_of_modelK h

end CFSG.KC.CosetJ.Model

end
