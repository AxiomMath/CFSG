module

public import Certificates.Data.Thm49ECore
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.EvenBN.Tits.Model.Centralizers

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.Tits.Thm49E

open Subgroup Certificates.Thm49E CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.LocalAnalysis.EvenBN.Tits.Model

@[expose] def zpHat : Equiv.Perm (Fin 1755) := wordIn 4 titsGen zpWord

@[expose] def y0Hat : Equiv.Perm (Fin 1755) := wordIn 4 titsGen y0Word

theorem wordIn_mem_titsA' (w : List ℤ) : wordIn 4 titsGen w ∈ titsA :=
  wordIn_mem (fun _ hi => titsGen_mem_titsA hi) w

end CFSG.LocalAnalysis.EvenBN.Tits.Thm49E
