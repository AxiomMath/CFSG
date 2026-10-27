module

public import CFSG.LocalAnalysis.EvenBN.Tits.Thm49ETriangle
public import CFSG.LocalAnalysis.EvenBN.Tits.Thm49EPhi
public import CFSG.LocalAnalysis.EvenBN.Tits.Sec4Nine

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.Thm49E

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits.Model

theorem thm49FailureExclusion_of_facts
    {zp y0 : Equiv.Perm (Fin 1755)} (hF6 : F6Facts zp y0) (hTO : TOHat zp y0) :
    Thm49FailureExclusion := by
  intro G _ _ d hd hfail
  obtain ⟨c⟩ := hd.nonempty_ctx (fun ⟨g, hg⟩ => hfail g hg)
  exact c.false_of_facts hF6 hTO

end CFSG.LocalAnalysis.EvenBN.Tits.Thm49E
