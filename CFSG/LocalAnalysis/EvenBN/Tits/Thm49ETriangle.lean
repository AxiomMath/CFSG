module

public import CFSG.LocalAnalysis.EvenBN.Tits.Thm49ESwap
public import CFSG.LocalAnalysis.EvenBN.Tits.Thm49ETheta

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.Thm49E

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits.Model

theorem Ctx.false_of_facts {G : Type} [Group G] (c : Ctx G) {zp y0 : Equiv.Perm (Fin 1755)}
    (hF6 : F6Facts zp y0) (hTO : TOHat zp y0) : False := by
  obtain ⟨z, z', y₁, v, hz, hz', hy, hΦz, hΦz', hΦy, hvP, hvQ, hvR⟩ := c.exists_swap hF6
  exact c.false_of_swap hF6 hTO hz hz' hy hΦz hΦz' hΦy hvP hvQ hvR

end CFSG.LocalAnalysis.EvenBN.Tits.Thm49E
