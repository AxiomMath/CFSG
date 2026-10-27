module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PointConfigCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC)

variable {G : Type} [Group G] [Finite G]

theorem pointConfig_of_exotic {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    (hfail : ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M) (hIH : LargerPrimesUnique G p) {x : G}
    (hgen : IsGenericPoint p P M x) (h5 : 5 ≤ p) {J : Subgroup G} (hE : ExoticNormal p M x J)
    (hT : ∃ (Q : Type) (_ : Group Q) (ψ : ↥J →* Q), Function.Surjective ψ ∧
      ψ.ker = (rankThreePrimeCore p J).subgroupOf J ∧ Typ p Q) :
    PointConfig Typ G p P M x J :=
  ⟨hp, hM, hfail, hIH, hgen, h5, hE.le_centralizer, hE.centralizer_le, hE.perfect, hE.lt_core,
    hE.minimal, hE.not_le, hT⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
