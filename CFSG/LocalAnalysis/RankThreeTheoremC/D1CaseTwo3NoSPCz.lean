module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPCz
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoData3.exists_surjective_czQuot (hd : D1CaseTwoData3 p P M H R Rbar)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤) {z : H}
    (hzp : orderOf (z : G) = p)
    (hzL : QuotientGroup.mk' (primeComplementCore (G := H) p) z ∈
      Subgroup.centralizer (L : Set (H ⧸ primeComplementCore (G := H) p))) :
    ∃ (A : Subgroup (D1CzQuot p (z : G))) (f : A →* L), Function.Surjective f :=
  D1CaseTwoDataAt.exists_surjective_czQuot (hd := hd.toAt) (hL := hL) (hzp := hzp) (hzL := hzL)

end Config

end CFSG.LocalAnalysis.RankThreeTheoremC
