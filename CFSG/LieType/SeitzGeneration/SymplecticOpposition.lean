module

public import CFSG.GroupTheory.OppositeRadicals
public import CFSG.Assembly.LowTwoRankDefs
import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUSp
import CFSG.LieType.SeitzGeneration.CentralOpposition
import CFSG.LieType.HighestRoot.ModelCenter

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Assembly.LowTwoRank CFSG.Open CFSG.GroupTheory

theorem hasGoodOppositePRadicals_statedSp {n r : ℕ} {F : Type} [Field F] [Finite F]
    [Fact r.Prime] [CharP F r] {Q : Subgroup (StatedSp n F)}
    (hQne : Q ≠ ⊥) (hQ : IsRadicalPGroup r ⊤ Q) : HasGoodOppositePRadicals r ⊤ Q :=
  CFSG.StandardType.GGOppRadSpU.hasGoodOppositePRadicals_sp hQne hQ

theorem hasGoodOppositePRadicals_of_statedSp {n r : ℕ} {F : Type} [Field F] [Finite F]
    [Fact r.Prime] [CharP F r] {L : Type*} [Group L] [Finite L]
    (ψ : StatedSp n F →* L) (hker : ψ.ker ≤ Subgroup.center (StatedSp n F))
    {Q : Subgroup L} (hQne : Q ≠ ⊥) (hQ : IsRadicalPGroup r ψ.range Q) :
    HasGoodOppositePRadicals r ψ.range Q :=
  hasGoodOppositePRadicals_of_lift ψ r hker
    (fun z hz hzr => CFSG.ComponentClassification.RankTwoOddLie.centerPPrime_statedSp n F z
      (hker hz) hzr)
    (fun _ h1 h2 => hasGoodOppositePRadicals_statedSp h1 h2) hQne hQ

end CFSG.LieType.SeitzGeneration
