module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Top
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6G2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Tits

public section

namespace CFSG.QuasithinUnique.Setup.X6

open CFSG.QuasithinUnique.Setup.X35 CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem no_even_G2_or_Tits_component
    (hT : ActorComponentTransfer)
    (hTits : TitsSylowOvergroupLattice) {V : Type} [CommGroup V] [Finite V]
    {H T M E : Subgroup (MulAut V)} (hA : ActorBase V H T M E) (hns : ¬ Group.IsSolvable H)
    {L : Subgroup (MulAut V)} (hL : IsComponentIn L H) :
    (∀ f : ℕ, ¬ ChevalleyExceptionalModel (↥L ⧸ Subgroup.center ↥L) .G2 2 f) ∧
      ¬ ReeTitsModel (↥L ⧸ Subgroup.center ↥L) .Tits 2 1 :=
  ⟨fun _ h => false_of_actorComponentTransfer hT hA hns hL
      (even_G2_model_two_extensions h).2.1,
    fun h => false_of_actorComponentTransfer hT hA hns hL
      (tits_model_two_extensions hTits h).2.2.2.1⟩

end CFSG.QuasithinUnique.Setup.X6
