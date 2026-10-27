module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.Janko
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly CFSG.ProperTwoGeneratedCore.TheoremC
open CFSG.ShultStronglyClosedTI

@[expose] def JankoConfigurationJOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (H : Subgroup G) (z : G),
    CoreSetting G S H → IsCentralInvolution (S : Subgroup G) z →
      ¬ Subgroup.centralizer ({z} : Set G) ≤ H → JankoConfiguration G S z →
        Nonempty (G ≃* properTwoGenCoreJ1)

theorem jankoConfigurationJOne_of_oddCore (hO : CentralOddCoreTrivial) :
    JankoConfigurationJOne := by
  intro G _ _ S H z hset hz hesc hconf
  obtain ⟨hJ⟩ := jankoConfigurationJanko G S z hset.simple hz hconf (hO G S H z hset hz hesc hconf)
  obtain ⟨e⟩ := hJ.nonempty_mulEquiv_walterJ1
  exact ⟨e.trans (MulEquiv.subgroupCongr CFSG.Walter.walterJ1_eq_properTwoGenCoreJ1)⟩

end CFSG.ProperTwoGeneratedCore.Lemma37
