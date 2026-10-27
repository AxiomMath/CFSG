module

public import CFSG.GH74.QTGen4.Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.Skeleton
public import CFSG.Quasithin.EmptyFaithful.TopAssemblyNative
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.QTGen4

@[expose] def StageTheorem1531Counterexample_F4 : Prop :=
  ∀ (G : Type) [Group G] [Finite4 G] (T Mc M : Subgroup G),
    CFSG.Quasithin.quasithinQTFE14Cat G T Mc → CFSG.Quasithin.IsMf T Mc M →
    ¬ CFSG.Quasithin.SixModels G →
    ¬ CFSG.Quasithin.IsOFourPlusAction M (CFSG.Quasithin.VZ T M)

theorem stageTheorem1531Counterexample_F4_of_strong
    (closing : CFSG.Quasithin.StageTheorem1531_F4) :
    StageTheorem1531Counterexample_F4 :=
  fun G _ _ T Mc M hypothesis maximal _ => closing G T Mc M hypothesis maximal

structure CounterexampleParts_F4 : Prop where
  existence : CFSG.Quasithin.StageMfExists
  branches : CFSG.Quasithin.StageTheorem1513_F4
  closing : StageTheorem1531Counterexample_F4
  triality : CFSG.Open.QuasithinSixModelsTauCeti.TrialityD4ModelBridge
  tits : CFSG.Open.QuasithinSixModelsTauCeti.TitsModelBridge

theorem six_models_of_counterexample_parts_F4
    (existence : CFSG.Quasithin.StageMfExists)
    (branches : CFSG.Quasithin.StageTheorem1513_F4)
    (closing : StageTheorem1531Counterexample_F4)
    (G : Type) [Group G] [Finite4 G] (T Mc : Subgroup G)
    (hypothesis : CFSG.Quasithin.quasithinQTFE14Cat G T Mc) :
    CFSG.Quasithin.SixModels G := by
  classical
  by_contra counterexample
  obtain ⟨maximal, maximal_property⟩ := existence G T Mc hypothesis
  rcases branches G T Mc maximal hypothesis maximal_property with recognized | orthogonal
  · exact counterexample recognized.2
  · exact closing G T Mc maximal hypothesis maximal_property counterexample orthogonal

theorem nativeSixModels_of_counterexample_parts_F4

    (triality : CFSG.Open.QuasithinSixModelsTauCeti.TrialityD4ModelBridge)
    (tits : CFSG.Open.QuasithinSixModelsTauCeti.TitsModelBridge)
    (existence : CFSG.Quasithin.StageMfExists)
    (branches : CFSG.Quasithin.StageTheorem1513_F4)
    (closing : StageTheorem1531Counterexample_F4)
    (G : Type) [Group G] [Finite4 G] (T Mc : Subgroup G)
    (hypothesis : CFSG.Quasithin.quasithinQTFE14Cat G T Mc) :
    CFSG.Quasithin.NativeSixModels G :=
  CFSG.Quasithin.SixModels.toNative triality tits
    (six_models_of_counterexample_parts_F4 existence branches closing G T Mc hypothesis)

theorem stmt15_3_1_GH_of_counterexample_parts_F4

    (triality : CFSG.Open.QuasithinSixModelsTauCeti.TrialityD4ModelBridge)
    (tits : CFSG.Open.QuasithinSixModelsTauCeti.TitsModelBridge)
    (existence : CFSG.Quasithin.StageMfExists)
    (branches : CFSG.Quasithin.StageTheorem1513_F4)
    (closing : StageTheorem1531Counterexample_F4) : Stmt15_3_1_GH := by
  intro G _ _ context T Mc hypothesis
  haveI : Finite4 G := finite4_of_gen4 context.1
  change CFSG.Quasithin.NativeSixModels G
  exact nativeSixModels_of_counterexample_parts_F4 triality tits existence branches closing
    G T Mc hypothesis

end CFSG.GH74.QTGen4
