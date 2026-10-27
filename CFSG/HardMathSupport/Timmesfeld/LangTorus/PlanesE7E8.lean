module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerBase

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge

set_option linter.unusedSectionVars false

theorem center_eq_bot_of_mulEquiv_adjointGroup {C : Type*} [Group C] {τ : Tag} {K : Type}
    [Field K] [Finite K] (e : C ≃* ↥(adjointGroup τ K)) : Subgroup.center C = ⊥ := by
  refine eq_bot_iff.2 fun z hz => ?_
  have hez : e z ∈ Subgroup.center ↥(adjointGroup τ K) := by
    refine Subgroup.mem_center_iff.2 fun g => ?_
    obtain ⟨c, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz c]
  rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hez
  exact Subgroup.mem_bot.2 (e.injective (hez.trans (map_one e).symm))

theorem center_catT_E7_eq_bot (q : TauCeti.PrimePower) (hv : (excIndex .E7 q).Valid) :
    Subgroup.center (CatT ⟨excIndex .E7 q, hv⟩) = ⊥ := by
  obtain ⟨K, _, _, -, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  exact center_eq_bot_of_mulEquiv_adjointGroup e

theorem center_catT_E8_eq_bot (q : TauCeti.PrimePower) (hv : (excIndex .E8 q).Valid) :
    Subgroup.center (CatT ⟨excIndex .E8 q, hv⟩) = ⊥ := by
  obtain ⟨K, _, _, -, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  exact center_eq_bot_of_mulEquiv_adjointGroup e

end CFSG.HardMathSupport.Timmesfeld.LangTorus
