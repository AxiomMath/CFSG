module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S13812
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeKVocab
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative commutatorElement

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem d4_of_F4 (h139 : Stmt13_3_9_F4) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hK : K ∈ cComp H)
    (N : Subgroup G) (hN2 : IsPGroup 2 ↥N) (hLT : L ⊔ T ≤ Subgroup.normalizer (N : Set G))
    (hKN : K ≤ Subgroup.normalizer (N : Set G)) : N = ⊥ := by
  by_contra hN1
  have hloc : IsTwoLocal (Subgroup.normalizer (N : Set G)) := ⟨N, hN1, hN2, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hM := S.uniqueM.2 M' ⟨hM', hLT.trans hle⟩
  apply (S.lem13812_one_F4 h139 h37 h38 hH hK).1
  rw [← hM]
  exact hKN.trans hle

end Setting4

end CFSG.Quasithin.H13.A6
