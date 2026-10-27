module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.L32ASigma

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace L32A

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

omit [CFSG.GH74.QTGen4.Finite4 G] in

private theorem mem_normalizer_inf' {g : G} {A B : Subgroup G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  exact fun x => ⟨fun hx => ⟨(hA x).mp hx.1, (hB x).mp hx.2⟩,
    fun hx => ⟨(hA x).mpr hx.1, (hB x).mpr hx.2⟩⟩

end L32A

end CFSG.Quasithin.H13
