module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O98Defs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35GoodLie
public import CFSG.RankThree.PartOne.TCB.Final
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicOuter
import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.Open CFSG.RankThree.PartOne

namespace K35

theorem k35Good_of_isCatalogGroup {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hnab : ∃ a b : T, a * b ≠ b * a) (hcat : IsCatalogGroup T) : K35Good T := by
  rcases PlaneCases.catalog_cases (TCB.tauCetiCatalogBridge T hnab hcat) with
    ⟨q, -, ⟨e⟩⟩ | ⟨n, hn5, ⟨e⟩⟩ | ⟨t, n, ℓ, f, -, hmodel⟩ | ⟨s, ⟨e⟩⟩
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · exact K35Good.of_mulEquiv e (k35Good_of_not_nine_dvd fun h9 =>
      CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn5 3 Nat.prime_three (by norm_num)
        ((by norm_num : 3 ∣ 9).trans h9))
  · exact k35Good_of_lieModel hmodel
  · obtain ⟨e'⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s
    exact K35Good.of_mulEquiv (e.trans e') (k35Good_of_not_nine_dvd fun h9 =>
      CFSG.AGLEmbedding.not_dvd_card_outer_sporadic
        CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s 3 Nat.prime_three (by norm_num)
        ((by norm_num : 3 ∣ 9).trans h9))

end K35

theorem kFactThreeFiveInner_holds : KFactThreeFiveInner := by
  intro X _ _ hcat K E _ hKq _ hE hE9 h23 hΓ _
  haveI : Group.IsPerfect K := hKq.1
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hKq.2.1
  exact K35.exists_inner_of_k35Good K E hE hE9 h23 hΓ (K35.k35Good_of_isCatalogGroup hKq.2.2
    (hcat K (Subgroup.center K) inferInstance hKq.2.1 hKq.2.2))

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
