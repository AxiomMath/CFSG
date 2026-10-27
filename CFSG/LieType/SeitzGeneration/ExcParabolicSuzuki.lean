module

public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
public import CFSG.LieType.SeitzGeneration.Inner
public import CFSG.LieType.SeitzGeneration.ExcParabolicModel
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.RankThree.PartTwo.Sec4.Census.BridgeSuzuki
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCyclic
public import CFSG.LieType.Simplicity.Suzuki

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint

theorem seitzExcParabolicFor_suzuki :
    SeitzExcParabolicFor IsSuzukiIndex := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, ⟨m, rfl⟩, -⟩
  exfalso
  have : Fact p.Prime := ⟨hp⟩
  have hmodel : SuzukiModel (Cat ⟨.suzuki m, hv⟩) 2 (2 * m + 1) :=
    CFSG.SectionRank.suzukiModel_of_mulEquiv (MulEquiv.refl _)
      (CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv)
  have hsimple := (CFSG.LieType.Simplicity.fam_2b2_simplicity _ 2 (2 * m + 1) hmodel).2
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨e⟩⟩ := hmodel
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [hF, hfa]
  have e' : Cat ⟨.suzuki m, hv⟩ ≃* CFSG.Open.GLASzGroup a F :=
    e.trans (MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a F))
  have : Finite (Cat ⟨.suzuki m, hv⟩) :=
    Finite.of_equiv _ e.symm.toEquiv
  have hsyl := CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.suzuki_model_oddSylow_cyclic
    a ha hF' e'
  have hinj := conj_injective_of_simple_of_range_ne_bot (range_conj_ne_bot_of_inner hp hc hin)
  have hmap := Subgroup.map_comap_eq_self hin
  have hE₀ := isElemAbelian_comap_conj hinj hE
  have hcard₀ : Nat.card (E.comap (MulAut.conj : Cat ⟨.suzuki m, hv⟩ →* _)) = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap, hc]
  have hodd : Odd (Nat.card (E.comap (MulAut.conj : Cat ⟨.suzuki m, hv⟩ →* _))) := by
    rw [hcard₀]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hcyc := CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.odd_commutative_subgroup_cyclic
    _ hodd hE₀.1 hsyl
  have := isElementaryAbelian_of_isElemAbelian hE₀
  exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hcard₀ hcyc

end CFSG.LieType.SeitzGeneration
