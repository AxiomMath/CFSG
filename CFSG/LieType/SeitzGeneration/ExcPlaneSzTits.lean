module

public import CFSG.LieType.SeitzGeneration.ExcPlaneBridge
public import CFSG.LieType.SeitzGeneration.ExcPlaneFamilies
public import CFSG.LieType.SeitzGeneration.ExcParabolicTits
public import CFSG.RankThree.PartTwo.Sec4.Census.BridgeSuzuki
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCyclic
public import CFSG.LieType.BorelTits.Suzuki

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint CFSG.Open CFSG.AGLEmbeddingD2

theorem rankLE2_of_oddSylow_cyclic {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2)
    (hSylow : ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → ∀ P : Sylow q G, IsCyclic P) : RankLE2 p G :=
  rankLE2_of_elemAbelian_cyclic hp fun F hF =>
    CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.odd_commutative_subgroup_cyclic F
      (odd_card_of_isElemAbelian hp hp2 hF) hF.1 hSylow

theorem excPlaneSuzuki : ExcPlaneSuzuki := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex ⟨m, rfl⟩ hr
  exfalso
  apply hr
  have hmodel : SuzukiModel (Cat ⟨.suzuki m, hv⟩) 2 (2 * m + 1) :=
    CFSG.SectionRank.suzukiModel_of_mulEquiv (MulEquiv.refl _)
      (CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv)
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨e⟩⟩ := hmodel
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [hF, hfa]
  have e' : Cat ⟨.suzuki m, hv⟩ ≃* CFSG.Open.GLASzGroup a F :=
    e.trans (MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a F))
  have : Finite (Cat ⟨.suzuki m, hv⟩) := Finite.of_equiv _ e.symm.toEquiv
  exact rankLE2_of_oddSylow_cyclic hp hp2
    (CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.suzuki_model_oddSylow_cyclic a ha
      hF' e')

section Tits


theorem excPlaneTits : ExcPlaneTits := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex hd hr
  subst hd
  exfalso
  have hT := card_cat_tits hv
  obtain ⟨⟨E, -, hE⟩, -⟩ := exists_isElemAbelian_card_of_not_rankLE2 hp hr
  have : Finite (Cat ⟨.tits, hv⟩) := Nat.finite_of_card_ne_zero (by rw [hT]; norm_num)
  have h3 : p ≠ 3 := fun h => hex (Or.inl ⟨h, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩)
  have h5 : p ≠ 5 := fun h => hex (Or.inr ⟨h, Or.inl rfl⟩)
  refine not_sq_dvd_card_tits hp hp2 h3 h5 ?_
  rw [← hT, ← hE]
  exact Subgroup.card_subgroup_dvd_card E

end Tits

end CFSG.LieType.SeitzGeneration
