module

public import CFSG.LocalAnalysis.AGLEmbedding.GenericTargetFacts
public import CFSG.Timmesfeld.RankOne.SL2
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCyclic
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels
import CFSG.LieType.BorelTits.Suzuki

public section

namespace CFSG.AGLEmbedding

theorem isCyclic_sylow_of_mulEquiv {K L : Type*} [Group K] [Finite K] [Group L] {p : ℕ}
    [Fact p.Prime] (e : K ≃* L) (h : ∀ S : Sylow p L, IsCyclic (S : Subgroup L)) (T : Sylow p K) :
    IsCyclic (T : Subgroup K) := by
  have hc : IsCyclic ↥((T : Subgroup K).map e.toMonoidHom) :=
    h (T.mapSurjective (f := e.toMonoidHom) e.surjective)
  exact isCyclic_of_surjective
    (Subgroup.equivMapOfInjective (T : Subgroup K) e.toMonoidHom e.injective).symm.toMonoidHom
    (Subgroup.equivMapOfInjective (T : Subgroup K) e.toMonoidHom e.injective).symm.surjective

theorem isCyclic_sylow_three_linTwoEight {K : Type} [Group K] [Finite K] (q : TauCeti.PrimePower)
    (hq2 : q.p = 2) (hqe : q.exponent = 3) (hv : (TauCeti.LieTypeIndex.A 1 q).Valid)
    (e : K ≃* CatGroup ⟨.A 1 q, hv⟩) (T : Sylow 3 K) : IsCyclic (T : Subgroup K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨p, ex, hp, hex⟩ := q
  simp only at hq2 hqe
  subst hq2
  subst hqe
  have : Fact (Nat.Prime 2) := ⟨hp⟩
  exact isCyclic_sylow_of_mulEquiv
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 ⟨2, 3, hp, hex⟩ hv))
    (fun S => CFSG.Timmesfeld.RankOne.isCyclic_sylow_psl2 (n := 3) (by norm_num) 3
      (by norm_num) S) T

theorem isCyclic_sylow_five_suzuki {K : Type} [Group K] [Finite K]
    (m : ℕ) (hv : (TauCeti.LieTypeIndex.suzuki m).Valid) (e : K ≃* CatGroup ⟨.suzuki m, hv⟩)
    (T : Sylow 5 K) : IsCyclic (T : Subgroup K) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hmodel := CFSG.RankThree.PartOne.CTP.suzukiModel_of_isoLie m ⟨hv, ⟨e⟩⟩
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨e₀⟩⟩ := hmodel
  have e' : K ≃* CFSG.Open.GLASzGroup a F :=
    e₀.trans (MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a F))
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [hF, hfa]
  exact CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.suzuki_model_oddSylow_cyclic
    a ha hF' e' 5 (by norm_num) T

end CFSG.AGLEmbedding
