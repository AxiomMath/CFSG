module

public import CFSG.LieType.SeitzGeneration.ExcPrimeSplit
public import CFSG.LieType.SeitzGeneration.OuterQuotient
public import CFSG.LieType.SeitzGeneration.Inner
public import CFSG.LieType.SeitzGeneration.ExcParabolicModel
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.RankThree.PartTwo.Sec4.Census.BridgeSuzuki
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCyclic
public import CFSG.LieType.Simplicity.Suzuki
public import CFSG.LieType.Suzuki.SuzukiOuterCyclic

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms

theorem suzukiModel_cat {m : ℕ} (hv : (TauCeti.LieTypeIndex.suzuki m).Valid) :
    SuzukiModel (Cat ⟨.suzuki m, hv⟩) 2 (2 * m + 1) :=
  CFSG.SectionRank.suzukiModel_of_mulEquiv (MulEquiv.refl _)
    (CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv)

theorem not_innerPlane_suzuki {m : ℕ}
    (hv : (TauCeti.LieTypeIndex.suzuki m).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (MulAut (Cat ⟨.suzuki m, hv⟩))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2) : ¬ InnerPlane ⟨.suzuki m, hv⟩ p E := by
  intro hin
  have : Fact p.Prime := ⟨hp⟩
  have hmodel := suzukiModel_cat hv
  have hsimple := (CFSG.LieType.Simplicity.fam_2b2_simplicity _ 2 (2 * m + 1) hmodel).2
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨e⟩⟩ := hmodel
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [hF, hfa]
  have e' : Cat ⟨.suzuki m, hv⟩ ≃* CFSG.Open.GLASzGroup a F :=
    e.trans (MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a F))
  have : Finite (Cat ⟨.suzuki m, hv⟩) := Finite.of_equiv _ e.symm.toEquiv
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

theorem seitzExcAnisotropicFor_suzuki :
    SeitzExcAnisotropicFor IsSuzukiIndex := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, ⟨m, rfl⟩, -⟩
  exact (not_innerPlane_suzuki hv hp hp2 hE hc hin).elim

theorem card_cat_suzuki_coprime_three {m : ℕ}
    (hv : (TauCeti.LieTypeIndex.suzuki m).Valid) :
    Nat.Coprime 3 (Nat.card (Cat ⟨.suzuki m, hv⟩)) := by
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨e⟩⟩ := suzukiModel_cat hv
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [hF, hfa]
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hF']
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * a + 1) = q at hq ⊢
  have hq1 : 1 ≤ q := by omega
  refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h => ?_
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
    · omega
  · have h' : (q ^ 2 + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
    have : q ^ 2 % 3 = 1 := by
      rw [Nat.pow_mod, hq]
    omega

theorem no_plane_suzuki_three {m : ℕ}
    (hv : (TauCeti.LieTypeIndex.suzuki m).Valid)
    {E : Subgroup (MulAut (Cat ⟨.suzuki m, hv⟩))} (hE : IsElemAbelian 3 E)
    (hc : Nat.card E = 3 ^ 2) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime (Nat.card E) (Nat.card (Cat ⟨.suzuki m, hv⟩)) := by
    rw [hc]
    exact (card_cat_suzuki_coprime_three hv).pow_left 2
  obtain ⟨f, hf⟩ := injective_outer_of_coprime_card hcop
  have hcyc : IsCyclic (Outer (Cat ⟨.suzuki m, hv⟩)) :=
    (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} _ 2 (2 * m + 1)
      (suzukiModel_cat hv)).1.1
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have := isElementaryAbelian_of_isElemAbelian hE
  exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hc (isCyclic_of_injective f hf)

theorem seitzExcOuterNarrowForAt_suzuki_three :
    SeitzExcOuterNarrowForAt IsSuzukiIndex PrimeRange.three := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨-, -, ⟨m, rfl⟩, hp3⟩
  obtain rfl : p = 3 := hp3
  exact (no_plane_suzuki_three hv hE hc).elim

end CFSG.LieType.SeitzGeneration
