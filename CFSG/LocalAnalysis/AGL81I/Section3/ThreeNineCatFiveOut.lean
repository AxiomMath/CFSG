module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatalogue
public import CFSG.Sporadic.Schreier.TitsOuter
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineFiveFamilies
import CFSG.Adapters.LieModelSimple
import CFSG.LieType.Simplicity.Basic
import CFSG.RankThree.ThinCatalog.OuterThreeFree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinThreeOut
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma55

public section
namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueSchreierAlternating
  (outer_card_dvd_two_of_equiv_outside_six)

theorem isoLie_suzuki_two_of_suzukiModel {K : Type} [Group K] (h : SuzukiModel K 2 5) :
    CFSG.RankThree.PartOne.Census3.IsoLie K (.suzuki 2) := by
  obtain ⟨-, a, ha, F, _, _, hf, hF, ⟨e⟩⟩ := h
  obtain rfl : a = 2 := by omega
  exact CFSG.RankThree.PartOne.SEITZ7.isoLie_suzuki_of_blueprint ha (by rw [hF]) e

private theorem not_dvd_of_dvd_two {p n : ℕ} (hp5 : 5 ≤ p) (h : n ∣ 2) : ¬ p ∣ n := by
  intro hpn
  have := Nat.le_of_dvd (by norm_num : 0 < 2) (hpn.trans h)
  omega

private theorem not_dvd_of_dvd_four {p n : ℕ} (hp5 : 5 ≤ p) (h : n ∣ 4) : ¬ p ∣ n := by
  intro hpn
  have := Nat.le_of_dvd (by norm_num : 0 < 4) (hpn.trans h)
  omega

private theorem sporadic_facts {K : Type} [Group K] {p : ℕ}
    (hSporOut : ∀ s : TauCeti.SporadicName, Nat.card (Outer (Carrier s)) ∣ 2)
    (hSporSimple : ∀ s : TauCeti.SporadicName, IsSimpleGroup (Carrier s))
    (hp : p.Prime) (hp2 : p ≠ 2) {s : TauCeti.SporadicName} (hK : IsSporadic K s) :
    IsSimpleGroup K ∧ ¬ p ∣ Nat.card (Outer K) := by
  obtain ⟨e⟩ := hK
  haveI := hSporSimple s
  exact ⟨MulEquiv.isSimpleGroup e,
    CFSG.AGLEmbedding.not_dvd_card_outer_of_mulEquiv e.symm (hSporOut s) hp hp2⟩

theorem pairFive_member_facts
    (hSporOut : ∀ s : TauCeti.SporadicName, Nat.card (Outer (Carrier s)) ∣ 2)
    (hSporSimple : ∀ s : TauCeti.SporadicName, IsSimpleGroup (Carrier s))
    {K : Type} [Group K] [Finite K] {p : ℕ} (hp5 : 5 ≤ p) (hK : KGroupLowRank24_12 p K)
    (hrk : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 2) :
    IsSimpleGroup K ∧ ((p = 5 ∧ SuzukiModel K 2 5) ∨ ¬ p ∣ Nat.card (Outer K)) := by
  obtain ⟨hp, hp2, -, -, hc⟩ := hK
  rcases hc with (hA | hA | hA | hA | hA | hA | hA | hA | hA) | ⟨-, hG2⟩ | ⟨hp3, -⟩ |
    ⟨rfl, hSz | hT | hS | hS | hS | hS | hS | hS | hS | hS | hS | hS⟩ |
    ⟨rfl, hS | hS | hS | hS⟩ | ⟨rfl, hS⟩
  · obtain ⟨e⟩ := hA
    exact ⟨(CFSG.LieType.Simplicity.fam_alternating_converse K ⟨2 * p, by omega, ⟨e⟩⟩).2.2,
      Or.inr (not_dvd_of_dvd_two hp5
        (outer_card_dvd_two_of_equiv_outside_six (Or.inr (by omega)) e))⟩
  · obtain ⟨e⟩ := hA
    exact ⟨(CFSG.LieType.Simplicity.fam_alternating_converse K ⟨3 * p, by omega, ⟨e⟩⟩).2.2,
      Or.inr (not_dvd_of_dvd_two hp5
        (outer_card_dvd_two_of_equiv_outside_six (Or.inr (by omega)) e))⟩
  · refine ⟨CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hA, Or.inr ?_⟩
    exact not_dvd_of_dvd_four hp5
      ((CFSG.RankThree.ThinCatalog.outer_card_dvd_of_psl_two hA).trans
        (Nat.mul_dvd_mul_left 2 (Nat.gcd_dvd_left 2 _)))
  · exfalso
    obtain ⟨-, -, hcases⟩ := CFSG.SectionRank.classical_model_rank hp2 hA
    rcases hcases with ⟨-, ⟨-, hle⟩ | ⟨h, -⟩ | h4⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h4
    all_goals first | omega | cases h
  · obtain ⟨e⟩ := hA
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have hm : StatedClassicalModel K .PSL 3 p 1 :=
      ⟨⟨hp, le_rfl, by norm_num, by simp, by simp⟩, ZMod p, inferInstance, inferInstance,
        by rw [Nat.card_zmod, pow_one],
        ⟨e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3
          (ZMod p))⟩⟩
    refine ⟨CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hm, Or.inr ?_⟩
    have hbound := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
      (Or.inl rfl) (le_refl 3) hp (by norm_num) hm).1
    simp only [CFSG.RankThree.OuterOrder.determinantParameter, mul_one, pow_one] at hbound
    intro hdvd
    exact CFSG.AGLEmbeddingD2.not_dvd_two_mul_gcd_pred hp hp2 (hdvd.trans hbound)
  · refine ⟨CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hA, Or.inr ?_⟩
    have hbound := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
      (Or.inr rfl) (le_refl 3) hp (by norm_num) hA).1
    simp only [CFSG.RankThree.OuterOrder.determinantParameter, mul_one, pow_one] at hbound
    intro hdvd
    exact CFSG.AGLEmbeddingD2.not_dvd_two_mul_gcd_succ hp hp2 (hdvd.trans hbound)
  · exfalso
    have := four_le_pRank_of_isPSLType_four hp hp2 hA
    omega
  · exfalso
    have := four_le_pRank_of_psu_four hp2 hA
    omega
  · exfalso
    obtain ⟨-, -, hcases⟩ := CFSG.SectionRank.classical_model_rank hp2 hA
    rcases hcases with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, ⟨-, hle⟩ | h4⟩ | h4
    all_goals first | omega | cases h
  · exfalso
    haveI : Fact p.Prime := ⟨hp⟩
    have := CFSG.SectionRank.three_mul_le_pRank_of_G2Model (p := p) (f := 1) hG2.2
    omega
  · exfalso
    omega
  · exact ⟨(CFSG.LieType.Simplicity.fam_2b2_simplicity K 2 5 hSz).2, Or.inl ⟨rfl, hSz⟩⟩
  · refine ⟨(CFSG.LieType.Simplicity.fam_tits_simplicity K 2 1 hT).2, Or.inr ?_⟩
    intro h5
    obtain ⟨n, hn⟩ := (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier K 2 1 hT).1.exists_card_eq
    have h52 : 5 ∣ 2 ^ n := by rwa [hn] at h5
    have : 5 ∣ 2 := Nat.prime_five.dvd_of_dvd_pow h52
    norm_num at this
  all_goals
    exact ⟨(sporadic_facts hSporOut hSporSimple hp hp2 hS).1,
      Or.inr (sporadic_facts hSporOut hSporSimple hp hp2 hS).2⟩

theorem pairFive_member_facts_of_mulEquiv {K₁ K₂ : Type} [Group K₁] [Group K₂] (e : K₁ ≃* K₂)
    (hq : CFSG.IsQuasisimple K₂) {p : ℕ}
    (h : IsSimpleGroup K₁ ∧ ((p = 5 ∧ SuzukiModel K₁ 2 5) ∨ ¬ p ∣ Nat.card (Outer K₁))) :
    Subgroup.center K₂ = ⊥ ∧ ((p = 5 ∧ SuzukiModel K₂ 2 5) ∨ ¬ p ∣ Nat.card (Outer K₂)) := by
  haveI : IsSimpleGroup K₁ := h.1
  haveI : IsSimpleGroup K₂ := e.symm.isSimpleGroup
  refine ⟨CFSG.ComponentClassification.GSThmB.center_eq_bot_of_isSimpleGroup_of_isQuasisimple hq,
    ?_⟩
  rcases h.2 with ⟨rfl, hSz⟩ | hout
  · exact Or.inl ⟨rfl, CFSG.SectionRank.suzukiModel_of_mulEquiv e.symm hSz⟩
  · refine Or.inr fun hd => hout ?_
    have hcard : Nat.card (Outer K₁) = Nat.card (Outer K₂) :=
      Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv
    rwa [← hcard] at hd

end CFSG.LocalAnalysis.AGL81I.Section3
