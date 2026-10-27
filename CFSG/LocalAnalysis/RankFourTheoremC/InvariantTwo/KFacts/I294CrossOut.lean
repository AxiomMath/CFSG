module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossOutBase
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212Inputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicLift
public import CFSG.RankThree.PartOne.AUTSL.OddOutGaps
public import CFSG.RankThree.PartOne.KA.AlternatingPlaneInner
public import CFSG.RankThree.PartOne.S11d.OddExcAll
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutEsix
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.SporadicOut
public import CFSG.RankThree.PartOne.SPOR.OuterSimple
public import CFSG.RankThree.PartOne.TCB.Final
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Blueprint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.OutStructure
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.RankThreeTheoremC
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)
open Subgroup

theorem not_dvd_gcd_psl_of_not_isLinearOrUnitaryAt {K : Type} [Group K] {p n r f : ℕ}
    (hl : ¬ IsLinearOrUnitaryAt p K) (h : StatedClassicalModel K .PSL n r f) :
    ¬ p ∣ Nat.gcd n (r ^ f - 1) := by
  intro hd
  obtain ⟨-, F, i1, i2, hF, ⟨e⟩⟩ := h
  exact hl (Or.inl ⟨n, F, i1, i2, hd.trans (Nat.gcd_dvd_left _ _),
    by rw [hF]; exact hd.trans (Nat.gcd_dvd_right _ _), ⟨e⟩⟩)

theorem not_dvd_gcd_psu_of_not_isLinearOrUnitaryAt {K : Type} [Group K] {p n r f : ℕ}
    (hl : ¬ IsLinearOrUnitaryAt p K) (h : StatedClassicalModel K .PSU n r f) :
    ¬ p ∣ Nat.gcd n (r ^ f + 1) := by
  intro hd
  obtain ⟨-, F, i1, i2, hF, ⟨e⟩⟩ := h
  exact hl (Or.inr ⟨n, r ^ f, F, i1, i2, hF, hd.trans (Nat.gcd_dvd_left _ _),
    hd.trans (Nat.gcd_dvd_right _ _), ⟨e⟩⟩)

section Even


theorem outPChain_or_not_dvd_of_even' {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {t : StatedLieTag} {n f : ℕ} (hmodel : LieModel K t n 2 f)
    (hndL : ∀ {n m : ℕ}, StatedClassicalModel K .PSL n 2 m → ¬ p ∣ Nat.gcd n (2 ^ m - 1))
    (hndU : ∀ {n m : ℕ}, StatedClassicalModel K .PSU n 2 m → ¬ p ∣ Nat.gcd n (2 ^ m + 1)) :
    OutPChain p K ∨ ¬ p ∣ Nat.card (Outer K) := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  rcases hmodel with ⟨ht, hcl⟩ | ⟨hn0, ht, hch⟩ | ⟨hn0, ht, hree⟩ | ⟨hn0, ht, hsz⟩
  · simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · by_cases hn : n = 2
      · subst hn
        exact Or.inl (outPNice_PSL_two hp hcl).toChain
      · obtain ⟨⟨-, -, hn2, -⟩, -⟩ := id hcl
        exact Or.inl (outPNice_PSL_ge_three hp hp2 (by omega) hcl (hndL hcl)).toChain
    · exact Or.inl (outPNice_PSU hp hcl (hndU hcl)).toChain
    · by_cases hn : n = 2
      · subst hn
        exact Or.inl (outPNice_PSp_two hp hcl).toChain
      · obtain ⟨⟨-, -, hn2, -⟩, -⟩ := id hcl
        exact Or.inl (outPNice_PSp_ge_three hp (by omega) hcl).toChain
    · obtain ⟨⟨-, -, -, hp2'⟩, -⟩ := id hcl
      exact absurd rfl hp2'
    · obtain ⟨⟨-, -, hn4⟩, -⟩ := id hcl
      by_cases hn : n = 4
      · subst hn
        exact Or.inl (outPChain_POmegaPlus_four hp (by omega) hcl)
      · exact Or.inl (outPNice_POmegaPlus_ge_five hp hp2 (by omega) hcl).toChain
    · obtain ⟨⟨-, -, hn4⟩, -⟩ := id hcl
      exact Or.inl (outPNice_POmegaMinus hp hp2 hn4 hcl).toChain
  · simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (outPNice_G2 hp hch).toChain
    · exact Or.inl (outPNice_F4 hp hch).toChain
    · exact Or.inl (outPNice_E6 hp hp3 hp2 hch).toChain
    · exact Or.inl (outPNice_E7 hp hch).toChain
    · exact Or.inl (outPNice_E8 hp hch).toChain
    · exact Or.inl (outPNice_twistedE6 hp hp3 hch).toChain
    · exact Or.inl (outPNice_trialityD4 hp hch).toChain
  · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · obtain ⟨⟨-, -, -, h23, -⟩, -⟩ := id hree
      omega
    · exact Or.inl (outPNice_twistedF4 hp hree).toChain
    · refine Or.inr fun hdvd => ?_
      obtain ⟨k, hk⟩ := (Sporadic.Schreier.Tits.AT_Tits_model_Schreier K 2 f hree).1.exists_card_eq
      rw [hk] at hdvd
      have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow hdvd)
      omega
  · subst ht
    exact Or.inl (outPNice_Suzuki hp hsz).toChain

end Even

section Odd


theorem outPChain_of_odd' {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {t : StatedLieTag} {n ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hmodel : LieModel K t n ℓ f)
    (hndL : ∀ {n f : ℕ}, StatedClassicalModel K .PSL n ℓ f → ¬ p ∣ Nat.gcd n (ℓ ^ f - 1))
    (hndU : ∀ {n f : ℕ}, StatedClassicalModel K .PSU n ℓ f → ¬ p ∣ Nat.gcd n (ℓ ^ f + 1)) :
    OutPChain p K := by
  have hp3 : 3 < p := by omega
  have hp2 : p ≠ 2 := by omega
  rcases hmodel with ⟨ht, hcl⟩ | ⟨hn0, ht, hch⟩ | ⟨hn0, ht, hree⟩ | ⟨hn0, ht, hsz⟩
  · cases t
    · by_cases hn2 : n = 2
      · subst hn2
        exact (outPNice_PSL_two_odd hp hp3 hℓ2 hcl).toChain
      · have hn3 : 3 ≤ n := by
          have := hcl.1.2.2.1
          omega
        exact (outPNice_PSL_ge_three_odd hp hp2 hn3 hcl (hndL hcl)).toChain
    · exact (outPNice_PSU_odd hp hcl (hndU hcl)).toChain
    · by_cases hn2 : n = 2
      · subst hn2
        exact AUTSL.oddOutGaps.1 p K ℓ f hp hp5 hℓ2 hcl
      · have hn3 : 3 ≤ n := by
          have := hcl.1.2.2.1
          omega
        exact (outPNice_PSp_ge_three_odd hp hp2 hn3 hcl).toChain
    · exact (outPNice_POmegaOdd_gen hp hp5 hcl).toChain
    · by_cases hn4 : n = 4
      · subst hn4
        exact outPChain_POmegaPlus_four_gen hp hp5 hcl
      · have hn5 : 5 ≤ n := by
          have := hcl.1.2.2
          omega
        exact (outPNice_POmegaPlus_gen_ge_five hp hp5 hn5 hcl).toChain
    · exact (outPNice_POmegaMinus_gen hp hp5 hcl).toChain
    all_goals exact hcl.2.elim
  · exact (oddExceptionalOut_holds p K t ℓ f hp hp5 hℓ hℓ2 ht hch).toChain
  · cases t
    case twistedG2 =>
      have h3 : ℓ = 3 := hree.1.2.2.2.1
      subst h3
      exact AUTSL.oddOutGaps.2 p K f hp hp5 hree
    case twistedF4 => exact absurd hree.1.2.2.2.1 hℓ2
    case Tits => exact absurd hree.1.2.2.2.1 hℓ2
    all_goals
      obtain ⟨-, a, -, hm⟩ := hree
      exact hm.elim
  · exact absurd hsz.1 hℓ2

end Odd

section Final


theorem pRank_outer_le_one_of_catalog {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) (hcat : CFSG.Open.IsCatalogGroup K) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hl : ¬ IsLinearOrUnitaryAt p K) :
    CFSG.Open.pRank p (⊤ : Subgroup (Outer K)) ≤ 1 := by
  have : IsSimpleGroup K := hs
  have : Fact p.Prime := ⟨hp⟩
  rcases PlaneCases.catalog_cases (TCB.tauCetiCatalogBridge K hnab hcat) with
    ⟨q, hq, ⟨e⟩⟩ | ⟨n, hn5, ⟨e⟩⟩ | ⟨t, n, ℓ, f, hadm, hmodel⟩ | ⟨s, ⟨e⟩⟩
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · have hout : Nat.card (Outer K) ≤ 4 :=
      (Nat.card_congr (equivalence e).toEquiv).trans_le (card_outer_alternating_le_four hn5)
    exact pRank_outer_le_one_of_outer_small hp (Or.inl (by nlinarith))
  · have hndL : ∀ {n' f' : ℕ}, StatedClassicalModel K .PSL n' ℓ f' →
        ¬ p ∣ Nat.gcd n' (ℓ ^ f' - 1) := fun h => not_dvd_gcd_psl_of_not_isLinearOrUnitaryAt hl h
    have hndU : ∀ {n' f' : ℕ}, StatedClassicalModel K .PSU n' ℓ f' →
        ¬ p ∣ Nat.gcd n' (ℓ ^ f' + 1) := fun h => not_dvd_gcd_psu_of_not_isLinearOrUnitaryAt hl h
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      rcases outPChain_or_not_dvd_of_even' hp hp5 hmodel hndL hndU with h | h
      · exact pRank_outer_le_one_of_outPChain hp h
      · exact pRank_outer_le_one_of_outer_small hp (Or.inr h)
    · exact pRank_outer_le_one_of_outPChain hp
        (outPChain_of_odd' hp hp5 hadm.1 hℓ2 hmodel hndL hndU)
  · rcases sporadicOutSmall_of_simple SPOR.sporadicOuterOrderLeTwoSimple_holds s K hnab ⟨e⟩ with
      hlt | hno
    · exact pRank_outer_le_one_of_outer_small hp (Or.inl (by nlinarith))
    · exact pRank_outer_le_one_of_outer_small hp (Or.inr (hno p hp hp5))

theorem pRank_quotient_le_one_of_catalog {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (L : Subgroup X) [L.Normal] (hs : IsSimpleGroup L)
    (hnab : ∃ a b : L, a * b ≠ b * a) (hcat : CFSG.Open.IsCatalogGroup L)
    (hl : ¬ IsLinearOrUnitaryAt p L) (hcen : centralizer (L : Set X) = ⊥) :
    CFSG.Open.pRank p (⊤ : Subgroup (X ⧸ L)) ≤ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact (pRank_quotient_le_pRank_outer L hcen).trans
    (pRank_outer_le_one_of_catalog hs hnab hcat hp hp5 hl)

end Final

end CFSG.LocalAnalysis.RankFourTheoremC
