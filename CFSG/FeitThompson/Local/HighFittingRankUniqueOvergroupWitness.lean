module

public import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
public import CFSG.FeitThompson.Definitions.UniqueMaximalOvergroup
import CFSG.FeitThompson.Local.MixedFittingLargeAbelianUniqueness
import CFSG.FeitThompson.Local.HighRankFittingControlsSylow
import CFSG.FeitThompson.Local.PrimeFittingNormalSelfCentralizingAbelian
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing
import CFSG.FeitThompson.Local.PrimeFixedMinimalQuotient
import CFSG.FeitThompson.Definitions.AlphaPrimesOfAFiniteGroup
import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {M : Subgroup G}

theorem exists_isElementaryAbelian_natCard_eq_le_mixedFitting (hp : p.Prime)
    (hrank : 3 ≤ elementaryAbelianPRank p ↥(mixedFitting M)) :
    ∃ A : Subgroup G, A ≤ mixedFitting M ∧ IsElementaryAbelian p A ∧ Nat.card ↥A = p ^ 3 := by
  obtain ⟨H, hH⟩ := mem_elementaryAbelianRanks.1 ((le_elementaryAbelianPRank_iff hp.one_lt).1 hrank)
  refine ⟨H.map (mixedFitting M).subtype, Subgroup.map_subtype_le _,
    (isElementaryAbelian_of_nonempty_mulEquiv_pi hH).map _, ?_⟩
  rw [← Nat.card_congr
    (Subgroup.equivMapOfInjective H _ (mixedFitting M).subtype_injective).toEquiv]
  exact natCard_eq_pow_of_nonempty_mulEquiv_pi hH

theorem odd_of_three_le_elementaryAbelianPRank_mixedFitting (hp : p.Prime)
    (hodd : Odd (Nat.card G)) (hrank : 3 ≤ elementaryAbelianPRank p ↥(mixedFitting M)) :
    Odd p := by
  obtain ⟨A, -, -, hAcard⟩ :=
    exists_isElementaryAbelian_natCard_eq_le_mixedFitting (M := M) hp hrank
  have hdvd : p ∣ Nat.card G :=
    (hAcard ▸ dvd_pow_self p three_ne_zero).trans A.card_subgroup_dvd_card
  refine hp.odd_of_ne_two ?_
  rintro rfl
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)

theorem mixedFitting_le_map_sylow [Group.IsSolvable ↥M] (hp : p.Prime)
    (hFp : IsPGroup p ↥(mixedFitting M)) (S : Sylow p ↥M) :
    mixedFitting M ≤ (S : Subgroup ↥M).map M.subtype := by
  rw [mixedFitting_eq]
  exact Subgroup.map_mono ((le_pCore hp (fittingRaw_normal ↥M)
    (isPGroup_fittingRaw_of_isPGroup_mixedFitting hFp)).trans (pCore_le_sylow hp S))

theorem exists_bot_lt_isUniqueMaximalOvergroup_of_not_isPGroup [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hM : IsCoatom M) (hp : p.Prime)
    (hrank : 3 ≤ elementaryAbelianPRank p ↥(mixedFitting M))
    (hnp : ¬ IsPGroup p ↥(mixedFitting M)) :
    ∃ X : Subgroup G, ⊥ < X ∧ X ≤ mixedFitting M ∧ IsUniqueMaximalOvergroup X M := by
  obtain ⟨A, hAF, hAea, hAcard⟩ :=
    exists_isElementaryAbelian_natCard_eq_le_mixedFitting (M := M) hp hrank
  have hArank : 3 ≤ elementaryAbelianPRank p ↥A := hAea.le_elementaryAbelianPRank hp hAcard le_rfl
  have hAne : A ≠ ⊥ := ne_bot_of_le_elementaryAbelianPRank hp.one_lt three_ne_zero hArank
  have hAle : A ≤ mixedFittingCentralizer M A := by
    rw [mixedFittingCentralizer_eq]
    exact le_inf hAF (hAea.le_centralizer le_rfl)
  exact ⟨mixedFittingCentralizer M A, bot_lt_iff_ne_bot.2 fun hbot =>
      hAne (le_bot_iff.1 (hbot ▸ hAle)), mixedFittingCentralizer_le M A,
    isUniqueMaximalOvergroup_mixedFittingCentralizer hna hodd hsolv hM hp hAea hAF hArank hnp⟩

theorem exists_bot_lt_isUniqueMaximalOvergroup_of_isPGroup [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hM : IsCoatom M) (hp : p.Prime)
    (hrank : 3 ≤ elementaryAbelianPRank p ↥(mixedFitting M))
    (hFp : IsPGroup p ↥(mixedFitting M)) :
    ∃ X : Subgroup G, ⊥ < X ∧ X ≤ mixedFitting M ∧ IsUniqueMaximalOvergroup X M := by
  have hfp := Fact.mk hp
  have hMsolv := hsolv M hM.1
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p ↥M))
  set P : Subgroup G := (S : Subgroup ↥M).map M.subtype with hPdef
  have hPM : P ≤ M := Subgroup.map_subtype_le _
  have hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p := by
    rw [hPdef, ← Nat.card_congr
      (Subgroup.equivMapOfInjective _ _ M.subtype_injective).toEquiv, S.card_eq_multiplicity]
  have hPp : IsPGroup p ↥P := IsPGroup.of_card hPcard
  have hPrank : 3 ≤ elementaryAbelianPRank p ↥P :=
    hrank.trans (elementaryAbelianPRank_le_of_le hp.one_lt (mixedFitting_le_map_sylow hp hFp S))
  obtain ⟨A, hAn, hAcomm, hArank, hAcent⟩ :=
    exists_abelian_normal_centralizer_eq_of_three_le_elementaryAbelianPRank_of_isPGroup hp
      (odd_of_three_le_elementaryAbelianPRank_mixedFitting (M := M) hp hodd hrank) hPp hPrank
  set B : Subgroup G := A.map P.subtype with hBdef
  have hBP : B ≤ P := Subgroup.map_subtype_le _
  have hBA : B.subgroupOf P = A := by
    rw [hBdef, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
  have hBnormal : (B.subgroupOf P).Normal := hBA ▸ hAn
  have hBcomm : IsMulCommutative ↥B := by rw [hBdef]; infer_instance
  have hBcent : P ⊓ centralizer (B : Set G) = B :=
    (centralizer_subgroupOf_eq_iff hBP).1 (by rw [hBA]; exact hAcent)
  have hBrank : 3 ≤ elementaryAbelianPRank p ↥B :=
    hArank.trans_eq (elementaryAbelianPRank_eq_of_mulEquiv hp.one_lt
      (Subgroup.equivMapOfInjective A _ P.subtype_injective))
  refine ⟨B, bot_lt_iff_ne_bot.2
      (ne_bot_of_le_elementaryAbelianPRank hp.one_lt three_ne_zero hBrank), ?_, ?_⟩
  · exact le_mixedFitting_of_isPGroup_mixedFitting_of_rank_three hodd hsolv hM hp hFp hrank hPM
      hPcard hBP hBnormal hBcomm hBcent hBrank
  · exact isUniqueMaximalOvergroup_of_isPGroup_mixedFitting_of_rank_three hna hodd hsolv hM hp hFp
      hrank hPM hPcard hBP hBnormal hBcomm hBcent hBrank

theorem exists_bot_lt_isUniqueMaximalOvergroup_le_mixedFitting [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hM : IsCoatom M) (hp : p.Prime)
    (hrank : 3 ≤ elementaryAbelianPRank p ↥(mixedFitting M)) :
    ∃ X : Subgroup G, ⊥ < X ∧ X ≤ mixedFitting M ∧ IsUniqueMaximalOvergroup X M := by
  by_cases hFp : IsPGroup p ↥(mixedFitting M)
  · exact exists_bot_lt_isUniqueMaximalOvergroup_of_isPGroup hna hodd hsolv hM hp hrank hFp
  · exact exists_bot_lt_isUniqueMaximalOvergroup_of_not_isPGroup hna hodd hsolv hM hp hrank hFp

theorem exists_bot_lt_isUniqueMaximalOvergroup_le_mixedFitting_of_exists_prime [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K) (hM : IsCoatom M)
    (hrank : ∃ q : ℕ, q.Prime ∧ 3 ≤ elementaryAbelianPRank q ↥(mixedFitting M)) :
    ∃ X : Subgroup G, ⊥ < X ∧ X ≤ mixedFitting M ∧ IsUniqueMaximalOvergroup X M := by
  obtain ⟨q, hq, hqrank⟩ := hrank
  exact exists_bot_lt_isUniqueMaximalOvergroup_le_mixedFitting hna hodd hsolv hM hq hqrank

end

end CFSG.FeitThompson
