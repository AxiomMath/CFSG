module

public import CFSG.FeitThompson.Local.SylowNormalizerCommutatorsCentralizeFitting
public import CFSG.FeitThompson.Definitions.UniqueMaximalOvergroup
import CFSG.FeitThompson.Local.NonuniqueScnControlsNormalizers
import CFSG.FeitThompson.Local.SylowNormalizerNotCentralizing
import CFSG.FeitThompson.Local.HighRankFittingUniqueOvergroup
import CFSG.FeitThompson.Local.NonuniqueScnAuxiliaryPrime
import CFSG.FeitThompson.Local.LowRankFittingDerivedNilpotent
import CFSG.FeitThompson.Local.NilpotentDerivedNormalizerFactorization
import CFSG.FeitThompson.Local.SelfCentralizingAbelianSylowConstraint
import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
import CFSG.FeitThompson.Local.InvariantControlUniqueMaximalOvergroup
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.OddOrder.RankTwoKernelSmallerComplementPrimes
import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup
import CFSG.FeitThompson.Foundations.NormalNilpotentInFitting
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup
import CFSG.FeitThompson.Definitions.AlphaPrimesOfAFiniteGroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {p : ℕ}

theorem isUniqueMaximalOvergroup_self {M : Subgroup G} (hM : IsCoatom M) :
    IsUniqueMaximalOvergroup M M :=
  ⟨hM, le_rfl, fun _ hN hMN => (hM.le_iff_eq hN.1).1 hMN⟩

theorem pCoreIn_sup_pComplCoreIn_mixedFitting [Finite G] (hp : p.Prime) (M : Subgroup G) :
    pCoreIn p (mixedFitting M) ⊔ pComplCoreIn p (mixedFitting M) = mixedFitting M := by
  have h := pCore_sup_pComplCore_eq_top hp ↥(mixedFitting M)
  have h2 := congrArg (fun S : Subgroup ↥(mixedFitting M) => S.map (mixedFitting M).subtype) h
  simp only [Subgroup.map_sup, ← pCoreIn_eq, ← pComplCoreIn_eq,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
  exact h2

theorem commutator_self_le_mixedFitting [Finite G]
    (hodd : Odd (Nat.card G)) (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X)
    {M : Subgroup G} (hM : IsCoatom M)
    (hall : ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥(mixedFitting M) ≤ 2) :
    ⁅M, M⁆ ≤ mixedFitting M := by
  have hMsolv : Group.IsSolvable ↥M := hsolv M hM.1
  have hoddM : Odd (Nat.card ↥M) := odd_natCard_subgroup hodd M
  have h := commutator_le_fittingRaw (G := ↥M) hoddM
    (fun q hq => by rw [elementaryAbelianPRank_fittingRaw_eq hq]; exact hall q hq)
  have h2 := Subgroup.map_mono (f := M.subtype) h
  rwa [Subgroup.map_subtype_commutator, ← mixedFitting_eq] at h2

theorem le_sup_pComplCoreIn_normalizer [Finite G]
    (hodd : Odd (Nat.card G)) (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X)
    (hp : p.Prime) (P : Sylow p G) {M : Subgroup G} (hM : IsCoatom M)
    (hPM : (P : Subgroup G) ≤ M)
    (hall : ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥(mixedFitting M) ≤ 2) :
    M ≤ pComplCoreIn p (mixedFitting M) ⊔ normalizer ((P : Subgroup G) : Set G) := by
  have := Fact.mk hp
  have hcomm := commutator_self_le_mixedFitting hodd hsolv hM hall
  have hOpP : pCoreIn p (mixedFitting M) ≤ (P : Subgroup G) := by
    have hnorm : (P : Subgroup G) ≤
        normalizer ((pCoreIn p (mixedFitting M) : Subgroup G) : Set G) :=
      le_normalizer_pCoreIn p (hPM.trans (le_normalizer_mixedFitting M))
    have hsup : IsPGroup p ↥(pCoreIn p (mixedFitting M) ⊔ (P : Subgroup G)) :=
      IsPGroup.to_sup_of_normal_left' (isPGroup_pCoreIn hp _) P.isPGroup' hnorm
    have h := P.is_maximal' (Q := pCoreIn p (mixedFitting M) ⊔ (P : Subgroup G)) hsup le_sup_right
    exact le_trans le_sup_left h.le
  have hFle : mixedFitting M ≤
      pComplCoreIn p (mixedFitting M) ⊔ normalizer ((P : Subgroup G) : Set G) :=
    (pCoreIn_sup_pComplCoreIn_mixedFitting hp M).ge.trans
      (sup_le (le_sup_of_le_right (hOpP.trans Subgroup.le_normalizer)) le_sup_left)
  have hKM : mixedFitting M ⊔ (P : Subgroup G) ≤ M := sup_le (mixedFitting_le M) hPM
  have hMK : M ≤ normalizer ((mixedFitting M ⊔ (P : Subgroup G) : Subgroup G) : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.2
      ((Subgroup.commutator_mono hKM le_rfl).trans (hcomm.trans le_sup_left))
  have hPcardM : Nat.card ↥(P : Subgroup G) = p ^ (Nat.card ↥M).factorization p :=
    natCard_eq_pow_factorization_of_le hp hPM P.card_eq_multiplicity
  have hfrat := le_sup_normalizer_of_le_normalizer hp hKM hMK le_sup_right hPcardM
  exact hfrat.trans
    (sup_le (sup_le hFle (le_sup_of_le_right Subgroup.le_normalizer)) le_sup_right)

theorem isUniqueMaximalOvergroup_normalizer_commutator_normalizer_of_scn [Finite G]
    [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X)
    (hp : p.Prime) (P : Sylow p G) {A M : Subgroup G}
    (hAnormal : (A.subgroupOf (P : Subgroup G)).Normal)
    (hAself : centralizer (A : Set G) ⊓ (P : Subgroup G) = A)
    (hArank : 3 ≤ elementaryAbelianPRank p ↥A)
    (hAtwo : ∃ M₁ M₂ : Subgroup G, IsCoatom M₁ ∧ IsCoatom M₂ ∧ A ≤ M₁ ∧ A ≤ M₂ ∧ M₁ ≠ M₂)
    (hM : IsCoatom M) (hCM : centralizer (A : Set G) ≤ M) :
    IsUniqueMaximalOvergroup
      (normalizer
        ((⁅(P : Subgroup G), normalizer ((P : Subgroup G) : Set G)⁆ : Subgroup G) : Set G)) M := by
  have := Fact.mk hp
  set P₀ : Subgroup G := ⁅(P : Subgroup G), normalizer ((P : Subgroup G) : Set G)⁆ with hP₀def
  have hAP : A ≤ (P : Subgroup G) := hAself ▸ inf_le_right
  have hAne : A ≠ ⊥ := by
    intro h
    rw [h] at hArank
    have hle : elementaryAbelianPRank p ↥(⊥ : Subgroup G) ≤ Nat.card ↥(⊥ : Subgroup G) :=
      elementaryAbelianPRank_le_card hp.one_lt
    rw [Subgroup.card_bot] at hle
    omega
  have hPne : (P : Subgroup G) ≠ ⊥ := fun h => hAne (le_bot_iff.1 (h ▸ hAP))
  have hApg : IsPGroup p ↥A := P.isPGroup'.to_le hAP
  have hAcomm : IsMulCommutative ↥A := isMulCommutative_of_inf_centralizer_eq hAself
  have hP₀ne : P₀ ≠ ⊥ := commutator_normalizer_ne_bot hna hp hPne P.card_eq_multiplicity
  have hP₀P : P₀ ≤ (P : Subgroup G) := commutator_normalizer_le _
  have hP₀pg : IsPGroup p ↥P₀ := P.isPGroup'.to_le hP₀P
  have hNP₀ : normalizer (P₀ : Set G) ≠ ⊤ :=
    (normalizer_lt_top_of_isPGroup hna hp hP₀ne hP₀pg).ne
  have hP₀D : P₀ ≤ centralizer ((pComplCoreIn p (mixedFitting M) : Subgroup G) : Set G) :=
    le_centralizer_pComplCoreIn_mixedFitting hna hodd hsolv hp P hAnormal hAself hArank hAtwo hM hCM
  have hDP₀ : pComplCoreIn p (mixedFitting M) ≤ centralizer (P₀ : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1
      (by rw [Subgroup.commutator_comm]
          exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hP₀D)
  have hNPM : normalizer ((P : Subgroup G) : Set G) ≤ M :=
    normalizer_sylow_le_of_scn hna hodd hsolv hp P hAnormal hAself hArank hAtwo hM hCM
  have hPM : (P : Subgroup G) ≤ M := Subgroup.le_normalizer.trans hNPM
  by_cases hall : ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥(mixedFitting M) ≤ 2
  ·
    have hMN : M ≤ normalizer (P₀ : Set G) :=
      (le_sup_pComplCoreIn_normalizer hodd hsolv hp P hM hPM hall).trans
        (sup_le (hDP₀.trans (Subgroup.centralizer_le_normalizer _))
          (normalizer_le_normalizer_commutator (P : Subgroup G)))
    rw [(hM.le_iff_eq hNP₀).1 hMN]
    exact isUniqueMaximalOvergroup_self hM
  ·
    obtain ⟨q, hq, hqr⟩ : ∃ q : ℕ, q.Prime ∧ 2 < elementaryAbelianPRank q ↥(mixedFitting M) := by
      simpa only [not_forall, not_le, exists_prop] using hall
    have hq3 : 3 ≤ elementaryAbelianPRank q ↥(mixedFitting M) := hqr
    have := Fact.mk hq
    have hprank : elementaryAbelianPRank p ↥(mixedFitting M) ≤ 2 :=
      elementaryAbelianPRank_mixedFitting_le_two_of_exists_coatom_ne hna hodd hsolv hp hAcomm hApg
        hArank hAtwo hM
    have hqp : q ≠ p := by rintro rfl; omega
    have hJF : pCoreIn q M ≤ mixedFitting M := by
      rw [mixedFitting_eq, pCoreIn_eq]
      exact Subgroup.map_mono
        (le_fittingRaw_of_normal_of_isNilpotent (pCore_normal q ↥M) (isNilpotent_pCore hq ↥M))
    have hnp : ¬ p ∣ Nat.card ↥(pCoreIn q M) := by
      obtain ⟨n, hn⟩ := (isPGroup_pCoreIn hq M).exists_card_eq
      rw [hn]
      intro hdvd
      exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hdvd)).symm
    have hJD : pCoreIn q M ≤ pComplCoreIn p (mixedFitting M) :=
      le_pComplCoreIn hJF
        ((mixedFitting_le M).trans (le_normalizer_pCoreIn q Subgroup.le_normalizer)) hnp
    have hqJ : 3 ≤ elementaryAbelianPRank q ↥(pCoreIn q M) := by
      rw [elementaryAbelianPRank_pCoreIn hq]
      refine le_trans ?_ (elementaryAbelianPRank_fittingRaw_le_pCore hq ↥M)
      rw [elementaryAbelianPRank_fittingRaw_eq hq]
      exact hq3
    obtain ⟨E, hEJ, hEcomm, hEexp, hEcard⟩ :=
      (mem_elementaryAbelianRanks_subgroup_iff (H := pCoreIn q M) (d := 3) hq).1
        ((le_elementaryAbelianPRank_iff hq.one_lt).1 hqJ)
    have hEea : IsElementaryAbelian q E := isElementaryAbelian_iff.2
      ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hEcomm a a.2 b b.2), hEexp⟩
    have hErank : 3 ≤ elementaryAbelianPRank q ↥E :=
      hEea.le_elementaryAbelianPRank hq hEcard le_rfl
    obtain ⟨N, hN⟩ :=
      exists_isUniqueMaximalOvergroup_of_three_le_elementaryAbelianPRank_mixedFitting
        hna hodd hsolv hM hq hq3 hEea.isMulCommutative hEea.isPGroup hErank
    have hEM : IsUniqueMaximalOvergroup E M := by
      have h : M = N := hN.eq_of_isCoatom hM (hEJ.trans (pCoreIn_le q M))
      rw [h]; exact hN
    exact hEM.mono
      (((hEJ.trans hJD).trans hDP₀).trans (Subgroup.centralizer_le_normalizer _)) hNP₀

end

end CFSG.FeitThompson
