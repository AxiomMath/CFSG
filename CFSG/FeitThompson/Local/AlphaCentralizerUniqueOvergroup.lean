module

public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.Local.FixedMaximalElementaryAbelianTrivialAction
import CFSG.FeitThompson.Local.AlphaCoreNormalHall
import CFSG.FeitThompson.Local.PlaneRankThreeCentralizerUniqueness
import CFSG.FeitThompson.OddOrder.RankThreeUniquenessMaximalOvergroup
import CFSG.FeitThompson.Local.PComplementControlSylowNormalizer
import CFSG.FeitThompson.Local.PComplementQuotientSylowRank
import CFSG.FeitThompson.Local.MaximalInvariantSubgroupTransport
import CFSG.FeitThompson.OddOrder.RankTwoKernelSmallerComplementPrimes
import CFSG.FeitThompson.Foundations.SylowNormalizerSelfNormalizing
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G]

theorem isUniqueMaximalOvergroup_inf_centralizer_of_two_le_elementaryAbelianPRank_inf_alphaCore
    [Finite G] [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) {M X : Subgroup G}
    (hM : IsCoatom M) (hXM : X ≤ M)
    (hXα : ∀ q ∈ (Nat.card X).primeFactors, q ∉ alphaPrimes ↥M)
    {p : ℕ} (hp : p.Prime)
    (hrank : 2 ≤ elementaryAbelianPRank p
      ↥((alphaCore ↥M).map M.subtype ⊓ centralizer (X : Set G))) :
    IsUniqueMaximalOvergroup (M ⊓ centralizer (X : Set G)) M := by
  have := Fact.mk hp
  set B : Subgroup G := (alphaCore ↥M).map M.subtype with hBdef
  have hBM : B ≤ M := Subgroup.map_subtype_le _
  have hBHall : IsHallSubgroup (alphaPrimes ↥M) B :=
    isHallSubgroup_map_subtype_alphaCore hna hodd hsolv hM
  have hinf_ne_top : (M ⊓ centralizer (X : Set G)) ≠ ⊤ := fun h =>
    hM.1 (top_le_iff.1 (h ▸ inf_le_left))
  obtain ⟨E, hEle, hcomm, hexp, hEcard⟩ :=
    (mem_elementaryAbelianRanks_subgroup_iff hp).1
      ((le_elementaryAbelianPRank_iff hp.one_lt).1 hrank)
  have hEea : IsElementaryAbelian p E :=
    isElementaryAbelian_iff.2
      ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hcomm a a.2 b b.2), hexp⟩
  have hEB : E ≤ B := hEle.trans inf_le_left
  have hECX : E ≤ centralizer (X : Set G) := hEle.trans inf_le_right
  have hEM : E ≤ M := hEB.trans hBM
  have hpdvdE : p ∣ Nat.card E := hEcard ▸ dvd_pow_self p two_ne_zero
  have hpα : p ∈ alphaPrimes ↥M :=
    isPiNumber_iff.1 hBHall.natCard p (Nat.mem_primeFactors.2
      ⟨hp, hpdvdE.trans (Subgroup.card_dvd_of_le hEB), Nat.card_pos.ne'⟩)
  have hMrank : 3 ≤ elementaryAbelianPRank p ↥M := (mem_alphaPrimes.1 hpα).2
  have hpodd : Odd p := hodd.of_dvd_nat (hpdvdE.trans E.card_subgroup_dvd_card)
  have hXpi : IsPiNumber (alphaPrimes ↥M)ᶜ (Nat.card X) := isPiNumber_compl_iff.2 hXα
  have hcopB : Nat.Coprime (Nat.card B) (Nat.card X) :=
    hBHall.natCard.coprime_of_compl hXpi Nat.card_pos.ne' Nat.card_pos.ne'
  have hXB : X ≤ normalizer (B : Set G) :=
    hXM.trans (le_normalizer_map_subtype_of_normal (alphaCore_normal ↥M))
  have hXCE : X ≤ centralizer (E : Set G) := fun x hx =>
    mem_centralizer_iff.2 fun e he => (mem_centralizer_iff.1 (hECX he) x hx).symm
  have hXNE : X ≤ normalizer (E : Set G) := hXCE.trans (centralizer_le_normalizer _)
  have hBXtop : (B ⊔ X : Subgroup G) ≠ ⊤ := fun h => hM.1 (top_le_iff.1 (h ▸ sup_le hBM hXM))
  obtain ⟨P, hPB, hPp, hEP, hXP, hidx⟩ :=
    exists_isPGroup_ge_le_normalizer_not_dvd_index (hsolv _ hBXtop) hXB hcopB hp hEB hXNE
      hEea.isPGroup
  have hPM : P ≤ M := hPB.trans hBM
  have hpBidx : ¬ p ∣ B.index := fun h =>
    isPiNumber_iff.1 hBHall.index p
      (Nat.mem_primeFactors.2 ⟨hp, h, Subgroup.index_ne_zero_of_finite⟩) hpα
  have hPindex : ¬ p ∣ P.index := by
    rw [← Subgroup.relIndex_mul_index hPB]
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact hidx h
    · exact hpBidx h
  have hPcardG : Nat.card ↥P = p ^ (Nat.card G).factorization p :=
    natCard_eq_pow_factorization_iff.2 ⟨hPp, hPindex⟩
  have hPsub : Nat.card ↥(P.subgroupOf M) = p ^ (Nat.card ↥M).factorization p :=
    natCard_subgroupOf_eq_pow_factorization hPcardG hPM
  have hrankP : 3 ≤ elementaryAbelianPRank p ↥P := by
    have h1 : elementaryAbelianPRank p ↥(P.subgroupOf M) = elementaryAbelianPRank p ↥P :=
      elementaryAbelianPRank_eq_of_mulEquiv hp.one_lt (subgroupOfEquivOfLe hPM)
    have h2 := elementaryAbelianPRank_eq_of_natCard_eq_pow_factorization hp hPsub
    omega
  by_cases hD : 3 ≤ elementaryAbelianPRank p ↥(P ⊓ centralizer (E : Set G))
  ·
    obtain ⟨N, hN⟩ :=
      exists_isUniqueMaximalOvergroup_of_plane_of_three_le_elementaryAbelianPRank_centralizer
        hp hp hna hodd hsolv hEea hEcard
        (hD.trans (elementaryAbelianPRank_le_of_le hp.one_lt inf_le_right))
    have hNM : M = N := hN.eq_of_isCoatom hM hEM
    subst hNM
    exact hN.mono (le_inf hEM hECX) hinf_ne_top
  ·
    have hEPsub : Maximal (IsElementaryAbelianSubgroup p) (E.subgroupOf P) := by
      refine ⟨(isElementaryAbelianSubgroup_iff.2 ⟨hEea.isMulCommutative, hexp⟩).comap
        P.subtype_injective, fun A hA hle => ?_⟩
      have hA' : IsElementaryAbelian p (A.map P.subtype) :=
        isElementaryAbelian_iff.2 ⟨(hA.map P.subtype).isMulCommutative,
          (hA.map P.subtype).pow_eq_one⟩
      have hAP : A.map P.subtype ≤ P := Subgroup.map_subtype_le _
      have hEA' : E ≤ A.map P.subtype := fun e he =>
        ⟨⟨e, hEP he⟩, hle (mem_subgroupOf.2 he), rfl⟩
      obtain ⟨d, hd⟩ := hA'.exists_natCard_eq_pow hp
      have hdle : d ≤ elementaryAbelianPRank p ↥(P ⊓ centralizer (E : Set G)) :=
        hA'.le_elementaryAbelianPRank hp hd (le_inf hAP (hA'.le_centralizer hEA'))
      have h2d : 2 ≤ d := by
        have hdvd := Subgroup.card_dvd_of_le hEA'
        rw [hEcard, hd] at hdvd
        exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd
      have hd2 : d = 2 := by omega
      have hEeq : E = A.map P.subtype :=
        Subgroup.eq_of_le_of_card_ge hEA' (by rw [hd, hd2, hEcard])
      intro a ha
      rw [mem_subgroupOf, hEeq]
      exact ⟨a, ha, rfl⟩
    have hcopXP : (Nat.card ↥X).Coprime (Nat.card ↥P) :=
      Nat.Coprime.symm ((hBHall.natCard.of_dvd (Subgroup.card_dvd_of_le hPB)
        Nat.card_pos.ne').coprime_of_compl hXpi Nat.card_pos.ne' Nat.card_pos.ne')
    have hfix : ∀ a : ↥X, ∀ e ∈ E.subgroupOf P, conjOnNormalized P hXP a e = e := by
      intro a e he
      refine Subtype.ext ?_
      rw [conjOnNormalized_apply_coe]
      have hc : (a : G) * (e : G) = (e : G) * (a : G) :=
        mem_centralizer_iff.1 (hECX (mem_subgroupOf.1 he)) (a : G) a.2
      rw [hc]
      group
    have htriv := apply_eq_self_of_maximal_isElementaryAbelianSubgroup_fixed hp hpodd hPp
      (conjOnNormalized P hXP) hcopXP hEPsub hfix
    have hPCX : P ≤ centralizer (X : Set G) := by
      intro y hy
      refine mem_centralizer_iff.2 fun x hx => ?_
      have h2 : (x : G) * y * x⁻¹ = y := by
        have h3 := congrArg Subtype.val (htriv ⟨x, hx⟩ ⟨y, hy⟩)
        rwa [conjOnNormalized_apply_coe] at h3
      calc x * y = x * y * x⁻¹ * x := by group
        _ = y * x := by rw [h2]
    have hrank3 : 3 ≤ maxElementaryAbelianPRank ↥(M ⊓ centralizer (X : Set G)) :=
      le_trans (hrankP.trans (elementaryAbelianPRank_le_of_le hp.one_lt (le_inf hPM hPCX)))
        (elementaryAbelianPRank_le_maxElementaryAbelianPRank hp)
    obtain ⟨N, hN⟩ := exists_isUniqueMaximalOvergroup_of_three_le_maxElementaryAbelianPRank
      hna hodd hsolv hinf_ne_top hrank3
    exact hN.eq_of_isCoatom hM inf_le_left ▸ hN

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup CFSG.FeitThompson

universe u

theorem FTS_alpha_centralizer_uniqueness :
    Statements.FTS_alpha_centralizer_uniqueness.{u} := by
  intro G _ _ hG M X hM hXM hprimes hrank
  obtain ⟨p, hp, hrank⟩ := hrank
  have := hG.simple
  rw [CFSG.FeitThompson.Prep06.alphaCoreIn_eq] at hrank
  exact isUniqueMaximalOvergroup_inf_centralizer_of_two_le_elementaryAbelianPRank_inf_alphaCore
    hG.nonabelian hG.odd hG.solvable hM hXM hprimes hp hrank

end

end CFSG.FeitThompson.Proofs
