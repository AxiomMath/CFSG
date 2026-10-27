module

public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.AlphaCentralizerUniqueOvergroup
import CFSG.FeitThompson.Local.OutsideSigmaNormalizerRankTwoPlane
import CFSG.FeitThompson.Local.AlphaPrimesInSigmaPrimes
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
import Mathlib

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {X : Type*} [Group X] {r : ℕ}

theorem elementaryAbelianPRank_eq_zero_of_lt_two [Finite X] (hr : r < 2) :
    elementaryAbelianPRank r X = 0 := by
  interval_cases r
  · refine Nat.le_antisymm (elementaryAbelianPRank_le fun d hd => ?_) (Nat.zero_le _)
    obtain ⟨H, hH⟩ := exists_subgroup_card_eq_of_mem_elementaryAbelianRanks hd
    rcases Nat.eq_zero_or_pos d with rfl | hd'
    · exact le_rfl
    · exact absurd (by rw [hH, zero_pow hd'.ne'] : Nat.card ↥H = 0) Nat.card_pos.ne'
  · rw [elementaryAbelianPRank_eq_sSup, Nat.sSup_of_not_bddAbove]
    rintro ⟨b, hb⟩
    have hmem : b + 1 ∈
        {d | ∃ H : Subgroup X, Nonempty (↥H ≃* (Fin d → Multiplicative (ZMod 1)))} := by
      refine ⟨⊥, ⟨?_⟩⟩
      have h1 : Unique ↥(⊥ : Subgroup X) := inferInstance
      have h2 : Unique (Fin (b + 1) → Multiplicative (ZMod 1)) := inferInstance
      exact MulEquiv.ofUnique
    exact absurd (hb hmem) (by omega)

theorem elementaryAbelianPRank_le_minFac [Finite X] (hr : 2 ≤ r) :
    elementaryAbelianPRank r X ≤ elementaryAbelianPRank r.minFac X := by
  have hr0 : r ≠ 0 := by omega
  have hs : r.minFac.Prime := Nat.minFac_prime (by omega)
  refine elementaryAbelianPRank_le fun d hd => ?_
  obtain ⟨H, ⟨e⟩⟩ := mem_elementaryAbelianRanks.1 hd
  obtain ⟨f, hf⟩ : ∃ f : Multiplicative (ZMod r.minFac) →* Multiplicative (ZMod r),
      Function.Injective f := by
    set a : ZMod r := ((r / r.minFac : ℕ) : ZMod r) with ha
    have hcard : addOrderOf a = r.minFac := by
      rw [ha, ZMod.addOrderOf_coe _ hr0,
        Nat.gcd_eq_right (Nat.div_dvd_of_dvd (Nat.minFac_dvd r)),
        Nat.div_div_self (Nat.minFac_dvd r) hr0]
    set x : Multiplicative (ZMod r) := Multiplicative.ofAdd a with hx
    have hord : orderOf x = r.minFac := by rw [hx, orderOf_ofAdd_eq_addOrderOf, hcard]
    have hB : Nat.card ↥(zpowers x) = r.minFac := by rw [Nat.card_zpowers, hord]
    have e2 : Multiplicative (ZMod r.minFac) ≃* ↥(zpowers x) := by
      rw [← hB]; exact zmodCyclicMulEquiv inferInstance
    exact ⟨(zpowers x).subtype.comp e2.toMonoidHom,
      (Subgroup.subtype_injective _).comp e2.injective⟩
  let g : (Fin d → Multiplicative (ZMod r.minFac)) →* (Fin d → Multiplicative (ZMod r)) :=
    MonoidHom.pi fun i => f.comp (Pi.evalMonoidHom _ i)
  have hg : Function.Injective g := fun u v huv => funext fun i => hf (congrFun huv i)
  have hcomp : Function.Injective ((H.subtype.comp e.symm.toMonoidHom).comp g) :=
    ((Subgroup.subtype_injective _).comp e.symm.injective).comp hg
  calc d = elementaryAbelianPRank r.minFac (Fin d → Multiplicative (ZMod r.minFac)) :=
        (elementaryAbelianPRank_pi hs.one_lt d).symm
    _ ≤ elementaryAbelianPRank r.minFac X :=
        elementaryAbelianPRank_le_of_injective hs.one_lt hcomp

theorem elementaryAbelianPRank_le_of_forall_prime [Finite X] {n : ℕ}
    (h : ∀ s : ℕ, s.Prime → elementaryAbelianPRank s X ≤ n) (r : ℕ) :
    elementaryAbelianPRank r X ≤ n := by
  rcases lt_or_ge r 2 with hr | hr
  · rw [elementaryAbelianPRank_eq_zero_of_lt_two hr]; exact Nat.zero_le _
  · exact (elementaryAbelianPRank_le_minFac hr).trans (h _ (Nat.minFac_prime (by omega)))

variable {G : Type*} [Group G]

theorem isUniqueMaximalOvergroup_normalizer_of_two_le_elementaryAbelianPRank
    [Finite G] [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) {M Y : Subgroup G}
    (hM : IsCoatom M) (hYM : Y ≤ M) {t : ℕ} (ht : t.Prime) (htα : t ∉ alphaPrimes ↥M)
    (hYne : Y ≠ ⊥) (hYt : IsPGroup t ↥Y) {r : ℕ} (hr : r.Prime)
    (hrank : 2 ≤ elementaryAbelianPRank r
      ↥(CFSG.FeitThompson.Prep08.alphaCoreOf M ⊓ centralizer (Y : Set G))) :
    IsUniqueMaximalOvergroup (normalizer (Y : Set G)) M := by
  have := Fact.mk ht
  have hYα : ∀ s ∈ (Nat.card Y).primeFactors, s ∉ alphaPrimes ↥M := by
    intro s hs
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hYt
    obtain ⟨hsp, hsd, -⟩ := Nat.mem_primeFactors.1 hs
    rw [hn] at hsd
    rw [(Nat.prime_dvd_prime_iff_eq hsp ht).1 (hsp.dvd_of_dvd_pow hsd)]
    exact htα
  have huniq :=
    isUniqueMaximalOvergroup_inf_centralizer_of_two_le_elementaryAbelianPRank_inf_alphaCore
      hna hodd hsolv hM hYM hYα hr hrank
  exact huniq.mono (inf_le_right.trans (centralizer_le_normalizer _))
    (normalizer_lt_top_of_isPGroup hna ht hYne hYt).ne

theorem elementaryAbelianPRank_inf_alphaCoreOf_centralizer_le_one [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) {M P Q : Subgroup G} {p q : ℕ}
    (hset : CFSG.FeitThompson.Prep08.IsRegularTauOneAlphaSetup M P Q p q) (r : ℕ) :
    elementaryAbelianPRank r
        ↥(CFSG.FeitThompson.Prep08.alphaCoreOf M ⊓ centralizer ((P : Subgroup G) : Set G)) ≤ 1 ∧
      elementaryAbelianPRank r
        ↥(CFSG.FeitThompson.Prep08.alphaCoreOf M ⊓ centralizer ((Q : Subgroup G) : Set G)) ≤ 1 := by
  have hM := hset.isCoatom_M
  have hp : p.Prime := prime_of_mem_tau1Primes hset.mem_tau1
  have hpσ : p ∉ sigmaPrimes M := notMem_sigmaPrimes_of_mem_tau1Primes hset.mem_tau1
  have hpα : p ∉ alphaPrimes ↥M := fun h =>
    hpσ (alphaPrimes_subset_sigmaPrimes hna hodd hsolv hM h)
  have hPcard := hset.natCard_P
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hPcard
    exact hp.one_lt.ne hPcard
  have hPp : IsPGroup p ↥P := IsPGroup.of_card (by rw [pow_one, hPcard])
  refine ⟨elementaryAbelianPRank_le_of_forall_prime (fun s hs => ?_) r,
    elementaryAbelianPRank_le_of_forall_prime (fun s hs => ?_) r⟩
  ·
    by_contra hcon
    have h2 : 2 ≤ elementaryAbelianPRank s
        ↥(CFSG.FeitThompson.Prep08.alphaCoreOf M ⊓ centralizer ((P : Subgroup G) : Set G)) := by omega
    have huniq := isUniqueMaximalOvergroup_normalizer_of_two_le_elementaryAbelianPRank
      hna hodd hsolv hM hset.le_P hp hpα hPne hPp hs h2
    have hrank2 := elementaryAbelianPRank_eq_two_of_notMem_sigmaPrimes hna hodd hsolv hM hp hpσ
      hPcard huniq.le
    rw [elementaryAbelianPRank_eq_one_of_mem_tau1Primes hset.mem_tau1] at hrank2
    exact absurd hrank2 (by norm_num)
  ·
    by_contra hcon
    have h2 : 2 ≤ elementaryAbelianPRank s
        ↥(CFSG.FeitThompson.Prep08.alphaCoreOf M ⊓ centralizer ((Q : Subgroup G) : Set G)) := by omega
    have huniq := isUniqueMaximalOvergroup_normalizer_of_two_le_elementaryAbelianPRank
      hna hodd hsolv hM hset.le_Q hset.prime_q hset.q_notMem_alpha hset.Q_ne_bot hset.isPGroup_Q
      hs h2
    exact hset.not_unique huniq.setOf_eq_singleton

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open CFSG.FeitThompson

universe u

theorem FTS_regular_tau_one_alpha_centralizer_rank_bounds :
    Statements.FTS_regular_tau_one_alpha_centralizer_rank_bounds.{u} := by
  intro G _ _ hG _M _P _Q _p _q hset r
  have := hG.isSimpleGroup
  exact elementaryAbelianPRank_inf_alphaCoreOf_centralizer_le_one hG.not_isMulCommutative
    hG.odd_natCard hG.isSolvable_of_ne_top hset r

end

end CFSG.FeitThompson.Proofs
