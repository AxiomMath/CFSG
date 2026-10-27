module

public import CFSG.FeitThompson.Definitions.NarrowPGroupsAndBetaPrimes
public import CFSG.FeitThompson.Definitions.UniqueMaximalOvergroup
public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Local.BetaPrimesSigmaCompatibility
import CFSG.FeitThompson.Local.BetaSylowNormalizerUniqueMaximal
import CFSG.FeitThompson.OddOrder.SigmaSylowIsAmbientSylow
import CFSG.FeitThompson.Local.AbelianSylowNormalPrimeCentralizerFitting
import CFSG.FeitThompson.Local.FittingEqualsChiefActionKernel
import CFSG.FeitThompson.Local.SimpleGroupNormalizerProper
import CFSG.FeitThompson.Foundations.SylowNormalizerSelfNormalizing

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {p q : ℕ} {M P Q : Subgroup G}

theorem le_centralizer_of_isPGroup_of_le_normalizer_of_natCard_eq_prime (hp : p.Prime)
    (hPcard : Nat.card P = p) {N : Subgroup G} (hN : IsPGroup p N)
    (hNP : N ≤ normalizer (P : Set G)) : N ≤ centralizer (P : Set G) := by
  have := Fact.mk hp
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by simp [hPcard, hp.pos.ne'])
  have hcyc : IsCyclic P := isCyclic_of_prime_card hPcard
  intro x hx
  have hx1 : P.normalizerMonoidHom ⟨x, hNP hx⟩ = 1 := by
    obtain ⟨n, hn⟩ := hN ⟨x, hx⟩
    set σ := P.normalizerMonoidHom ⟨x, hNP hx⟩ with hσ
    have hdvd1 : orderOf σ ∣ p ^ n := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [hσ, ← map_pow]
      have hxp : (⟨x, hNP hx⟩ : ↥(normalizer (P : Set G))) ^ p ^ n = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val hn)
      rw [hxp, map_one]
    have hdvd2 : orderOf σ ∣ p - 1 := by
      have h := orderOf_dvd_natCard σ
      rwa [IsCyclic.card_mulAut, hPcard, Nat.totient_prime hp] at h
    have hcop : Nat.Coprime (p ^ n) (p - 1) := by
      refine Nat.Coprime.pow_left _ ?_
      have h : p - 1 + 1 = p := by have := hp.pos; omega
      rw [← h]
      simp [Nat.Coprime]
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2)
  have hker : (⟨x, hNP hx⟩ : ↥(normalizer (P : Set G))) ∈ P.normalizerMonoidHom.ker :=
    MonoidHom.mem_ker.2 hx1
  rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hker
  exact hker

section Ambient

variable [Finite G] [IsSimpleGroup G]

theorem exists_isUniqueMaximalOvergroup_le_centralizer_of_natCard_eq_prime_of_le_fitting
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M)
    (hq : q ∈ betaPrimes ↥M) (hQM : Q ≤ M) (hQnormal : (Q.subgroupOf M).Normal)
    (hQcard : Nat.card Q = q ^ (Nat.card ↥M).factorization q)
    (hp : p.Prime) (hPF : P ≤ (fittingRaw ↥M).map M.subtype) (hPcard : Nat.card P = p) :
    ∃ Y : Subgroup G, Y ≤ centralizer (P : Set G) ∧ Y ≤ M ∧ IsUniqueMaximalOvergroup Y M := by
  have hqp : q.Prime := prime_of_mem_betaPrimes hq
  have := Fact.mk hqp
  have hPpg : IsPGroup p ↥P := IsPGroup.of_card (n := 1) (by simpa using hPcard)
  have hqσ : q ∈ sigmaPrimes M := betaPrimes_subset_sigmaPrimes hna hodd hsolv hM hq
  have hqβG : q ∈ betaPrimes G := (mem_betaPrimes_subgroup_iff_of_mem_sigmaPrimes hqσ).1 hq
  have hQG : Nat.card Q = q ^ (Nat.card G).factorization q :=
    natCard_eq_pow_factorization_of_mem_sigmaPrimes hqσ hQM hQcard
  set T : Sylow q G := Sylow.ofCard Q hQG with hT
  have hTQ : (T : Subgroup G) = Q := Sylow.coe_ofCard _ _
  have hQpg : IsPGroup q Q := IsPGroup.of_card hQcard
  have hQF : Q ≤ (fittingRaw ↥M).map M.subtype :=
    le_map_fittingRaw_of_le_normalizer hQM
      ((normal_subgroupOf_iff_le_normalizer hQM).1 hQnormal) hQpg.isNilpotent
  have hQuniq : IsUniqueMaximalOvergroup Q M := by
    have hbot : normalizer ((⊥ : Subgroup G) : Set G) = ⊤ := normalizer_eq_top_iff.2 inferInstance
    obtain ⟨M', hM'⟩ := exists_isUniqueMaximalOvergroup_inf_normalizer_of_mem_betaPrimes
      hna hodd hsolv hqβG T (X := ⊥) bot_le
    rw [hTQ, hbot, inf_top_eq] at hM'
    exact hM'.eq_of_isCoatom hM hQM ▸ hM'
  by_cases hpq : p = q
  ·
    subst hpq
    have hPM : P ≤ M := hPF.trans (Subgroup.map_subtype_le _)
    have hPQ : P ≤ Q := by
      have := hQnormal
      have h := le_of_isPGroup_of_normal_of_natCard_eq (L := ↥M) hp (Q := Q.subgroupOf M)
        (natCard_subgroupOf_eq_pow_factorization (p := p) (N := M) hQG hQM)
        (T := P.subgroupOf M) (IsPGroup.of_equiv hPpg (subgroupOfEquivOfLe hPM).symm)
      have h2 := Subgroup.map_mono (f := M.subtype) h
      rwa [map_subgroupOf_eq_of_le hPM, map_subgroupOf_eq_of_le hQM] at h2
    obtain ⟨M', hM'⟩ := exists_isUniqueMaximalOvergroup_inf_normalizer_of_mem_betaPrimes
      hna hodd hsolv hqβG T (hTQ ▸ hPQ)
    rw [hTQ] at hM'
    have hYM : Q ⊓ normalizer (P : Set G) ≤ M := inf_le_left.trans hQM
    exact ⟨Q ⊓ normalizer (P : Set G),
      le_centralizer_of_isPGroup_of_le_normalizer_of_natCard_eq_prime hp hPcard
        (hQpg.to_le inf_le_left) inf_le_right, hYM, hM'.eq_of_isCoatom hM hYM ▸ hM'⟩
  ·
    have hcop : (Nat.card Q).Coprime (Nat.card P) := by
      rw [hQcard, hPcard]
      exact Nat.Coprime.pow_left _ ((Nat.coprime_primes hqp hp).2 (Ne.symm hpq))
    exact ⟨Q, le_centralizer_of_coprime_natCard_of_isNilpotent _
      (isNilpotent_map_fittingRaw M) hQF hPF hcop, hQM, hQuniq⟩

theorem normalizer_ne_top_of_natCard_eq_prime (hna : ¬ IsMulCommutative G) (hp : p.Prime)
    (hPcard : Nat.card P = p) : normalizer (P : Set G) ≠ ⊤ := by
  have := Fact.mk hp
  have hPbot : (⊥ : Subgroup G) < P := by
    refine bot_lt_iff_ne_bot.2 fun h => ?_
    rw [h, Subgroup.card_bot] at hPcard
    exact hp.one_lt.ne hPcard
  have hPtop : P < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => ?_
    rw [h, Subgroup.card_top] at hPcard
    exact hna (isCyclic_of_prime_card hPcard).isMulCommutative
  exact (normalizer_lt_top_of_isSimpleGroup hPbot hPtop).ne

theorem centralizer_le_of_natCard_eq_prime_of_le_fitting (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    (hM : IsCoatom M) (hq : q ∈ betaPrimes ↥M) (hQM : Q ≤ M)
    (hQnormal : (Q.subgroupOf M).Normal)
    (hQcard : Nat.card Q = q ^ (Nat.card ↥M).factorization q)
    (hp : p.Prime) (hPF : P ≤ (fittingRaw ↥M).map M.subtype) (hPcard : Nat.card P = p) :
    centralizer (P : Set G) ≤ M := by
  obtain ⟨Y, hYC, -, hY⟩ :=
    exists_isUniqueMaximalOvergroup_le_centralizer_of_natCard_eq_prime_of_le_fitting
      hna hodd hsolv hM hq hQM hQnormal hQcard hp hPF hPcard
  exact hY.le_of_ne_top hYC fun h =>
    normalizer_ne_top_of_natCard_eq_prime hna hp hPcard
      (top_le_iff.1 (h ▸ centralizer_le_normalizer (P : Set G)))

theorem centralizer_le_of_natCard_eq_prime_of_le_fitting_of_sylow (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    (hM : IsCoatom M) (hq : q ∈ betaPrimes ↥M) (S : Sylow q ↥M)
    (hSnormal : (S : Subgroup ↥M).Normal)
    (hp : p.Prime) (hPF : P ≤ (fittingRaw ↥M).map M.subtype) (hPcard : Nat.card P = p) :
    centralizer (P : Set G) ≤ M := by
  have := Fact.mk (prime_of_mem_betaPrimes hq)
  refine centralizer_le_of_natCard_eq_prime_of_le_fitting hna hodd hsolv hM hq
    (Q := (S : Subgroup ↥M).map M.subtype) (Subgroup.map_subtype_le _) ?_ ?_ hp hPF hPcard
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    exact hSnormal
  · rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact S.card_eq_multiplicity

theorem normalizer_le_of_natCard_eq_prime_of_le_fitting (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    (hM : IsCoatom M) (hq : q ∈ betaPrimes ↥M) (hQM : Q ≤ M)
    (hQnormal : (Q.subgroupOf M).Normal)
    (hQcard : Nat.card Q = q ^ (Nat.card ↥M).factorization q)
    (hp : p.Prime) (hPF : P ≤ (fittingRaw ↥M).map M.subtype) (hPcard : Nat.card P = p) :
    normalizer (P : Set G) ≤ M := by
  obtain ⟨Y, hYC, -, hY⟩ :=
    exists_isUniqueMaximalOvergroup_le_centralizer_of_natCard_eq_prime_of_le_fitting
      hna hodd hsolv hM hq hQM hQnormal hQcard hp hPF hPcard
  exact hY.le_of_ne_top (hYC.trans (centralizer_le_normalizer _))
    (normalizer_ne_top_of_natCard_eq_prime hna hp hPcard)

end Ambient

end

end CFSG.FeitThompson
