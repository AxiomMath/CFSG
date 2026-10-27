module

public import CFSG.FeitThompson.Local.PrimeFittingNormalSelfCentralizingAbelian
public import CFSG.FeitThompson.Definitions.MaximalANormalizedQSubgroups
import CFSG.FeitThompson.Local.ThompsonTransitivityRankThreeScn
import CFSG.FeitThompson.Local.TrivialComplementaryCoreMaximalSylow
import CFSG.FeitThompson.Local.MaximalNormalizedPSubgroupSingletonTrivial
import CFSG.FeitThompson.Local.CentralSylowFixedFreeCycle
import CFSG.FeitThompson.Local.InvariantRankTwoFactorsFixedFreeCycle
import CFSG.FeitThompson.Local.FittingSupportExcludesNormalCore
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p q : ℕ} {M P A : Subgroup G}

theorem prime_dvd_natCard_of_isPGroup_of_ne_bot {F : Subgroup G} (hp : p.Prime)
    (hF : IsPGroup p ↥F) (hFbot : F ≠ ⊥) : p ∣ Nat.card ↥F := by
  have := Fact.mk hp
  obtain ⟨n, hn⟩ := hF.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hFbot (Subgroup.eq_bot_of_card_eq _ (by simpa using hn))
  exact hn ▸ dvd_pow_self p hn0

theorem normalizer_le_normalizer_pCoreIn (q : ℕ) (Y : Subgroup G) :
    normalizer (Y : Set G) ≤ normalizer ((pCoreIn q Y : Subgroup G) : Set G) := by
  rw [pCoreIn_eq]
  exact normalizer_le_normalizer_map_subtype Y (pCore q ↥Y)

theorem pCoreIn_eq_bot_iff (q : ℕ) (Y : Subgroup G) :
    pCoreIn q Y = ⊥ ↔ pCore q ↥Y = ⊥ := by
  rw [pCoreIn_eq, Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective]

theorem pCore_eq_bot_of_not_dvd_natCard {X : Type*} [Group X] [Finite X] (hq : q.Prime)
    (hX : ¬ q ∣ Nat.card X) : pCore q X = ⊥ := by
  have := Fact.mk hq
  obtain ⟨n, hn⟩ := (isPGroup_pCore hq X).exists_card_eq
  refine Subgroup.eq_bot_of_card_eq _ ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simpa using hn
  · exact absurd ((hn ▸ dvd_pow_self q hn0.ne' : q ∣ Nat.card ↥(pCore q X)).trans
      (pCore q X).card_subgroup_dvd_card) hX

theorem eq_bot_of_forall_pCoreIn_eq_bot {Y : Subgroup G} [Group.IsSolvable ↥Y]
    (h : ∀ r : ℕ, r.Prime → pCoreIn r Y = ⊥) : Y = ⊥ := by
  have hF : fittingRaw ↥Y = ⊥ := by
    rw [fittingRaw_eq_iSup_pCore]
    exact le_bot_iff.1 (iSup₂_le fun r hr => le_of_eq ((pCoreIn_eq_bot_iff r Y).1 (h r hr)))
  have := subsingleton_of_fittingRaw_eq_bot ↥Y hF
  exact Subgroup.eq_bot_of_subsingleton Y

namespace IsPrimeFittingSylowSetup

variable (h : IsPrimeFittingSylowSetup p M P A)

include h

theorem prime_dvd_natCard_subgroup : p ∣ Nat.card ↥M :=
  (prime_dvd_natCard_of_isPGroup_of_ne_bot h.prime h.isPGroup_mixedFitting
    h.mixedFitting_ne_bot).trans (Subgroup.card_dvd_of_le (mixedFitting_le M))

theorem prime_dvd_natCard : p ∣ Nat.card G :=
  h.prime_dvd_natCard_subgroup.trans M.card_subgroup_dvd_card

theorem mixedFitting_le_normalizer : mixedFitting M ≤ normalizer (A : Set G) :=
  h.mixedFitting_le_sylow.trans (le_normalizer_of_normal_subgroupOf h.le_sylow h.normal)

theorem not_dvd_natCard_fittingRaw (hq : q.Prime) (hqp : q ≠ p) :
    ¬ q ∣ Nat.card ↥(fittingRaw ↥M) := by
  have := Fact.mk h.prime
  obtain ⟨n, hn⟩ := h.isPGroup_fittingRaw.exists_card_eq
  rw [hn]
  exact fun hdvd => hqp ((Nat.prime_dvd_prime_iff_eq hq h.prime).1 (hq.dvd_of_dvd_pow hdvd))

theorem natCard_sylow_eq [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K) :
    Nat.card ↥P = p ^ (Nat.card G).factorization p :=
  (normalizer_le_and_natCard_eq_of_trivial_pComplCore h.prime hna hodd hsolv h.isCoatom
    h.prime_dvd_natCard_subgroup h.sylow_le h.card_sylow h.pComplCore_eq_bot).2

theorem eq_of_mem_maximalNormalizedPSubgroups [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hA3 : 3 ∈ elementaryAbelianRanks p ↥A) (hq : q.Prime) (hqp : q ≠ p) {Q₁ Q₂ : Subgroup G}
    (hQ₁ : Q₁ ∈ maximalNormalizedPSubgroups A q) (hQ₂ : Q₂ ∈ maximalNormalizedPSubgroups A q) :
    Q₁ = Q₂ := by
  have := Fact.mk h.prime
  have hcard := h.natCard_sylow_eq hna hodd hsolv
  have hself : centralizer (A : Set G) ⊓ (Sylow.ofCard P hcard : Subgroup G) = A := by
    rw [Sylow.coe_ofCard, inf_comm]; exact h.centralizer_inf_eq
  have hnormal : (A.subgroupOf (Sylow.ofCard P hcard : Subgroup G)).Normal := by
    rw [Sylow.coe_ofCard]; exact h.normal
  obtain ⟨k, hk, hkeq⟩ := exists_mem_pComplCoreIn_centralizer_conj_inv_smul_eq_of_rank_three_sylow
    hna hodd hsolv h.prime (Sylow.ofCard P hcard) hnormal hself hA3 hq hqp hQ₁ hQ₂
  rw [h.pComplCoreIn_centralizer_eq_bot, Subgroup.mem_bot] at hk
  subst hk
  simpa using hkeq

theorem exists_maximalNormalizedPSubgroups_eq_singleton [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hA3 : 3 ∈ elementaryAbelianRanks p ↥A) (hq : q.Prime) (hqp : q ≠ p) :
    ∃ Q : Subgroup G, maximalNormalizedPSubgroups A q = {Q} := by
  obtain ⟨Q, hQ⟩ := maximalNormalizedPSubgroups_nonempty A q
  exact ⟨Q, Set.eq_singleton_iff_unique_mem.2 ⟨hQ, fun Q' hQ' =>
    h.eq_of_mem_maximalNormalizedPSubgroups hna hodd hsolv hA3 hq hqp hQ' hQ⟩⟩

theorem maximalNormalizedPSubgroups_mixedFitting_eq_singleton {Q : Subgroup G}
    (hQ : maximalNormalizedPSubgroups A q = {Q}) :
    maximalNormalizedPSubgroups (mixedFitting M) q = {Q} := by
  have hQmem : Q ∈ maximalNormalizedPSubgroups A q := by rw [hQ]; rfl
  have hAF : A ≤ mixedFitting M := h.le_mixedFitting
  have hFQ : mixedFitting M ≤ normalizer (Q : Set G) :=
    le_normalizer_of_maximalNormalizedPSubgroups_eq_singleton h.mixedFitting_le_normalizer hQ
  have hQF : Q ∈ maximalNormalizedPSubgroups (mixedFitting M) q :=
    mem_maximalNormalizedPSubgroups_of_forall (isPGroup_of_mem hQmem) hFQ
      fun R hR hRF hQR => eq_of_mem_of_le hQmem hR (hAF.trans hRF) hQR
  refine Set.eq_singleton_iff_unique_mem.2 ⟨hQF, fun Q' hQ' => ?_⟩
  obtain ⟨Q'', hQ'', hle⟩ := exists_mem_maximalNormalizedPSubgroups_ge (isPGroup_of_mem hQ')
    (hAF.trans (le_normalizer_of_mem hQ'))
  rw [hQ, Set.mem_singleton_iff] at hQ''
  exact (eq_of_mem_of_le hQ' (isPGroup_of_mem hQF) hFQ (hQ'' ▸ hle)).symm

theorem eq_bot_of_isPGroup_of_le_normalizer_of_ne [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hA3 : 3 ∈ elementaryAbelianRanks p ↥A) (hq : q.Prime) (hqp : q ≠ p) {R : Subgroup G}
    (hR : IsPGroup q ↥R) (hRA : A ≤ normalizer (R : Set G)) : R = ⊥ := by
  obtain ⟨Q, hQ⟩ := h.exists_maximalNormalizedPSubgroups_eq_singleton hna hodd hsolv hA3 hq hqp
  have hQbot : Q = ⊥ :=
    eq_bot_of_maximalNormalizedPSubgroups_eq_singleton hna hq h.isCoatom
      (le_normalizer_mixedFitting M) (h.not_dvd_natCard_fittingRaw hq hqp)
      (h.maximalNormalizedPSubgroups_mixedFitting_eq_singleton hQ)
  obtain ⟨Q', hQ', hle⟩ := exists_mem_maximalNormalizedPSubgroups_ge hR hRA
  rw [hQ, Set.mem_singleton_iff] at hQ'
  exact le_bot_iff.1 (hQbot ▸ hQ' ▸ hle)

theorem eq_bot_of_not_dvd_natCard_of_le_normalizer [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hA3 : 3 ∈ elementaryAbelianRanks p ↥A) {Y : Subgroup G} (hY : ¬ p ∣ Nat.card ↥Y)
    (hYA : A ≤ normalizer (Y : Set G)) : Y = ⊥ := by
  have hYtop : Y ≠ ⊤ := fun hcon =>
    hY (by rw [hcon, Subgroup.card_top]; exact h.prime_dvd_natCard)
  have := hsolv Y hYtop
  refine eq_bot_of_forall_pCoreIn_eq_bot fun r hr => ?_
  rcases eq_or_ne r p with rfl | hrp
  · exact (pCoreIn_eq_bot_iff r Y).2 (pCore_eq_bot_of_not_dvd_natCard hr hY)
  · exact h.eq_bot_of_isPGroup_of_le_normalizer_of_ne hna hodd hsolv hA3 hr hrp
      (isPGroup_pCoreIn hr Y) (hYA.trans (normalizer_le_normalizer_pCoreIn r Y))

end IsPrimeFittingSylowSetup

theorem eq_bot_of_not_dvd_natCard_of_le_normalizer_of_prime_fitting [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    {F Y : Subgroup G} (hM : IsCoatom M) (hp : p.Prime) (hF : F = mixedFitting M) (hFbot : F ≠ ⊥)
    (hFp : IsPGroup p ↥F) (hPM : P ≤ M)
    (hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p) (hAP : A ≤ P)
    (hAnormal : (A.subgroupOf P).Normal) (hAcomm : IsMulCommutative ↥A)
    (hCP : P ⊓ centralizer (A : Set G) = A) (hA3 : 3 ∈ elementaryAbelianRanks p ↥A)
    (hY : ¬ p ∣ Nat.card ↥Y) (hYA : A ≤ normalizer (Y : Set G)) : Y = ⊥ := by
  subst hF
  have h : IsPrimeFittingSylowSetup p M P A :=
    { isCoatom := hM, isSolvable := hsolv M hM.1, odd := odd_natCard_subgroup hodd M,
      prime := hp, mixedFitting_ne_bot := hFbot, isPGroup_mixedFitting := hFp,
      sylow_le := hPM, card_sylow := hPcard, le_sylow := hAP, normal := hAnormal,
      isMulCommutative := hAcomm, centralizer_inf_eq := hCP }
  exact h.eq_bot_of_not_dvd_natCard_of_le_normalizer hna hodd hsolv hA3 hY hYA

theorem eq_bot_of_coprime_natCard_of_le_normalizer_of_prime_fitting [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    {F Y : Subgroup G} (hM : IsCoatom M) (hp : p.Prime) (hF : F = mixedFitting M) (hFbot : F ≠ ⊥)
    (hFp : IsPGroup p ↥F) (hPM : P ≤ M)
    (hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p) (hAP : A ≤ P)
    (hAnormal : (A.subgroupOf P).Normal) (hAcomm : IsMulCommutative ↥A)
    (hCP : P ⊓ centralizer (A : Set G) = A) (hA3 : 3 ∈ elementaryAbelianRanks p ↥A)
    (hY : Nat.Coprime p (Nat.card ↥Y)) (hYA : A ≤ normalizer (Y : Set G)) : Y = ⊥ :=
  eq_bot_of_not_dvd_natCard_of_le_normalizer_of_prime_fitting hna hodd hsolv hM hp hF hFbot hFp
    hPM hPcard hAP hAnormal hAcomm hCP hA3 (hp.coprime_iff_not_dvd.1 hY) hYA

end

end CFSG.FeitThompson
