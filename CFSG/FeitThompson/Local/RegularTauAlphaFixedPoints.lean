module

public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.CriticalRegularComplementFixedPoints
import CFSG.FeitThompson.Local.RegularTauAlphaCentralizerRankBounds
import CFSG.FeitThompson.Local.AlphaCoreNormalHall
import CFSG.FeitThompson.Local.OvergroupJoinsInvariantPrimeSubgroups
import CFSG.FeitThompson.Local.QuotientFittingInvariantComplement
import CFSG.FeitThompson.Local.PComplementQuotientSylowRank
import CFSG.FeitThompson.Local.FittingModuleFaithfulAction
import CFSG.FeitThompson.Local.PComplementControlSylowNormalizer
import CFSG.FeitThompson.Local.SigmaSylowAlphaProductNormal
import CFSG.FeitThompson.Local.InvariantRankTwoFactorsFixedFreeCycle
import CFSG.FeitThompson.Local.AlphaPrimesInSigmaPrimes
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.Foundations.SolvableSubgroupSolvable
public import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson.Prep08

section Aux

variable {X : Type*} [Group X]

theorem eq_bot_of_subgroupOf_eq_bot' {H K : Subgroup X} (hHK : H ≤ K) (h : H.subgroupOf K = ⊥) :
    H = ⊥ := by
  have h2 := congrArg (Subgroup.map K.subtype) h
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hHK, Subgroup.map_bot] at h2

variable [Finite X]

theorem factorization_natCard_eq_of_isHallSubgroup {π : Set ℕ} {H : Subgroup X}
    (hH : IsHallSubgroup π H) {r : ℕ} (hr : r.Prime) (hrπ : r ∈ π) :
    (Nat.card X).factorization r = (Nat.card ↥H).factorization r := by
  have hidx : ¬ r ∣ H.index := CFSG.FeitThompson.Proofs.not_dvd_index_of_isHallSubgroup hH hr hrπ
  have h := H.index_mul_card
  have hi0 : H.index ≠ 0 := fun h0 => hidx (h0 ▸ dvd_zero r)
  rw [← h, Nat.factorization_mul hi0 Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hidx, zero_add]

theorem elementaryAbelianPRank_subgroupOf {r : ℕ} (hr : 1 < r) {H K : Subgroup X} (h : H ≤ K) :
    elementaryAbelianPRank r ↥(H.subgroupOf K) = elementaryAbelianPRank r ↥H :=
  elementaryAbelianPRank_eq_of_mulEquiv hr (subgroupOfEquivOfLe h)

end Aux

variable {G : Type*} [Group G] [Finite G]

theorem inf_alphaCoreOf_centralizer_fixed_points [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) {M P Q : Subgroup G} {p q : ℕ}
    (hset : IsRegularTauOneAlphaSetup M P Q p q) (hAne : alphaCoreOf M ≠ ⊥) :
    alphaCoreOf M ⊓ centralizer ((P : Subgroup G) : Set G) ≠ ⊥ ∧
      alphaCoreOf M ⊓ centralizer (((Q ⊔ P : Subgroup G)) : Set G) = ⊥ := by
  classical
  have hM := hset.isCoatom_M
  set A : Subgroup G := alphaCoreOf M with hAdef
  set K : Subgroup G := (Q ⊔ P : Subgroup G) with hKdef
  have hAM : A ≤ M := alphaCoreOf_le M
  have hKM : K ≤ M := sup_le hset.le_Q hset.le_P
  have hMsolv : Group.IsSolvable ↥M := hsolv M hM.1
  have hp : p.Prime := prime_of_mem_tau1Primes hset.mem_tau1
  have hq : q.Prime := hset.prime_q
  have hpσ : p ∉ sigmaPrimes M := notMem_sigmaPrimes_of_mem_tau1Primes hset.mem_tau1
  have hpα : p ∉ alphaPrimes ↥M := fun h =>
    hpσ (alphaPrimes_subset_sigmaPrimes hna hodd hsolv hM h)
  have hPcard := hset.natCard_P
  have hPp : IsPGroup p ↥P := IsPGroup.of_card (by rw [pow_one, hPcard])
  have hAcard : Nat.card ↥A = Nat.card ↥(alphaCore ↥M) :=
    card_map_of_injective M.subtype_injective
  have hApf : ∀ s : ℕ, s.Prime → s ∣ Nat.card ↥A → s ∈ alphaPrimes ↥M := fun s hs hsd =>
    primeFactors_natCard_alphaCore_subset ↥M
      (Nat.mem_primeFactors.2 ⟨hs, hAcard ▸ hsd, Nat.card_pos.ne'⟩)
  have hQP : Q ⊓ P = ⊥ := disjoint_iff.1 (disjoint_of_coprime_natCard (by
    have := Fact.mk hq
    have := Fact.mk hp
    exact IsPGroup.coprime_card_of_ne q p hset.q_ne Q P hset.isPGroup_Q hPp))
  have hKcard : Nat.card ↥K = Nat.card ↥Q * p := by
    rw [hKdef, natCard_sup_eq_mul_of_le_normalizer hset.normalized hQP, hPcard]
  have hAK : (Nat.card ↥A).Coprime (Nat.card ↥K) := by
    have hQcop : (Nat.card ↥A).Coprime (Nat.card ↥Q) := by
      have := Fact.mk hq
      obtain ⟨n, hn⟩ := hset.isPGroup_Q.exists_card_eq
      rw [hn]
      exact Nat.Coprime.pow_right _
        (Nat.Coprime.symm ((hq.coprime_iff_not_dvd).2 fun hd =>
          hset.q_notMem_alpha (hApf q hq hd)))
    have hPcop : (Nat.card ↥A).Coprime p :=
      Nat.Coprime.symm ((hp.coprime_iff_not_dvd).2 fun hd => hpα (hApf p hp hd))
    rw [hKcard]; exact hQcop.mul_right hPcop
  have hMA : M ≤ normalizer ((A : Subgroup G) : Set G) :=
    le_normalizer_map_subtype_of_normal (alphaCore_normal ↥M)
  have hKA : K ≤ normalizer ((A : Subgroup G) : Set G) := hKM.trans hMA
  have hsolvAK : Group.IsSolvable ↥(A ⊔ K) := isSolvable_of_le (sup_le hAM hKM)
  have hrankbd := elementaryAbelianPRank_inf_alphaCoreOf_centralizer_le_one hna hodd hsolv hset
  obtain ⟨r, hr, hrA, R0, hR0A, hR0r, hR0C, hR0seed⟩ :
      ∃ r : ℕ, r.Prime ∧ r ∣ Nat.card ↥A ∧ ∃ R0 : Subgroup G, R0 ≤ A ∧ IsPGroup r ↥R0 ∧
        R0 ≤ centralizer ((K : Subgroup G) : Set G) ∧
        (A ⊓ centralizer ((K : Subgroup G) : Set G) ≠ ⊥ → R0 ≠ ⊥) := by
    by_cases hfix : A ⊓ centralizer ((K : Subgroup G) : Set G) = ⊥
    · obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd
        (n := Nat.card ↥A) (fun h1 => hAne (Subgroup.card_eq_one.1 h1))
      exact ⟨r, hr, hrd, ⊥, bot_le, IsPGroup.of_card (n := 0) (by simp), bot_le,
        fun h => absurd hfix h⟩
    · obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd
        (n := Nat.card ↥(A ⊓ centralizer ((K : Subgroup G) : Set G)))
        (fun h1 => hfix (Subgroup.card_eq_one.1 h1))
      have := Fact.mk hr
      have : Fintype ↥(A ⊓ centralizer ((K : Subgroup G) : Set G)) := Fintype.ofFinite _
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card
        (G := ↥(A ⊓ centralizer ((K : Subgroup G) : Set G))) r
        (by rwa [← Nat.card_eq_fintype_card])
      set R0 : Subgroup G :=
        (zpowers x).map (A ⊓ centralizer ((K : Subgroup G) : Set G)).subtype with hR0def
      have hR0card : Nat.card ↥R0 = r := by
        rw [hR0def, card_map_of_injective (Subgroup.subtype_injective _), Nat.card_zpowers, hx]
      have hR0le : R0 ≤ A ⊓ centralizer ((K : Subgroup G) : Set G) := map_subtype_le _
      refine ⟨r, hr, hR0card ▸ Subgroup.card_dvd_of_le (hR0le.trans inf_le_left),
        R0, hR0le.trans inf_le_left, IsPGroup.of_card (n := 1) (by rw [pow_one, hR0card]),
        hR0le.trans inf_le_right, fun _ hb => hr.one_lt.ne ?_⟩
      rw [← hR0card, hb, Subgroup.card_bot]
  have hR0K : K ≤ normalizer ((R0 : Subgroup G) : Set G) :=
    (le_centralizer_iff.1 hR0C).trans (centralizer_le_normalizer _)
  have hrα : r ∈ alphaPrimes ↥M := hApf r hr hrA
  have hpr : p ≠ r := fun h => hpα (h ▸ hrα)
  have hqr : q ≠ r := fun h => hset.q_notMem_alpha (h ▸ hrα)
  have hR0π : IsPiNumber ({r} : Set ℕ) (Nat.card ↥R0) :=
    isPiSubgroup_iff_isPiNumber.1 ((isPiSubgroup_singleton_iff hr R0).2 hR0r)
  obtain ⟨R, hRA, hRhall, hR0R, hKR⟩ :=
    exists_isHallSubgroup_subgroupOf_ge_le_normalizer_of_le_normalizer hsolvAK hKA hAK
      ({r} : Set ℕ) hR0A hR0π hR0K
  have hRM : R ≤ M := hRA.trans hAM
  have hRr : IsPGroup r ↥R := by
    have h2 : IsPGroup r ↥(R.subgroupOf A) :=
      (isPiSubgroup_singleton_iff hr _).1 (isPiSubgroup_iff_isPiNumber.2 hRhall.natCard)
    exact h2.of_surjective (subgroupOfEquivOfLe hRA).toMonoidHom
      (subgroupOfEquivOfLe hRA).surjective
  have hRcard : Nat.card ↥R = r ^ (Nat.card ↥A).factorization r :=
    natCard_eq_pow_factorization_of_isHallSubgroup_singleton hr hRA hRhall
  have hAfac : (Nat.card ↥M).factorization r = (Nat.card ↥A).factorization r := by
    rw [hAcard]
    exact factorization_natCard_eq_of_isHallSubgroup
      (isHallSubgroup_alphaCore hna hodd hsolv hM) hr hrα
  have hRrank : 3 ≤ elementaryAbelianPRank r ↥R := by
    have h1 : Nat.card ↥(R.subgroupOf M) = r ^ (Nat.card ↥M).factorization r := by
      rw [natCard_subgroupOf_of_le' hRM, hRcard, hAfac]
    have h2 := elementaryAbelianPRank_eq_of_natCard_eq_pow_factorization hr h1
    rw [elementaryAbelianPRank_subgroupOf hr.one_lt hRM] at h2
    rw [h2]
    exact (mem_alphaPrimes.1 hrα).2
  have hrankP : elementaryAbelianPRank r ↥(R ⊓ centralizer ((P : Subgroup G) : Set G)) ≤ 1 :=
    le_trans (elementaryAbelianPRank_le_of_le hr.one_lt (inf_le_inf_right _ hRA)) (hrankbd r).1
  have hrankQ : elementaryAbelianPRank r ↥(R ⊓ centralizer ((Q : Subgroup G) : Set G)) ≤ 1 :=
    le_trans (elementaryAbelianPRank_le_of_le hr.one_lt (inf_le_inf_right _ hRA)) (hrankbd r).2
  have hRQ : ⁅R, Q⁆ ≠ ⊥ := by
    intro hb
    have hle : R ≤ R ⊓ centralizer ((Q : Subgroup G) : Set G) :=
      le_inf le_rfl (commutator_eq_bot_iff_le_centralizer.1 hb)
    have := elementaryAbelianPRank_le_of_le (X := G) hr.one_lt hle
    omega
  have hRne : R ≠ ⊥ := fun hb => hRQ (by rw [hb]; simp)
  set W : Subgroup G := R ⊔ K with hWdef
  have hRW : R ≤ W := le_sup_left
  have hKW : K ≤ W := le_sup_right
  have hQW : Q ≤ W := le_sup_left.trans hKW
  have hPW : P ≤ W := le_sup_right.trans hKW
  have hWM : W ≤ M := sup_le hRM hKM
  have hWsolv : Group.IsSolvable ↥W := isSolvable_of_le hWM
  have hRKdisj : R ⊓ K = ⊥ :=
    disjoint_iff.1 (disjoint_of_coprime_natCard
      (Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hRA) hAK))
  have hRnormal : (R.subgroupOf W).Normal :=
    normal_subgroupOf_of_le_normalizer hRW (sup_le le_normalizer hKR)
  have hWprod : ((R.subgroupOf W : Subgroup ↥W) : Set ↥W) *
      ((K.subgroupOf W : Subgroup ↥W) : Set ↥W) = Set.univ := by
    have h1 : (R.subgroupOf W ⊔ K.subgroupOf W : Subgroup ↥W) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hRW hKW, hWdef, Subgroup.subgroupOf_self]
    have h2 := Subgroup.normal_mul (N := R.subgroupOf W) (H := K.subgroupOf W)
    rw [h1, Subgroup.coe_top] at h2
    exact h2.symm
  have hQPsub : (Q.subgroupOf W ⊔ P.subgroupOf W : Subgroup ↥W) = K.subgroupOf W :=
    (Subgroup.subgroupOf_sup hQW hPW).symm
  have hoddW : Odd (Nat.card ↥W) := hodd.of_dvd_nat (W : Subgroup G).card_subgroup_dvd_card
  have hoddp : Odd p := hoddW.of_dvd_nat (hPcard ▸ Subgroup.card_dvd_of_le hPW)
  have hoddq : Odd q := by
    have := Fact.mk hq
    obtain ⟨n, hn⟩ := hset.isPGroup_Q.exists_card_eq
    have hn0 : n ≠ 0 := fun h0 =>
      hset.Q_ne_bot (Subgroup.card_eq_one.1 (by rw [hn, h0, pow_zero]))
    exact hoddW.of_dvd_nat
      ((hn ▸ dvd_pow_self q hn0 : q ∣ Nat.card ↥Q).trans (Subgroup.card_dvd_of_le hQW))
  have hoddr : Odd r := by
    have := Fact.mk hr
    obtain ⟨n, hn⟩ := hRr.exists_card_eq
    have hn0 : n ≠ 0 := fun h0 => hRne (Subgroup.card_eq_one.1 (by rw [hn, h0, pow_zero]))
    exact hoddW.of_dvd_nat
      ((hn ▸ dvd_pow_self r hn0 : r ∣ Nat.card ↥R).trans (Subgroup.card_dvd_of_le hRW))
  have hsetup : IsCriticalRegularComplementSetup p q r (R.subgroupOf W) (Q.subgroupOf W)
      (P.subgroupOf W) :=
    { prime_p := hp
      prime_q := hq
      prime_r := hr
      odd_p := hoddp
      odd_q := hoddq
      odd_r := hoddr
      p_ne_q := Ne.symm hset.q_ne
      p_ne_r := hpr
      q_ne_r := hqr
      normal_R := hRnormal
      coe_mul_coe := by rw [hQPsub]; exact hWprod
      disjoint_R := by
        rw [hQPsub, inf_subgroupOf_eq_subgroupOf_inf, hRKdisj, Subgroup.bot_subgroupOf]
      normal_Q := by
        refine normal_subgroupOf_of_le_normalizer (by rw [hQPsub]; exact comap_mono le_sup_left) ?_
        rw [hQPsub, ← hQPsub]
        exact sup_le le_normalizer (le_normalizer_subgroupOf hset.normalized)
      disjoint_Q := by
        rw [inf_subgroupOf_eq_subgroupOf_inf, hQP, Subgroup.bot_subgroupOf]
      isPGroup_R := isPGroup_subgroupOf hRW hRr
      isPGroup_Q := isPGroup_subgroupOf hQW hset.isPGroup_Q
      ne_bot_Q := fun hb => hset.Q_ne_bot (eq_bot_of_subgroupOf_eq_bot' hQW hb)
      natCard_P := by rw [natCard_subgroupOf_of_le' hPW, hPcard]
      inf_centralizer_Q := by
        rw [centralizer_subgroupOf_of_le hPW, inf_subgroupOf_eq_subgroupOf_inf,
          hset.centralizer_eq, Subgroup.bot_subgroupOf]
      commutator_R_Q := by
        intro hb
        refine hRQ ?_
        have h2 := congrArg (Subgroup.map W.subtype) hb
        rwa [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
          Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hRW, inf_eq_left.2 hQW,
          Subgroup.map_bot] at h2
      rank_centralizer_P := by
        rw [centralizer_subgroupOf_of_le hPW, inf_subgroupOf_eq_subgroupOf_inf,
          elementaryAbelianPRank_subgroupOf hr.one_lt
            (le_trans inf_le_left hRW : R ⊓ centralizer ((P : Subgroup G) : Set G) ≤ W)]
        exact hrankP
      rank_centralizer_Q := by
        rw [centralizer_subgroupOf_of_le hQW, inf_subgroupOf_eq_subgroupOf_inf,
          elementaryAbelianPRank_subgroupOf hr.one_lt
            (le_trans inf_le_left hRW : R ⊓ centralizer ((Q : Subgroup G) : Set G) ≤ W)]
        exact hrankQ }
  obtain ⟨hconc1, hconc2⟩ := critical_regular_complement_common_fixed_points hsetup
  have hCRP : R ⊓ centralizer ((P : Subgroup G) : Set G) ≠ ⊥ := by
    intro hb
    refine hconc1 ?_
    rw [centralizer_subgroupOf_of_le hPW, inf_subgroupOf_eq_subgroupOf_inf, hb,
      Subgroup.bot_subgroupOf]
  have hCRK : R ⊓ centralizer ((K : Subgroup G) : Set G) = ⊥ := by
    refine eq_bot_of_subgroupOf_eq_bot'
      (le_trans inf_le_left hRW : R ⊓ centralizer ((K : Subgroup G) : Set G) ≤ W) ?_
    rw [← inf_subgroupOf_eq_subgroupOf_inf, ← centralizer_subgroupOf_of_le hKW, ← hQPsub]
    exact hconc2
  refine ⟨fun hb => hCRP (le_bot_iff.1 (hb ▸ inf_le_inf_right _ hRA)), ?_⟩
  by_contra hfix
  exact hR0seed hfix (le_bot_iff.1 (hCRK ▸ le_inf hR0R hR0C))

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open CFSG.FeitThompson

universe u

theorem FTS_regular_tau_one_alpha_fixed_points :
    Statements.FTS_regular_tau_one_alpha_fixed_points.{u} := by
  intro G _ _ hG _M _P _Q _p _q hset hAne
  have := hG.isSimpleGroup
  exact inf_alphaCoreOf_centralizer_fixed_points hG.not_isMulCommutative hG.odd_natCard
    hG.isSolvable_of_ne_top hset hAne

end

end CFSG.FeitThompson.Proofs
