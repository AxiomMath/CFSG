module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.SigmaComplementThreeHallFactors
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.UniqueMaximalOvergroupCentralizerTauOneThree
import CFSG.FeitThompson.Local.SigmaComplementPlaneActionSupport
import CFSG.FeitThompson.Local.TypeINonfrobeniusWitness
import CFSG.FeitThompson.Local.SigmaConjugateIntersectionCyclic
import CFSG.FeitThompson.Local.OutsideSigmaNormalizerRankTwoPlane
import CFSG.FeitThompson.Local.FrattiniCommutingProductPrimePower
import CFSG.FeitThompson.OddOrder.FittingSplitsOverHallCore
import CFSG.FeitThompson.Local.LargestPrimeCharacteristicSylow
import CFSG.FeitThompson.Local.MaximalPlaneDerivedNormalComplement
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup
open CFSG.FeitThompson.Prep05 (centralizerIn IsPPlane)
open CFSG.FeitThompson.Prep09 (IsMinimalSimpleOddOrder)

universe u

variable {G : Type u} [Group G]

theorem exists_sigmaComplement_ge [Finite G] {L U : Subgroup G} [Group.IsSolvable ↥L]
    (hHall : IsHallPiSubgroup (sigmaPrimes L) ((sigmaCore L).subgroupOf L))
    (hUL : U ≤ L) (hU : IsPiSubgroup ((sigmaPrimes L)ᶜ) (U.subgroupOf L)) :
    ∃ F : Subgroup G, U ≤ F ∧ F ≤ L ∧
      FreeCore.IsInternalSemidirectProduct L (sigmaCore L) F := by
  set s : Subgroup ↥L := (sigmaCore L).subgroupOf L with hs
  have hsmap : s.map L.subtype = sigmaCore L := Subgroup.map_subgroupOf_eq_of_le (sigmaCore_le L)
  obtain ⟨T, hT, hUT⟩ := exists_isHallSubgroup_ge_of_isPiSubgroup hU
  have hscard : IsPiNumber (sigmaPrimes L) (Nat.card ↥s) :=
    isPiSubgroup_iff_isPiNumber.1 hHall.isPiSubgroup
  have hsindex : IsPiNumber ((sigmaPrimes L)ᶜ) s.index :=
    isPiNumber_iff.2 fun p hp => hHall.notMem_of_mem_primeFactors_index p hp
  have hcop1 : (Nat.card ↥s).Coprime (Nat.card ↥T) :=
    hscard.coprime_of_compl hT.natCard Nat.card_pos.ne' Nat.card_pos.ne'
  have hcop2 : s.index.Coprime T.index :=
    hsindex.coprime_of_compl (by simpa using hT.index) Subgroup.index_ne_zero_of_finite
      Subgroup.index_ne_zero_of_finite
  have hprod : Nat.card ↥T * T.index = Nat.card ↥s * s.index := by
    rw [Subgroup.card_mul_index, Subgroup.card_mul_index]
  have hTeq : Nat.card ↥T = s.index :=
    Nat.dvd_antisymm (hcop1.symm.dvd_of_dvd_mul_left ⟨T.index, hprod.symm⟩)
      (hcop2.dvd_of_dvd_mul_right ⟨Nat.card ↥s, by rw [hprod, Nat.mul_comm]⟩)
  have hcardprod : Nat.card ↥s * Nat.card ↥T = Nat.card ↥L := by
    rw [hTeq]; exact Subgroup.card_mul_index s
  have hdisj : Disjoint s T := Subgroup.disjoint_of_coprime_natCard hcop1
  have hsup : s ⊔ T = ⊤ :=
    (Subgroup.isComplement'_of_card_mul_and_disjoint hcardprod hdisj).sup_eq_top
  refine ⟨T.map L.subtype, ?_, Subgroup.map_subtype_le _, ?_, le_normalizer_sigmaCore L, ?_⟩
  · have h := Subgroup.map_mono (f := L.subtype) hUT
    rwa [Subgroup.map_subgroupOf_eq_of_le hUL] at h
  · calc sigmaCore L ⊔ T.map L.subtype = (s ⊔ T).map L.subtype := by
          rw [Subgroup.map_sup, hsmap]
      _ = L := by rw [hsup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  · rw [disjoint_iff, ← hsmap, ← Subgroup.map_inf _ _ _ L.subtype_injective,
      disjoint_iff.1 hdisj, Subgroup.map_bot]

theorem isElementaryAbelianPlane_of_isPPlane {p : ℕ} (hp : p.Prime) {A : Subgroup G}
    (h : IsPPlane p A) : _root_.CFSG.FeitThompson.IsElementaryAbelianPlane p A :=
  nonempty_mulEquiv_pi_of_isElementaryAbelian hp
    (isElementaryAbelian_iff_isElementaryAbelianSubgroup.2 h.1) h.2

theorem eq_of_le_of_le_of_ne_of_isPPlane [Finite G] {p : ℕ} (hp : p.Prime) {A P C : Subgroup G}
    (hA : IsPPlane p A) (hPcard : Nat.card ↥P = p) (hPC : P ≤ C) (hCA : C ≤ A) (hne : C ≠ A) :
    C = P := by
  have hdvd : Nat.card ↥C ∣ p ^ 2 := hA.2 ▸ Subgroup.card_dvd_of_le hCA
  have hpdvd : p ∣ Nat.card ↥C := hPcard ▸ Subgroup.card_dvd_of_le hPC
  have hCcard : Nat.card ↥C = p := by
    rcases (Nat.dvd_prime_pow hp).1 hdvd with ⟨k, hk, hkC⟩
    interval_cases k
    · rw [pow_zero] at hkC
      rw [hkC] at hpdvd
      exact absurd (Nat.dvd_one.1 hpdvd) hp.ne_one
    · simpa using hkC
    · exact absurd (Subgroup.eq_of_le_of_card_ge hCA (by rw [hA.2, hkC])) hne
  exact (Subgroup.eq_of_le_of_card_ge hPC (by rw [hCcard, hPcard])).symm

theorem inf_eq_bot_of_natCard_eq_prime [Finite G] {p : ℕ} (hp : p.Prime) {Q K : Subgroup G}
    (hQ : Nat.card ↥Q = p) (h : ¬ Q ≤ K) : Q ⊓ K = ⊥ := by
  have hdvd : Nat.card ↥(Q ⊓ K) ∣ p := hQ ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
  · exact Subgroup.card_eq_one.1 h1
  · exact absurd ((Subgroup.eq_of_le_of_card_ge (inf_le_left (b := K)) (by rw [hQ, h1])) ▸
      (inf_le_right : Q ⊓ K ≤ K)) h

theorem FNI_tau13_nonsigma_normalizer_reflected_plane
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_hall_abelian.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_tau12_fixed_plane_line_core_free.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FNI_tau13_nonfree_third_factor_structure.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_sigma_prime_separation.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_fixed_line_centralizer_unique.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_three_prime_normalizer_transfer.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_tau13_nonsigma_normalizer_reflected_plane.{u} := by
  intro G _ _ hG M E hME p hp P hPE hPcard hcent L hL hNPL hpL
  have : Fintype G := Fintype.ofFinite G
  have : IsSimpleGroup G := hG.isSimpleGroup
  have hG2 : _root_.CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG4 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG9 : IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hM : IsCoatom M := hME.isCoatom
  have hsdM := hME.semidirect
  have hEM : E ≤ M := hsdM.right_le
  have hpprime : p.Prime := by
    rcases hp with h | h
    · exact prime_of_mem_tau1Primes h
    · exact prime_of_mem_tau3Primes h
  have hPne : P ≠ ⊥ :=
    (Subgroup.one_lt_card_iff_ne_bot P).1 (by rw [hPcard]; exact hpprime.one_lt)
  have hpM : p ∉ sigmaPrimes M := by
    rcases hp with h | h
    · exact notMem_sigmaPrimes_of_mem_tau1Primes h
    · exact notMem_sigmaPrimes_of_mem_tau3Primes h
  have hrankM : elementaryAbelianPRank p ↥M = 1 := by
    rcases hp with h | h
    · exact elementaryAbelianPRank_eq_one_of_mem_tau1Primes h
    · exact elementaryAbelianPRank_eq_one_of_mem_tau3Primes h
  have hrankL : elementaryAbelianPRank p ↥L = 2 :=
    elementaryAbelianPRank_eq_two_of_notMem_sigmaPrimes hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hL hpprime hpL hPcard hNPL
  have hptau2 : p ∈ tauTwoPrimes L := mem_tauTwoPrimes_iff.2 ⟨hpprime, hpL, hrankL⟩
  refine ⟨?_, hptau2⟩
  have hnoncon := (h₉ G hG9 M hM E hEM hsdM p hp P (hPE.trans hEM) hPcard L hL hNPL).1
  have hCnt : Nontrivial ↥(centralizerIn (sigmaCore M) P) :=
    (Subgroup.nontrivial_iff_ne_bot _).2 hcent
  obtain ⟨q, hqmem⟩ := primeFactors_natCard_nonempty ↥(centralizerIn (sigmaCore M) P)
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hqmem
  obtain ⟨y, hyC, hyord⟩ :=
    exists_mem_orderOf_eq_of_dvd (H := centralizerIn (sigmaCore M) P) hq
      (Nat.dvd_of_mem_primeFactors hqmem)
  set Q : Subgroup G := zpowers y with hQdef
  have hQcard : Nat.card ↥Q = q := by rw [hQdef, Nat.card_zpowers, hyord]
  have hQC : Q ≤ centralizerIn (sigmaCore M) P := by rw [hQdef, zpowers_le]; exact hyC
  have hQS : Q ≤ sigmaCore M := hQC.trans inf_le_left
  have hQcentP : Q ≤ centralizer (P : Set G) := hQC.trans inf_le_right
  have hQne : Q ≠ ⊥ :=
    (Subgroup.one_lt_card_iff_ne_bot Q).1 (by rw [hQcard]; exact hq.one_lt)
  have hqM : q ∈ sigmaPrimes M :=
    mem_sigmaPrimes_of_isPGroup_le_sigmaCore hq hQne
      (IsPGroup.of_card (n := 1) (by rw [pow_one, hQcard])) hQS
  have hsep : sigmaPrimes M ∩ sigmaPrimes L = ∅ := h₇ G hG9 M L hM hL hnoncon
  have hqL : q ∉ sigmaPrimes L := fun h => by
    have : q ∈ sigmaPrimes M ∩ sigmaPrimes L := ⟨hqM, h⟩
    rw [hsep] at this
    exact this
  have hpq : p ≠ q := fun h => hpM (h ▸ hqM)
  have hPcentQ : P ≤ centralizer (Q : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm,
      Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hQcentP
  have hcommPQ : ∀ x ∈ P, ∀ z ∈ Q, Commute x z := fun _ hx z hz =>
    (Subgroup.mem_centralizer_iff.1 (hPcentQ hx) z hz).symm
  have hPL : P ≤ L := Subgroup.le_normalizer.trans hNPL
  have hQL : Q ≤ L :=
    hQcentP.trans ((Subgroup.centralizer_le_normalizer (P : Set G)).trans hNPL)
  have hPQL : P ⊔ Q ≤ L := sup_le hPL hQL
  have hinfPQ : P ⊓ Q = ⊥ := by
    have hdvdp : Nat.card ↥(P ⊓ Q) ∣ p := hPcard ▸ Subgroup.card_dvd_of_le inf_le_left
    have hdvdq : Nat.card ↥(P ⊓ Q) ∣ q := hQcard ▸ Subgroup.card_dvd_of_le inf_le_right
    exact Subgroup.card_eq_one.1
      (Nat.eq_one_of_dvd_coprimes ((Nat.coprime_primes hpprime hq).2 hpq) hdvdp hdvdq)
  have hcardPQ : Nat.card ↥(P ⊔ Q) = p * q := by
    have h := natCard_sup_mul_natCard_inf_of_commute hcommPQ
    rw [hinfPQ, Subgroup.card_bot, mul_one, hPcard, hQcard] at h
    exact h
  have hsolvL : Group.IsSolvable ↥L := hG.isSolvable_of_ne_top L hL.1
  obtain ⟨hHallL, -, -⟩ := h₁ G hG2 L hL
  obtain ⟨F, hPQF, hFL, hsdF⟩ :=
    exists_sigmaComplement_ge (L := L) (U := P ⊔ Q) hHallL.2 hPQL (by
      rw [isPiSubgroup_iff, natCard_subgroupOf hPQL, hcardPQ]
      intro r hr
      rw [Nat.primeFactors_mul hpprime.ne_zero hq.ne_zero, Finset.mem_union,
        hpprime.primeFactors, hq.primeFactors] at hr
      rcases hr with hr | hr
      · rw [Finset.mem_singleton] at hr; exact hr ▸ hpL
      · rw [Finset.mem_singleton] at hr; exact hr ▸ hqL)
  have hPF : P ≤ F := le_sup_left.trans hPQF
  have hQF : Q ≤ F := le_sup_right.trans hPQF
  have hsigF : _root_.CFSG.FeitThompson.IsSigmaComplement L F := ⟨hL, hsdF⟩
  have hsigF05 : CFSG.FeitThompson.Prep05.IsSigmaComplement L F :=
    ⟨hL, hsdF⟩
  obtain ⟨-, hranks, -⟩ := FNI_sigma_complement_prime_data h₁ G hG4 L F hsigF
  have hpF : p ∈ _root_.CFSG.FeitThompson.primeDivisorsOf ↥F :=
    ⟨hpprime, hPcard ▸ Subgroup.card_dvd_of_le hPF⟩
  have hrankF : elementaryAbelianPRank p ↥F = 2 := by
    rw [(hranks p hpF).1, hrankL]
  obtain ⟨A, hAF, hAplane⟩ := exists_isPPlane_le hpprime hrankF
  have hAL : A ≤ L := hAF.trans hFL
  have hAplane04 : _root_.CFSG.FeitThompson.IsElementaryAbelianPlane p A :=
    isElementaryAbelianPlane_of_isPPlane hpprime hAplane
  have hOut : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane p L A :=
    ⟨hL, hpprime, hpL, hAL, hAplane04⟩
  have hPA : P ≤ A := (h₃ G hG4 p L A F hOut hsigF hAF).2.1 P hPF hPcard
  have hCQM : centralizer (Q : Set G) ≤ M :=
    (FNI_tau13_nonregular_core_line_unique h₁ h₆ h₈ G hG M E hME p hp P hPE hPcard hcent q hq Q
      hQC hQcard).le
  have hQnotcent : ¬ Q ≤ centralizer (A : Set G) := by
    intro hQA
    have hAcentQ : A ≤ centralizer (Q : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm,
        Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hQA
    have hAM : A ≤ M := hAcentQ.trans hCQM
    have h2 : 2 ≤ elementaryAbelianPRank p ↥M :=
      IsElementaryAbelian.le_elementaryAbelianPRank hpprime
        (isElementaryAbelian_iff_isElementaryAbelianSubgroup.2 hAplane.1) hAplane.2 hAM
    rw [hrankM] at h2
    omega
  have hcomm : ⁅A, Q⁆ ≠ ⊥ := by
    rw [Ne, Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hQnotcent
  have hPCA : P ≤ centralizerIn A Q := le_inf hPA hPcentQ
  have hCAeq : centralizerIn A Q = P := by
    refine eq_of_le_of_le_of_ne_of_isPPlane hpprime hAplane hPcard hPCA inf_le_left ?_
    intro h
    exact hQnotcent (by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm,
        Subgroup.commutator_eq_bot_iff_le_centralizer]
      have : A ≤ centralizer (Q : Set G) := h ▸ (inf_le_right : centralizerIn A Q ≤ _)
      exact this)
  obtain ⟨F₁, F₂, F₃, hsplit, -⟩ := FNI_sigma_complement_three_factors h₁ G hG4 L F hsigF
  obtain ⟨-, hnormal, hprimes⟩ :=
    FBG_sigma_complement_plane_action_support h₂ h₃ h₄ G hG2 L hL p hpprime hpL A hAL hAplane04
      F hsdF hAF F₁ F₂ F₃ ⟨hsplit.le_E₁, hsplit.isHall_E₁⟩ ⟨hsplit.le_E₂, hsplit.isHall_E₂⟩
      ⟨hsplit.le_E₃, hsplit.isHall_E₃⟩ hsplit.outer hsplit.inner
  have hqtau1 : q ∈ tau1Primes L := by
    refine hprimes q (Nat.mem_primeFactors.2 ⟨hq, ?_, Subgroup.index_ne_zero_of_finite⟩)
    have hQA : Q ⊓ centralizer (A : Set G) = ⊥ :=
      inf_eq_bot_of_natCard_eq_prime hq hQcard hQnotcent
    have hinf : F ⊓ centralizer (A : Set G) ⊓ Q = ⊥ :=
      le_bot_iff.1 (le_trans (le_inf inf_le_right (inf_le_left.trans inf_le_right)) hQA.le)
    have hdisj : Disjoint ((F ⊓ centralizer (A : Set G)).subgroupOf F) (Q.subgroupOf F) := by
      rw [disjoint_iff, Subgroup.subgroupOf, Subgroup.subgroupOf, ← Subgroup.comap_inf, hinf]
      simp
    have := hnormal
    have hdvd := natCard_dvd_index_of_disjoint ((F ⊓ centralizer (A : Set G)).subgroupOf F)
      (Q.subgroupOf F) hdisj
    rwa [natCard_subgroupOf hQF, hQcard] at hdvd
  have hACQne : A ⊓ centralizer (Q : Set G) ≠ ⊥ := by
    intro h
    exact hPne (le_bot_iff.1 (h ▸ hPCA))
  have hSLQ : centralizerIn (sigmaCore L) Q = ⊥ :=
    h₅ G hG4 q p L F Q A hsigF hqtau1 hQF hQcard hptau2 hAF hAplane04 hACQne
  exact ⟨F, hsigF05, q, hqtau1, Q, hQF, hQcard, A, hAF, hAplane, hPA, hCAeq, hcomm, hSLQ⟩

end

end CFSG.FeitThompson.Proofs
