module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
import CFSG.FeitThompson.Local.CoreCentralizerTypeIIIOrIVDerived
import CFSG.FeitThompson.Local.LowRankFittingDerivedNilpotent
import CFSG.FeitThompson.Local.PComplementQuotientSylowRank
import CFSG.FeitThompson.Local.CriticalSubgroupFixedLine
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Topology.Sheaves.Presheaf

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup Pointwise

universe u

variable {G : Type u} [Group G] {q : ℕ}

theorem index_subgroupOf_left_eq [Finite G] {M A B : Subgroup G}
    (h : FreeCore.IsInternalSemidirectProduct M A B) :
    (A.subgroupOf M).index = Nat.card ↥B := by
  have h1 : Nat.card ↥(A.subgroupOf M) * (A.subgroupOf M).index = Nat.card ↥M :=
    Subgroup.card_mul_index _
  have h2 : Nat.card ↥(A.subgroupOf M) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.left_le).toEquiv
  rw [h2, h.natCard_eq_mul] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1

theorem elementaryAbelianPRank_eq_of_le_of_factorization_eq [Finite G] (hq : q.Prime)
    {K M : Subgroup G} (hKM : K ≤ M)
    (hfac : (Nat.card ↥K).factorization q = (Nat.card ↥M).factorization q) :
    elementaryAbelianPRank q ↥K = elementaryAbelianPRank q ↥M := by
  have hfq := Fact.mk hq
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow q ↥K))
  set P' : Subgroup G := (P : Subgroup ↥K).map K.subtype with hP'
  have hcardP : Nat.card ↥(P : Subgroup ↥K) = q ^ (Nat.card ↥K).factorization q :=
    P.card_eq_multiplicity
  have hcardP' : Nat.card ↥P' = q ^ (Nat.card ↥K).factorization q := by
    rw [hP', Subgroup.card_subtype, hcardP]
  have hP'K : P' ≤ K := Subgroup.map_subtype_le _
  have h1 : elementaryAbelianPRank q ↥(P : Subgroup ↥K) = elementaryAbelianPRank q ↥K :=
    elementaryAbelianPRank_eq_of_natCard_eq_pow_factorization hq hcardP
  have h2 : elementaryAbelianPRank q ↥(P'.subgroupOf M) = elementaryAbelianPRank q ↥M := by
    refine elementaryAbelianPRank_eq_of_natCard_eq_pow_factorization hq ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hP'K.trans hKM)).toEquiv, hcardP', hfac]
  have h3 : elementaryAbelianPRank q ↥(P'.subgroupOf M) = elementaryAbelianPRank q ↥P' :=
    elementaryAbelianPRank_eq_of_mulEquiv hq.one_lt
      (Subgroup.subgroupOfEquivOfLe (hP'K.trans hKM))
  have h4 : elementaryAbelianPRank q ↥P' = elementaryAbelianPRank q ↥(P : Subgroup ↥K) :=
    (elementaryAbelianPRank_eq_of_mulEquiv hq.one_lt
      ((P : Subgroup ↥K).equivMapOfInjective K.subtype K.subtype_injective)).symm
  rw [← h1, ← h4, ← h3, h2]

theorem isCyclic_sylow_iff_elementaryAbelianPRank_le_one {X : Type*} [Group X] [Finite X]
    (hq : q.Prime) (hodd : Odd q) (P : Sylow q X) :
    IsCyclic ↥(P : Subgroup X) ↔ elementaryAbelianPRank q X ≤ 1 := by
  have hfq := Fact.mk hq
  have hPrank : elementaryAbelianPRank q ↥(P : Subgroup X) = elementaryAbelianPRank q X :=
    elementaryAbelianPRank_eq_of_natCard_eq_pow_factorization hq P.card_eq_multiplicity
  rw [← hPrank]
  refine ⟨fun hc => ?_, fun h => isCyclic_of_elementaryAbelianPRank_le_one hq hodd P.isPGroup' h⟩
  by_contra h
  obtain ⟨A, hcomm, hexp, hcard⟩ := (mem_elementaryAbelianRanks_iff_exists_subgroup hq
    (X := ↥(P : Subgroup X)) (d := 2)).1
    ((le_elementaryAbelianPRank_iff hq.one_lt).1 (show 2 ≤ _ by omega))
  exact not_isCyclic_of_isElementaryAbelian_of_natCard_eq_pow hq
    (isElementaryAbelian_iff.2 ⟨hcomm, hexp⟩) hcard le_rfl hc

theorem forall_isCyclic_sylow_iff {X : Type*} [Group X] [Finite X] (hq : q.Prime) (hodd : Odd q) :
    (∀ P : Sylow q X, IsCyclic ↥(P : Subgroup X)) ↔ elementaryAbelianPRank q X ≤ 1 := by
  refine ⟨fun h => ?_, fun h P => (isCyclic_sylow_iff_elementaryAbelianPRank_le_one hq hodd P).2 h⟩
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow q X))
  exact (isCyclic_sylow_iff_elementaryAbelianPRank_le_one hq hodd P).1 (h P)

theorem forall_not_isCyclic_sylow_iff {X : Type*} [Group X] [Finite X] (hq : q.Prime)
    (hodd : Odd q) :
    (∀ P : Sylow q X, ¬ IsCyclic ↥(P : Subgroup X)) ↔ 2 ≤ elementaryAbelianPRank q X := by
  refine ⟨fun h => ?_, fun h P hc => ?_⟩
  · obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow q X))
    by_contra hcon
    exact h P ((isCyclic_sylow_iff_elementaryAbelianPRank_le_one hq hodd P).2 (by omega))
  · have := (isCyclic_sylow_iff_elementaryAbelianPRank_le_one hq hodd P).1 hc
    omega

theorem FNI_sigma_complement_prime_data
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u}) :
    Statements.FNI_sigma_complement_prime_data.{u} := by
  intro G _ _ hG M E hME
  obtain ⟨hM, hsd⟩ := hME
  have hsimple := hG.isSimpleGroup
  let _ : Fintype G := Fintype.ofFinite G
  obtain ⟨hHallOf, hHallG, hSle⟩ := h₁ G
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩ M hM
  have hEM : E ≤ M := hsd.right_le
  have hSM : sigmaCore M ≤ M := hsd.left_le
  have hcard : Nat.card ↥M = Nat.card ↥(sigmaCore M) * Nat.card ↥E := hsd.natCard_eq_mul
  have hS1 : ∀ r ∈ (Nat.card ↥(sigmaCore M)).primeFactors, r ∈ sigmaPrimes M :=
    isPiSubgroup_iff.1 hHallG.isPiSubgroup
  have hS2 : ∀ r ∈ (Nat.card ↥E).primeFactors, r ∉ sigmaPrimes M := by
    rw [← index_subgroupOf_left_eq hsd]
    exact hHallOf.2.notMem_of_mem_primeFactors_index
  have hnotdvdS : ∀ r : ℕ, r.Prime → r ∉ sigmaPrimes M → ¬ r ∣ Nat.card ↥(sigmaCore M) :=
    fun r hr hrσ hd => hrσ (hS1 r (Nat.mem_primeFactors.2 ⟨hr, hd, Nat.card_pos.ne'⟩))
  have hπE : ∀ r : ℕ, r.Prime → (r ∣ Nat.card ↥E ↔ r ∣ Nat.card ↥M ∧ r ∉ sigmaPrimes M) := by
    intro r hr
    refine ⟨fun hd => ⟨hcard ▸ hd.mul_left _,
      hS2 r (Nat.mem_primeFactors.2 ⟨hr, hd, Nat.card_pos.ne'⟩)⟩, ?_⟩
    rintro ⟨hd, hσ⟩
    rw [hcard] at hd
    rcases (Nat.Prime.dvd_mul hr).1 hd with h | h
    · exact absurd h (hnotdvdS r hr hσ)
    · exact h
  have hpart1 : primeDivisorsOf ↥E = primeDivisorsOf ↥M \ sigmaPrimes M := by
    ext r
    simp only [Set.mem_sdiff, mem_primeDivisorsOf]
    constructor
    · intro h
      obtain ⟨hdM, hσ⟩ := (hπE r h.1).1 h.2
      exact ⟨⟨h.1, hdM⟩, hσ⟩
    · rintro ⟨⟨hr, hd⟩, hσ⟩
      exact ⟨hr, (hπE r hr).2 ⟨hd, hσ⟩⟩
  have hoddG := hG.odd_natCard
  have hoddprime : ∀ r : ℕ, r ∣ Nat.card ↥M → Odd r :=
    fun r hd => Odd.of_dvd_nat hoddG (hd.trans M.card_subgroup_dvd_card)
  have hrank : ∀ r : ℕ, r.Prime → r ∣ Nat.card ↥E →
      elementaryAbelianPRank r ↥E = elementaryAbelianPRank r ↥M ∧
        elementaryAbelianPRank r ↥M ≤ 2 := by
    intro r hr hd
    obtain ⟨hdM, hrσ⟩ := (hπE r hr).1 hd
    have hfac : (Nat.card ↥E).factorization r = (Nat.card ↥M).factorization r := by
      rw [hcard, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (hnotdvdS r hr hrσ), zero_add]
    refine ⟨elementaryAbelianPRank_eq_of_le_of_factorization_eq hr hEM hfac, ?_⟩
    by_contra h3
    exact hrσ (alphaPrimes_subset_sigmaPrimes hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hM (mem_alphaPrimes.2 ⟨hr, by omega⟩))
  have hEnormS : (⁅E, E⁆ : Subgroup G) ≤ normalizer ((sigmaCore M : Subgroup G) : Set G) :=
    ((Subgroup.commutator_le_self E).trans hEM).trans hsd.le_normalizer
  have hderived : (⁅M, M⁆ : Subgroup G) = sigmaCore M ⊔ ⁅E, E⁆ :=
    le_antisymm (commutator_le_sup_commutator_of_sup hSM hEM hsd.sup_eq hsd.le_normalizer)
      (sup_le hSle (Subgroup.commutator_mono hEM hEM))
  have hpart3 : ((⁅M, M⁆ : Subgroup G) : Set G) =
      (sigmaCore M : Set G) * ((⁅E, E⁆ : Subgroup G) : Set G) := by
    rw [hderived, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hEnormS]
  have hpart4 : (⁅M, M⁆ : Subgroup G) ⊓ E = ⁅E, E⁆ := by
    rw [hderived, inf_comm]
    exact inf_sup_eq_of_disjoint_of_le_normalizer hsd.disjoint
      (Subgroup.commutator_le_self E) hEnormS
  have hcardDerived : Nat.card ↥(⁅M, M⁆ : Subgroup G) =
      Nat.card ↥(sigmaCore M) * Nat.card ↥(⁅E, E⁆ : Subgroup G) := by
    rw [hderived]
    exact natCard_sup_of_le_normalizer hEnormS
      (hsd.disjoint.mono_right (Subgroup.commutator_le_self E))
  have hdvdDerived : ∀ r : ℕ, r.Prime → r ∉ sigmaPrimes M →
      (r ∣ Nat.card ↥(⁅M, M⁆ : Subgroup G) ↔ r ∣ Nat.card ↥(⁅E, E⁆ : Subgroup G)) := by
    intro r hr hrσ
    rw [hcardDerived]
    refine ⟨fun hd => ?_, fun hd => hd.mul_left _⟩
    rcases (Nat.Prime.dvd_mul hr).1 hd with h | h
    · exact absurd h (hnotdvdS r hr hrσ)
    · exact h
  have hEne : E ≠ ⊤ := fun h => hM.1 (top_le_iff.1 (h ▸ hEM))
  have hEsolv : Group.IsSolvable ↥E := hG.isSolvable_of_ne_top E hEne
  have hoddE : Odd (Nat.card ↥E) := Odd.of_dvd_nat hoddG E.card_subgroup_dvd_card
  have hpart5 : Group.IsNilpotent ↥(⁅E, E⁆ : Subgroup G) := by
    have hrankF : ∀ r : ℕ, r.Prime → elementaryAbelianPRank r ↥(fittingRaw ↥E) ≤ 2 := by
      intro r hr
      refine le_trans (elementaryAbelianPRank_subgroup_le hr.one_lt _) ?_
      by_cases hd : r ∣ Nat.card ↥E
      · exact ((hrank r hr hd).1).le.trans (hrank r hr hd).2
      · rw [(elementaryAbelianPRank_eq_zero_iff hr).2 hd]
        omega
    have hnil := isNilpotent_commutator (G := ↥E) hoddE hrankF
    have e := (_root_.commutator ↥E).equivMapOfInjective E.subtype E.subtype_injective
    rw [Subgroup.map_subtype_commutator] at e
    exact Group.nilpotent_of_mulEquiv e
  have hcommE : Nat.card (_root_.commutator ↥E) = Nat.card ↥(⁅E, E⁆ : Subgroup G) :=
    natCard_commutator_subtype E
  have hpart6₂ : piTwoPrimes' ↥E = tauTwoPrimes M := by
    ext r
    simp only [piTwoPrimes', Set.mem_ofPred_eq, mem_primeDivisorsOf, mem_tauTwoPrimes_iff]
    constructor
    · rintro ⟨⟨hr, hd⟩, hcyc⟩
      obtain ⟨hdM, hrσ⟩ := (hπE r hr).1 hd
      have h2 := (forall_not_isCyclic_sylow_iff hr (hoddprime r hdM)).1 hcyc
      obtain ⟨he, hle⟩ := hrank r hr hd
      exact ⟨hr, hrσ, by omega⟩
    · rintro ⟨hr, hrσ, hr2⟩
      have hdM : r ∣ Nat.card ↥M := (one_le_elementaryAbelianPRank_iff hr).1 (by omega)
      have hd : r ∣ Nat.card ↥E := (hπE r hr).2 ⟨hdM, hrσ⟩
      obtain ⟨he, -⟩ := hrank r hr hd
      exact ⟨⟨hr, hd⟩, (forall_not_isCyclic_sylow_iff hr (hoddprime r hdM)).2 (by omega)⟩
  have hpart6₁ : piOnePrimes' ↥E = tau1Primes M := by
    ext r
    simp only [piOnePrimes', Set.mem_ofPred_eq, mem_primeDivisorsOf, mem_tau1Primes_iff]
    constructor
    · rintro ⟨⟨hr, hd⟩, hcyc, hnd⟩
      obtain ⟨hdM, hrσ⟩ := (hπE r hr).1 hd
      have h1 := (forall_isCyclic_sylow_iff hr (hoddprime r hdM)).1 hcyc
      obtain ⟨he, -⟩ := hrank r hr hd
      have hr1 : 1 ≤ elementaryAbelianPRank r ↥E :=
        (one_le_elementaryAbelianPRank_iff hr).2 hd
      refine ⟨hr, hdM, hrσ, by omega, ?_⟩
      rw [hdvdDerived r hr hrσ, ← hcommE]
      exact hnd
    · rintro ⟨hr, hdM, hrσ, hr1, hnd⟩
      have hd : r ∣ Nat.card ↥E := (hπE r hr).2 ⟨hdM, hrσ⟩
      obtain ⟨he, -⟩ := hrank r hr hd
      refine ⟨⟨hr, hd⟩, (forall_isCyclic_sylow_iff hr (hoddprime r hdM)).2 (by omega), ?_⟩
      rw [hcommE, ← hdvdDerived r hr hrσ]
      exact hnd
  have hpart6₃ : piThreePrimes' ↥E = tau3Primes M := by
    ext r
    simp only [piThreePrimes', Set.mem_ofPred_eq, mem_primeDivisorsOf, mem_tau3Primes_iff]
    constructor
    · rintro ⟨⟨hr, hd⟩, hcyc, hnd⟩
      obtain ⟨hdM, hrσ⟩ := (hπE r hr).1 hd
      have h1 := (forall_isCyclic_sylow_iff hr (hoddprime r hdM)).1 hcyc
      obtain ⟨he, -⟩ := hrank r hr hd
      have hr1 : 1 ≤ elementaryAbelianPRank r ↥E :=
        (one_le_elementaryAbelianPRank_iff hr).2 hd
      refine ⟨hr, hdM, hrσ, by omega, ?_⟩
      rw [hdvdDerived r hr hrσ, ← hcommE]
      exact hnd
    · rintro ⟨hr, hdM, hrσ, hr1, hnd⟩
      have hd : r ∣ Nat.card ↥E := (hπE r hr).2 ⟨hdM, hrσ⟩
      obtain ⟨he, -⟩ := hrank r hr hd
      refine ⟨⟨hr, hd⟩, (forall_isCyclic_sylow_iff hr (hoddprime r hdM)).2 (by omega), ?_⟩
      rw [hcommE, ← hdvdDerived r hr hrσ]
      exact hnd
  exact ⟨hpart1, fun r hr => hrank r hr.1 hr.2, hpart3, hpart4, hpart5, hpart6₁, hpart6₂, hpart6₃⟩

end

end CFSG.FeitThompson.Proofs
