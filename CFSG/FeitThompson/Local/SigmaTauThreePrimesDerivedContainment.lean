module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
import CFSG.FeitThompson.Local.CyclicSylowDerivedNormal
import CFSG.FeitThompson.Local.CriticalSubgroupFixedLine
import CFSG.FeitThompson.Local.PComplementQuotientSylowRank

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup

universe u

variable {G : Type u} [Group G] {q : ℕ} {M Q : Subgroup G}

theorem isPiSubgroup_subgroupOf {π : Set ℕ} (hQM : Q ≤ M) (hQ : IsPiSubgroup π Q) :
    IsPiSubgroup π (Q.subgroupOf M) := by
  refine isPiSubgroup_iff.2 fun r hr => isPiSubgroup_iff.1 hQ r ?_
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQM).toEquiv] at hr

variable [Finite G]

theorem le_sigmaCore_of_isPiSubgroup
    (hHall : CFSG.FeitThompson.IsHallPiSubgroupOf (sigmaPrimes M) (sigmaCore M) M)
    (hQM : Q ≤ M) (hQ : IsPiSubgroup (sigmaPrimes M) Q) : Q ≤ sigmaCore M := by
  have h := hHall.2.le_of_isPiSubgroup (isPiSubgroup_subgroupOf hQM hQ)
  have h2 := Subgroup.map_mono (f := M.subtype) h
  rwa [Subgroup.map_subgroupOf_eq_of_le hQM,
    Subgroup.map_subgroupOf_eq_of_le (sigmaCore_le M)] at h2

theorem le_commutator_of_mem_tau3Primes (hodd : Odd (Nat.card G)) (hq3 : q ∈ tau3Primes M)
    (hQM : Q ≤ M) (hQ : IsPGroup q ↥Q) : Q ≤ ⁅M, M⁆ := by
  obtain ⟨hq, hqM, -, hrank1, hdvd⟩ := mem_tau3Primes_iff.1 hq3
  have := Fact.mk hq
  have hqodd : Odd q := Odd.of_dvd_nat hodd (hqM.trans M.card_subgroup_dvd_card)
  obtain ⟨P, hP⟩ := (hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQM).symm).exists_le_sylow
  have hrank : elementaryAbelianPRank q ↥(P : Subgroup ↥M) = elementaryAbelianPRank q ↥M :=
    elementaryAbelianPRank_eq_of_natCard_eq_pow_factorization hq P.card_eq_multiplicity
  have : IsCyclic ↥(P : Subgroup ↥M) :=
    isCyclic_of_elementaryAbelianPRank_le_one hq hqodd P.isPGroup' (by rw [hrank, hrank1])
  have hdvd' : q ∣ Nat.card ↥(_root_.commutator ↥M) := by
    rw [natCard_commutator_subtype]; exact hdvd
  have h2 := Subgroup.map_mono (f := M.subtype) (hP.trans (cyclicSylow_le_commutator P hdvd'))
  rwa [Subgroup.map_subgroupOf_eq_of_le hQM, Subgroup.map_subtype_commutator] at h2

theorem FNI_sigma_third_primes_derived_containment
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u}) :
    Statements.FNI_sigma_third_primes_derived_containment.{u} := by
  intro G _ _ hG q M hM hq hqmem Q hQM hQpow
  obtain ⟨n, hQcard⟩ := hQpow
  rcases hqmem with hqσ | hq3
  ·
    let _ : Fintype G := Fintype.ofFinite G
    obtain ⟨hHallOf, -, hSle⟩ := h₁ G
      ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩ M hM
    refine le_trans (le_sigmaCore_of_isPiSubgroup hHallOf hQM ?_) hSle
    refine isPiSubgroup_iff.2 fun r hr => ?_
    rw [hQcard] at hr
    obtain ⟨hr1, hr2, -⟩ := Nat.mem_primeFactors.1 hr
    rwa [(Nat.prime_dvd_prime_iff_eq hr1 hq).1 (hr1.dvd_of_dvd_pow hr2)]
  ·
    exact le_commutator_of_mem_tau3Primes hG.odd_natCard hq3 hQM (IsPGroup.of_card hQcard)

end

end CFSG.FeitThompson.Proofs
