module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.PlaneNormalizerRankTwoPrimesInSigma
import CFSG.FeitThompson.Local.SigmaComplementThreeHallFactors
import CFSG.FeitThompson.Local.SigmaTauThreePrimesDerivedContainment
import CFSG.FeitThompson.Local.SigmaComplementPlaneActionSupport
import CFSG.FeitThompson.Local.AmbientMaximalPlaneDerivedComplement
import CFSG.FeitThompson.OddOrder.SigmaSylowIsAmbientSylow
import CFSG.FeitThompson.Representations.DadeSignalizersCanonicalNormalHall
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

universe u

variable {G : Type*} [Group G]

theorem exists_isPGroup_le_not_dvd_relIndex [Finite G] {q : ℕ} (hq : q.Prime) (E : Subgroup G) :
    ∃ Q : Subgroup G, Q ≤ E ∧ IsPGroup q ↥Q ∧ (∃ m : ℕ, Nat.card ↥Q = q ^ m) ∧
      ¬ q ∣ Q.relIndex E := by
  have := Fact.mk hq
  let S : Sylow q ↥E := default
  have hP : IsPGroup q ↥((S : Subgroup ↥E).map E.subtype) :=
    S.isPGroup'.of_equiv ((S : Subgroup ↥E).equivMapOfInjective E.subtype E.subtype_injective)
  refine ⟨(S : Subgroup ↥E).map E.subtype, Subgroup.map_subtype_le _, hP, hP.exists_card_eq, ?_⟩
  rw [Subgroup.relIndex, subgroupOf_map_subtype]
  exact S.not_dvd_index

theorem elementaryAbelianPRank_le_two_of_notMem_sigmaPrimes [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) {T : Subgroup G} (hT : IsCoatom T)
    {q : ℕ} (hq : q.Prime) (hqσ : q ∉ sigmaPrimes T) : elementaryAbelianPRank q ↥T ≤ 2 := by
  by_contra h
  exact hqσ (alphaPrimes_subset_sigmaPrimes hna hodd hsolv hT (mem_alphaPrimes.2 ⟨hq, by omega⟩))

theorem le_of_isPGroup_of_relIndex_eq_pow [Finite G] {p q m n : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q ≠ p) {X D Q : Subgroup G} (hXD : X ≤ normalizer (D : Set G)) (hQX : Q ≤ X)
    (hQcard : Nat.card ↥Q = q ^ m) (hidx : D.relIndex X = p ^ n) : Q ≤ D := by
  have hnormal : (D.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hXD
  have hcop : (Nat.card ↥(Q.subgroupOf X)).Coprime (D.subgroupOf X).index := by
    rw [natCard_subgroupOf hQX, hQcard, ← Subgroup.relIndex, hidx]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hq hp).2 hqp)
  have h := le_of_coprime_natCard_index hcop
  intro x hx
  have hmem : (⟨x, hQX hx⟩ : ↥X) ∈ Q.subgroupOf X := hx
  exact h hmem

theorem commutator_le_inf_of_le_normalizer {A D Q : Subgroup G}
    (hQA : Q ≤ normalizer (A : Set G)) (hAD : A ≤ normalizer (D : Set G)) (hQD : Q ≤ D) :
    (⁅A, Q⁆ : Subgroup G) ≤ A ⊓ D :=
  le_inf (Subgroup.le_normalizer_iff_commutator_le_left.1 hQA)
    (by
      rw [Subgroup.commutator_comm]
      exact le_trans (Subgroup.commutator_mono hQD le_rfl)
        (Subgroup.le_normalizer_iff_commutator_le_left.1 hAD))

theorem FNI_plane_normalizer_action_prime_transfer
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_hall_abelian.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_plane_normalizer_action_prime_transfer.{u} := by
  intro G _ _ hG p M A E T hA hE hAE hT hNT q hq hqdvd
  have := hG.isSimpleGroup
  let _ : Fintype G := Fintype.ofFinite G
  have hfp := Fact.mk hA.prime
  have hG2 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG3 : Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨hEnormA, -, -, -, -⟩ := h₃ G hG p M A E hA hE hAE
  have hET : E ≤ T := hEnormA.trans hNT
  have hAT : A ≤ T := le_trans le_normalizer hNT
  have hrel0 : (E ⊓ centralizer (A : Set G) : Subgroup G).relIndex E ≠ 0 := by
    rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite
  obtain ⟨E₁, E₂, E₃, hsplit, -⟩ := FNI_sigma_complement_three_factors h₁ G hG M E hE
  obtain ⟨-, -, hτ₁⟩ := sigma_complement_plane_action_support h₂ h₃ h₅ hG2 hE.isCoatom hA.prime
    hA.notMem_sigmaPrimes hA.le hA.isElementaryAbelianPlane hE.isInternalSemidirectProduct hAE
    ⟨hsplit.le_E₁, hsplit.isHall_E₁⟩ ⟨hsplit.le_E₂, hsplit.isHall_E₂⟩
    ⟨hsplit.le_E₃, hsplit.isHall_E₃⟩ hsplit.outer hsplit.inner
  have hqτ₁M : q ∈ tau1Primes M := hτ₁ q (Nat.mem_primeFactors.2 ⟨hq, hqdvd, hrel0⟩)
  have hrankp : elementaryAbelianPRank p ↥M = 2 := (h₅ G hG p M A hA).1
  have hqnep : q ≠ p := by
    intro h
    rw [h] at hqτ₁M
    have := elementaryAbelianPRank_eq_one_of_mem_tau1Primes hqτ₁M
    omega
  obtain ⟨Q, hQE, -, ⟨m, hQcard⟩, hQidx⟩ := exists_isPGroup_le_not_dvd_relIndex hq E
  have hQnc : ¬ Q ≤ E ⊓ centralizer (A : Set G) := fun hle =>
    hQidx (dvd_trans hqdvd (Subgroup.relIndex_dvd_of_le_left _ hle))
  have hqdvdT : q ∣ Nat.card ↥T := by
    refine dvd_trans (dvd_trans hqdvd ?_) (Subgroup.card_dvd_of_le hET)
    rw [Subgroup.relIndex]; exact Subgroup.index_dvd_card _
  have hpσT : p ∈ sigmaPrimes T :=
    (FNI_plane_normalizer_rank_two_primes_in_sigma h₁ h₂ h₃ h₄ h₅ h₆ G hG p M A E T
      hA hE hAE hT hNT).2 (mem_tauTwoPrimes_iff.2 ⟨hA.prime, hA.notMem_sigmaPrimes, hrankp⟩)
  have hAT' : A ≤ (⁅T, T⁆ : Subgroup G) :=
    le_trans (le_sigmaCore_of_isPiSubgroup (h₁ G hG2 T hT).1 hAT
      (isPiSubgroup_of_plane hA.prime hpσT hA.isElementaryAbelianPlane)) (h₁ G hG2 T hT).2.2
  obtain ⟨R, hR, hAR⟩ := exists_isSylowSubgroupOf_ge_of_isPGroup_subgroupOf hAT
    (isPGroup_subgroupOf_of_plane hAT hA.isElementaryAbelianPlane)
  have hRcard : Nat.card ↥R = p ^ (Nat.card G).factorization p := by
    rw [(_root_.CFSG.FeitThompson.isSylowIn_iff_natCard hA.prime hR.le).1 hR,
      factorization_eq_of_mem_sigmaPrimes hpσT]
  have hAea : IsElementaryAbelianSubgroup p A :=
    hA.isElementaryAbelianPlane.isElementaryAbelianSubgroup
  have hAmax : Maximal (IsElementaryAbelianSubgroup p) A := (h₅ G hG p M A hA).2.1
  have hArank : elementaryAbelianPRank p ↥A = 2 := by
    have h := card_eq_pow_elementaryAbelianPRank_of_isElementaryAbelianSubgroup hA.prime hAea
    rw [hA.isElementaryAbelianPlane.natCard'] at h
    exact (Nat.pow_right_injective hA.prime.two_le h).symm
  obtain ⟨D, -, hT'D, hpD, n, hidx⟩ :=
    FNI_ambient_maximal_plane_derived_prime_complement G hG3 p R A hA.prime hRcard hAR hAea hArank
      (fun B hB hAB => le_antisymm (hAmax.2 hB hAB) hAB) T (lt_top_iff_ne_top.2 hT.1) hR.le
  by_contra hcon
  rw [not_or] at hcon
  have hqmem : q ∈ sigmaPrimes T ∨ q ∈ tau3Primes T := by
    by_cases hqσT : q ∈ sigmaPrimes T
    · exact Or.inl hqσT
    ·
      have hle2 := elementaryAbelianPRank_le_two_of_notMem_sigmaPrimes hG.not_isMulCommutative
        hG.odd_natCard hG.isSolvable_of_ne_top hT hq hqσT
      have h1 : 1 ≤ elementaryAbelianPRank q ↥T :=
        (one_le_elementaryAbelianPRank_iff hq).2 hqdvdT
      have hne2 : elementaryAbelianPRank q ↥T ≠ 2 := fun h =>
        hcon.2 (mem_tauTwoPrimes_iff.2 ⟨hq, hqσT, h⟩)
      have hmem : q ∈ tau1Primes T ∪ tau3Primes T := by
        rw [tau1Primes_union_tau3Primes]
        exact ⟨hq, hqdvdT, hqσT, by omega⟩
      rcases hmem with h | h
      · exact absurd h hcon.1
      · exact Or.inr h
  have hQT' : Q ≤ (⁅T, T⁆ : Subgroup G) :=
    FNI_sigma_third_primes_derived_containment h₁ G hG q T hT hq hqmem Q (hQE.trans hET)
      ⟨m, hQcard⟩
  have hQD : Q ≤ D := le_of_isPGroup_of_relIndex_eq_pow hA.prime hq hqnep hT'D hQT' hQcard hidx
  have hAD : Disjoint A D := Subgroup.disjoint_of_coprime_natCard (by
    rw [hA.isElementaryAbelianPlane.natCard']
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hA.prime).2 hpD))
  have hcomm : (⁅A, Q⁆ : Subgroup G) = ⊥ :=
    le_bot_iff.1 (le_trans (commutator_le_inf_of_le_normalizer (hQE.trans hEnormA)
      (hAT'.trans hT'D) hQD) (disjoint_iff.1 hAD).le)
  rw [Subgroup.commutator_comm] at hcomm
  exact hQnc (le_inf hQE (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm))

end

end CFSG.FeitThompson.Proofs
