module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.NarrowSupportedPlaneCentralizesQSubgroup
import CFSG.FeitThompson.Local.ElementaryMaximalPLengthOneConstraint
import CFSG.FeitThompson.Local.KappaPrimeLineFixedEquivalence
import CFSG.FeitThompson.Local.NilpotentDerivedNormalizerFactorization
import CFSG.FeitThompson.Local.SplitKernelRemovalExponentAbelianSylow
import CFSG.FeitThompson.Foundations.NormalCommuteModIntersection
import CFSG.FeitThompson.Local.KappaPositiveMultipleCoreTrivialResidual
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup
open CFSG.FeitThompson.Prep03 (IsAmbient IsSemidirect)
open CFSG.FeitThompson.Prep09 (IsMinimalSimpleOddOrder
  IsMaximalElementaryAbelianPlane)

universe u

variable {G : Type u} [Group G]

theorem isOddSimpleMinimal_of_isAmbient [Fintype G] (hG : IsAmbient G) : IsOddSimpleMinimal G :=
  ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩

theorem isMinimalSimpleOddOrder_of_isAmbient [Fintype G] (hG : IsAmbient G) :
    IsMinimalSimpleOddOrder G :=
  ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩

theorem isElementaryAbelianPlane_map {p : ℕ} {B : Subgroup G} {f : G →* G}
    (hf : Function.Injective f) (h : IsElementaryAbelianPlane p B) :
    IsElementaryAbelianPlane p (B.map f) := by
  obtain ⟨e⟩ := h
  exact ⟨(equivMapOfInjective B f hf).symm.trans e⟩

theorem exists_plane_le_of_mem_tauTwoPrimes [Finite G] {q : ℕ} {M : Subgroup G}
    (h : q ∈ tauTwoPrimes M) : ∃ B : Subgroup G, B ≤ M ∧ IsElementaryAbelianPlane q B := by
  obtain ⟨-, -, ⟨H, hH⟩, -⟩ := mem_tauTwoPrimes_iff_exists_subgroup.1 h
  obtain ⟨e⟩ := hH
  exact ⟨H.map M.subtype, map_subtype_le _,
    ⟨(equivMapOfInjective H M.subtype M.subtype_injective).symm.trans e⟩⟩

theorem exists_plane_le_of_isInternalSemidirectProduct [Finite G] {q : ℕ} {M E : Subgroup G}
    (hq : q ∈ tauTwoPrimes M)
    (hdecomp : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E) :
    ∃ B : Subgroup G, B ≤ E ∧ IsElementaryAbelianPlane q B := by
  have hqp : q.Prime := prime_of_mem_tauTwoPrimes hq
  have : Fact q.Prime := ⟨hqp⟩
  have hqS : ¬ q ∣ Nat.card ↥(sigmaCore M) := fun hdvd =>
    notMem_sigmaPrimes_of_mem_tauTwoPrimes hq
      (isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) q
        (Nat.mem_primeFactors.2 ⟨hqp, hdvd, Nat.card_pos.ne'⟩))
  have hfact : (Nat.card ↥M).factorization q = (Nat.card ↥E).factorization q := by
    rw [hdecomp.natCard_eq_mul, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
    simp [Nat.factorization_eq_zero_of_not_dvd hqS]
  obtain ⟨B', hB'M, hB'plane⟩ := exists_plane_le_of_mem_tauTwoPrimes hq
  set S₀ : Sylow q ↥E := default with hS₀
  have hTE : ((S₀ : Subgroup ↥E)).map E.subtype ≤ E := map_subtype_le _
  have hTcard : Nat.card ↥(((S₀ : Subgroup ↥E)).map E.subtype)
      = q ^ (Nat.card ↥M).factorization q := by
    rw [card_subtype, S₀.card_eq_multiplicity, hfact]
  obtain ⟨S, hS⟩ := (exists_sylow_map_subtype_eq_iff hqp
    (P := ((S₀ : Subgroup ↥E)).map E.subtype)).2 ⟨hTE.trans hdecomp.right_le, hTcard⟩
  have hB'pg : IsPGroup q ↥(B'.subgroupOf M) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_congr (subgroupOfEquivOfLe hB'M).toEquiv]
    exact hB'plane.natCard'
  obtain ⟨m, -, hle⟩ := exists_mem_map_conj_le_sylow hB'M hB'pg S
  exact ⟨B'.map (MulAut.conj m : G →* G), (hS ▸ hle).trans hTE,
    isElementaryAbelianPlane_map (MulAut.conj m).injective hB'plane⟩

theorem le_centralizer_of_normal_of_coprime {E A B : Subgroup G} (hAE : A ≤ E) (hBE : B ≤ E)
    (hA : E ≤ normalizer (A : Set G)) (hB : E ≤ normalizer (B : Set G))
    (hcop : (Nat.card ↥A).Coprime (Nat.card ↥B)) : B ≤ centralizer (A : Set G) := by
  have hnA : (A.subgroupOf E).Normal := (normal_subgroupOf_iff_le_normalizer hAE).2 hA
  have hnB : (B.subgroupOf E).Normal := (normal_subgroupOf_iff_le_normalizer hBE).2 hB
  have hcop' : (Nat.card ↥(A.subgroupOf E)).Coprime (Nat.card ↥(B.subgroupOf E)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hAE).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hBE).toEquiv]
  intro b hb
  refine mem_centralizer_iff.2 fun a ha => ?_
  have h := mul_comm_of_normal_of_coprime_natCard (A.subgroupOf E) (B.subgroupOf E) hcop'
    (a := ⟨a, hAE ha⟩) (b := ⟨b, hBE hb⟩) (mem_subgroupOf.2 ha) (mem_subgroupOf.2 hb)
  exact congrArg (fun z : ↥E => (z : G)) h

theorem FNI_nonabelian_ambient_single_rank_two_prime
    (h₁ : Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₂ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₃ : Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₄ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FNI_nonabelian_ambient_single_rank_two_prime.{u} := by
  intro G _ _ hG p M A E hsetup hnonab
  have hG' : IsOddSimpleMinimal G := isOddSimpleMinimal_of_isAmbient hG
  have hGm : IsMinimalSimpleOddOrder G := isMinimalSimpleOddOrder_of_isAmbient hG
  have hp : p.Prime := hsetup.prime
  have : Fact p.Prime := ⟨hp⟩
  have hdecomp : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E :=
    isInternalSemidirectProduct_of_isSemidirect hsetup.decomp
  have hAplane : IsElementaryAbelianPlane p A := hsetup.isPlane
  have hosA : IsOutsideSigmaPlane p M A :=
    ⟨hsetup.isCoatom, hp, hsetup.notMem_sigma, hsetup.le_M_A, hAplane⟩
  have hsc : IsSigmaComplement M E := ⟨hsetup.isCoatom, hdecomp⟩
  have hAE : A ≤ E := hsetup.le_E_A
  have hrankA := (h₂ G hG' p M A hosA).1
  have hpτ : p ∈ tauTwoPrimes M := mem_tauTwoPrimes_iff.2 ⟨hp, hsetup.notMem_sigma, hrankA⟩
  refine Set.eq_singleton_iff_unique_mem.2 ⟨hpτ, fun q hq => ?_⟩
  by_contra hqp
  have hqprime : q.Prime := prime_of_mem_tauTwoPrimes hq
  have : Fact q.Prime := ⟨hqprime⟩
  obtain ⟨B, hBE, hBplane⟩ := exists_plane_le_of_isInternalSemidirectProduct hq hdecomp
  have hosB : IsOutsideSigmaPlane q M B :=
    ⟨hsetup.isCoatom, hqprime, notMem_sigmaPrimes_of_mem_tauTwoPrimes hq,
      hBE.trans hdecomp.right_le, hBplane⟩
  obtain ⟨hnormB, -, hCB, -, -⟩ := h₁ G hG' q M B E hosB hsc hBE
  obtain ⟨hnormA, -, -, -, -⟩ := h₁ G hG' p M A E hosA hsc hAE
  have hAcard : Nat.card ↥A = p ^ 2 := hAplane.natCard'
  have hBcard : Nat.card ↥B = q ^ 2 := hBplane.natCard'
  have hcop : (Nat.card ↥A).Coprime (Nat.card ↥B) := by
    rw [hAcard, hBcard]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hqprime).2 (Ne.symm hqp))
  have hBcentA : B ≤ centralizer (A : Set G) :=
    le_centralizer_of_normal_of_coprime hAE hBE hnormA hnormB hcop
  have hqdvdC : q ∣ Nat.card ↥(centralizer (A : Set G)) :=
    (dvd_pow_self q two_ne_zero).trans (hBcard ▸ card_dvd_of_le hBcentA)
  have hAmax : Maximal (IsElementaryAbelianSubgroup p) A := (h₂ G hG' p M A hosA).2.1
  have hBmax : Maximal (IsElementaryAbelianSubgroup q) B := (h₂ G hG' q M B hosB).2.1
  have hAmp : IsMaximalElementaryAbelianPlane p A := ⟨hAmax, hAcard⟩
  have hBpg : IsPGroup q ↥B := IsPGroup.of_card hBcard
  have hAnB : A ≤ normalizer (B : Set G) := hAE.trans hnormB
  obtain ⟨Q, hQmem, hBQ⟩ := exists_mem_maximalNormalizedPSubgroups_ge hBpg hAnB
  have hQpg : IsPGroup q ↥Q := (mem_maximalNormalizedPSubgroups_iff.1 hQmem).1.1
  have hAnQ : A ≤ normalizer (Q : Set G) := le_normalizer_of_mem hQmem
  have halt : IsCyclic ↥Q ∨ ∃ B' : Subgroup ↥Q, IsMaximalElementaryAbelianPlane q B' :=
    Or.inr ⟨B.subgroupOf Q, maximal_isElementaryAbelianSubgroup_subgroupOf hBmax hBQ,
      by rw [Nat.card_congr (subgroupOfEquivOfLe hBQ).toEquiv, hBcard]⟩
  obtain ⟨P, -, -, -, hPQ⟩ :=
    FTS_supported_plane_narrow_centralization h₃ h₄ G hGm p q hp hqprime (Ne.symm hqp) A hAmp
      Q hQpg hAnQ hQmem hqdvdC halt
  have hPC : (P : Subgroup G) ≤ centralizer (Q : Set G) :=
    commutator_eq_bot_iff_le_centralizer.1 hPQ
  have hPE : (P : Subgroup G) ≤ E :=
    hPC.trans ((centralizer_le (SetLike.coe_subset_coe.2 hBQ)).trans hCB)
  have hPM : (P : Subgroup G) ≤ M := hPE.trans hdecomp.right_le
  have hPcard : Nat.card ↥(P : Subgroup G) = p ^ (Nat.card G).factorization p :=
    P.card_eq_multiplicity
  have hPcardM : Nat.card ↥(P : Subgroup G) = p ^ (Nat.card ↥M).factorization p :=
    natCard_eq_pow_factorization_of_le hp hPM hPcard
  have hPsyl : IsSylowIn p M (P : Subgroup G) :=
    (exists_sylow_map_subtype_eq_iff hp).2 ⟨hPM, hPcardM⟩
  have hPab : IsMulCommutative ↥(P : Subgroup G) :=
    ((h₂ G hG' p M A hosA).2.2.1 (P : Subgroup G) hPsyl).1
  obtain ⟨R, hRcard, hRnonab⟩ := hnonab
  exact hRnonab (isMulCommutative_of_natCard_eq_pow_factorization hPab hPcard hRcard)

end

end CFSG.FeitThompson.Proofs
