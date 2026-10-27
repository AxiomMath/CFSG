module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.Local.RegularTauOneSylowBetaFixedPoints
import CFSG.FeitThompson.Local.NoncentralInvariantSylowFixedPointFreePlane
import CFSG.FeitThompson.Local.TauTwoFactorContainsPlaneRegularActions
import CFSG.FeitThompson.Local.SigmaComplementPlaneActionSupport
import CFSG.FeitThompson.Local.OddFrobeniusComplementPrimeSubgroupsNormal
import CFSG.FeitThompson.Local.AbelianSylowNormalPrimeCentralizerFitting
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.Local.RegularTauAlphaFixedPoints
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Representations.TypeIIDerivedFrobeniusOrEqualDegreePair

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

universe u

variable {G : Type u} [Group G]

theorem exists_prime_factorization_lt_of_ne [Finite G] {D E : Subgroup G} (hDE : D ≤ E)
    (hne : D ≠ E) :
    ∃ q : ℕ, q.Prime ∧ (Nat.card ↥D).factorization q < (Nat.card ↥E).factorization q := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  have hdvd : Nat.card ↥E ∣ Nat.card ↥D := by
    refine (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').1 (Finsupp.le_def.2 ?_)
    intro q
    by_cases hq : q.Prime
    · exact hcon q hq
    · simp [Nat.factorization_eq_zero_of_not_prime _ hq]
  exact hne (Subgroup.eq_of_le_of_card_ge hDE (Nat.le_of_dvd Nat.card_pos hdvd))

theorem FNI_tau13_noncentral_prime_configuration
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FTS_beta_prime_centralizing_sylow.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_tau13_noncentral_prime_configuration.{u} := by
  intro G _ _ hG M E E₁ E₂ E₃ htf p hp P hPE₁ hPcard hnc
  let _ : Fintype G := Fintype.ofFinite G
  have hcyc₃ := htf.isCyclic_E₃
  have hGOOMS : _root_.CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hM : IsCoatom M := htf.isSigmaComplement.isCoatom
  have hsemiM := htf.isSigmaComplement.semidirect
  have hEM : E ≤ M := hsemiM.right_le
  have hE₃E : E₃ ≤ E := htf.le_E₃
  have hE₁E : E₁ ≤ E := htf.le_E₁
  have hEnormE₃ : E ≤ normalizer (E₃ : Set G) := htf.semidirect_E.le_normalizer
  have hPE : P ≤ E := hPE₁.trans hE₁E
  have hPM : P ≤ M := hPE.trans hEM
  have hE₃M : E₃ ≤ M := hE₃E.trans hEM
  have hptau : p ∈ tau1Primes M := by
    obtain ⟨y, hyP, hyp⟩ := exists_mem_orderOf_eq_of_dvd hp (H := P) (by rw [hPcard])
    exact mem_of_isHallPiSubgroup_subgroupOf hE₁E htf.hall_E₁ (hPE₁ hyP) hp hyp
  have hCne : E₃ ⊓ centralizer (P : Set G) ≠ E₃ := fun h =>
    hnc (Subgroup.le_centralizer_iff.2 (h ▸ inf_le_right))
  obtain ⟨q, hq, hqlt⟩ :=
    exists_prime_factorization_lt_of_ne (inf_le_left (b := centralizer (P : Set G))) hCne
  have : Fact q.Prime := ⟨hq⟩
  have hapos : 0 < (Nat.card ↥E₃).factorization q := by omega
  have hqE₃ : q ∣ Nat.card ↥E₃ :=
    (Nat.Prime.dvd_iff_one_le_factorization hq Nat.card_pos.ne').2 hapos
  have hqtau : q ∈ tau3Primes M := by
    obtain ⟨y, hyE₃, hyq⟩ := exists_mem_orderOf_eq_of_dvd hq hqE₃
    exact mem_of_isHallPiSubgroup_subgroupOf hE₃E htf.hall_E₃ hyE₃ hq hyq
  have hpq : p ≠ q := fun h =>
    (Set.disjoint_left.1 (disjoint_tau1Primes_tau3Primes M)) hptau (h ▸ hqtau)
  set S : Subgroup ↥E₃ := ((default : Sylow q ↥E₃) : Subgroup ↥E₃) with hS
  set Q : Subgroup G := S.map E₃.subtype with hQdef
  have hQcard : Nat.card ↥Q = q ^ (Nat.card ↥E₃).factorization q := by
    rw [hQdef, Subgroup.card_subtype, hS]
    exact (default : Sylow q ↥E₃).card_eq_multiplicity
  have hQE₃ : Q ≤ E₃ := by rw [hQdef]; exact Subgroup.map_subtype_le _
  have hQM : Q ≤ M := hQE₃.trans hE₃M
  have hQbot : Q ≠ ⊥ := by
    intro hb
    have h1 : q ^ (Nat.card ↥E₃).factorization q = 1 := by
      rw [← hQcard, hb, Subgroup.card_bot]
    rcases Nat.pow_eq_one.1 h1 with h | h
    · exact hq.one_lt.ne' h
    · omega
  have hQcyc : IsCyclic ↥Q := isCyclic_of_le_of_isCyclic hQE₃ hcyc₃
  have hQpg : IsPGroup q ↥Q := IsPGroup.of_card hQcard
  have hQchar : S.Characteristic := by rw [hS]; exact characteristic_of_isCyclic _
  have hEnormQ : E ≤ normalizer (Q : Set G) := by
    rw [hQdef]
    exact le_normalizer_map_subtype_of_characteristic S hEnormE₃
  have hfix : Q ⊓ centralizer (P : Set G) = ⊥ := by
    by_contra hne
    have hPpg : IsPGroup p ↥P := IsPGroup.of_card (n := 1) (by rw [hPcard, pow_one])
    have hcomm := commutator_eq_bot_of_isCyclic_of_inf_centralizer_ne_bot hp hq hpq hPpg hQpg
      hQcyc (hPE.trans hEnormQ) hne
    have hQC : Q ≤ E₃ ⊓ centralizer (P : Set G) :=
      le_inf hQE₃ (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm)
    have hdvd : q ^ (Nat.card ↥E₃).factorization q ∣
        Nat.card ↥(E₃ ⊓ centralizer (P : Set G) : Subgroup G) := by
      rw [← hQcard]; exact Subgroup.card_dvd_of_le hQC
    have := (Nat.Prime.pow_dvd_iff_le_factorization hq Nat.card_pos.ne').1 hdvd
    omega
  have hσ := h₁ G hGOOMS M hM
  have hqσ : q ∉ sigmaPrimes M := notMem_sigmaPrimes_of_mem_tau3Primes hqtau
  have hqS : ¬ q ∣ Nat.card ↥(sigmaCore M) := fun hd =>
    hqσ (isPiSubgroup_iff.1 hσ.2.1.isPiSubgroup q
      (Nat.mem_primeFactors.2 ⟨hq, hd, Nat.card_pos.ne'⟩))
  have hfacE : (Nat.card ↥E).factorization q = (Nat.card ↥E₃).factorization q := by
    have h := factorization_natCard_eq_of_isHallSubgroup
      (isHallSubgroup_of_isHallPiSubgroup htf.hall_E₃) hq hqtau
    rwa [natCard_subgroupOf_of_le' hE₃E] at h
  have hfacM : (Nat.card ↥M).factorization q = (Nat.card ↥E₃).factorization q := by
    rw [hsemiM.natCard_eq_mul, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
    simp [Nat.factorization_eq_zero_of_not_dvd hqS, hfacE]
  have hQsylM : Nat.card ↥Q = q ^ (Nat.card ↥M).factorization q := by rw [hfacM, hQcard]
  have hnormQ : ¬ normalizer (Q : Set G) ≤ M := fun hle =>
    hqσ ((mem_sigmaPrimes_iff_exists_subgroup hq).2
      ⟨hqE₃.trans (Subgroup.card_dvd_of_le hE₃M), Q, hQM, hQsylM, hle⟩)
  obtain ⟨hαβ, hAB, hBne, hqβ, hfix1, hfix2⟩ :=
    FBG_regular_tau_one_sylow_beta_fixed_points h₂ G hGOOMS M hM p q hpq hp hq hptau P hPM hPcard
      Q ⟨hQM, hQsylM⟩ hQbot (hPE.trans hEnormQ) hfix
      (fun hset => hnormQ (by
        have hmem : M ∈ {T : Subgroup G | IsCoatom T ∧ normalizer (Q : Set G) ≤ T} := by
          rw [hset]; rfl
        exact hmem.2))
  have hAeq : Prep05.alphaCoreOf M =
      _root_.CFSG.FeitThompson.alphaCoreIn M := rfl
  have hBeq : Prep05.betaCoreOf M = betaCore M := by
    rw [Prep05.betaCoreOf_eq, betaCore_eq_map_piCore]
  refine ⟨q, hqtau, Q, hQE₃, hQbot, hQcyc, ⟨hQE₃, hQcard⟩, ⟨hQM, hQsylM⟩,
    hEnormQ, ?_, hnormQ, hαβ, ?_, ?_, ?_, ?_⟩
  · rw [Prep05.centralizerIn_eq]; exact hfix
  · rw [hAeq, hBeq, hAB]
  · rw [hAeq, hAB]; exact hBne
  · rw [Prep05.centralizerIn_eq, hAeq, hAB]; exact hfix1
  · rw [Prep05.centralizerIn_eq, hAeq, hAB, centralizer_coe_sup, ← centralizer_coe_mul_coe]
    exact hfix2

end

end CFSG.FeitThompson.Proofs
