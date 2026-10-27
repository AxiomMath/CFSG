module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.AdmissibleTauOneDisplacementContradiction
import CFSG.FeitThompson.Local.SigmaCoreConjugateTrivialExceptionalPlane
import CFSG.FeitThompson.Local.SigmaComplementExistsNontrivial
import CFSG.FeitThompson.Local.PComplementControlSylowNormalizer
import CFSG.FeitThompson.Local.ControlledPlaneCentralizersPrimeCore
import CFSG.FeitThompson.Local.NormalBetaSylowControlsFittingPrimes
import CFSG.FeitThompson.OddOrder.MaximalOvergroupExistence
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson CFSG.FeitThompson

universe u

theorem le_centralizer_of_isMinimalOddSimple_of_forall_prime
    (hd : _root_.CFSG.FeitThompson.Statements.FTS_admissible_tau_one_displacement_contradiction.{u})
    {G : Type u} [Group G] [Finite G] (hG : Prep06.IsMinimalOddSimple G)
    {M E : Subgroup G} (hM : M ∈ Prep06.maximalSubgroups G) (hEM : E ≤ M)
    (hsup : sigmaCore M ⊔ E = M) (hinf : sigmaCore M ⊓ E = ⊥)
    {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpτ : p ∈ tau1Primes M)
    {P R : Subgroup G} (hPE : P ≤ E) (hPcard : Nat.card ↥P = p)
    (hRCE : R ≤ E ⊓ centralizer (P : Set G)) (hRcard : Nat.card ↥R = r)
    (hadm : r ∈ tau1Primes M →
      Prep06.alphaCoreIn M ⊓ centralizer (P : Set G) ≤
        Prep06.alphaCoreIn M ⊓ centralizer (R : Set G) →
      Prep06.alphaCoreIn M ⊓ centralizer (P : Set G) =
        Prep06.alphaCoreIn M ⊓ centralizer (R : Set G))
    (hcop : (Nat.card ↥(sigmaCore M)).Coprime (Nat.card ↥E))
    {C : Subgroup G} (hCS : C ≤ sigmaCore M ⊓ centralizer (P : Set G))
    (hRC : R ≤ normalizer (C : Set G))
    (hdisj : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥C →
      q ∈ alphaPrimes ↥M ∨
        Prep06.alphaCoreIn M ⊓ centralizer (P : Set G) ≤
          Prep06.alphaCoreIn M ⊓ centralizer (R : Set G)) :
    C ≤ centralizer (R : Set G) := by
  have hfin : Fintype G := Fintype.ofFinite G
  have hM' : IsCoatom M := hM
  have := hG.simple
  have hRE : R ≤ E := hRCE.trans inf_le_left
  have hRM : R ≤ M := hRE.trans hEM
  have hCsig : C ≤ sigmaCore M := hCS.trans inf_le_left
  have hCM : C ≤ M := hCsig.trans (sigmaCore_le M)
  have hMsolv : Group.IsSolvable ↥M := hG.solvable M hM'.1
  have hsolv : Group.IsSolvable ↥(C ⊔ R : Subgroup G) :=
    @isSolvable_of_le _ _ _ _ (sup_le hCM hRM) hMsolv
  have hcopCR : (Nat.card ↥C).Coprime (Nat.card ↥R) :=
    (Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hCsig) hcop).coprime_dvd_right
      (Subgroup.card_dvd_of_le hRE)
  obtain ⟨T, hT, hNT⟩ := exists_isCoatom_ge_of_ne_top
    (normalizer_ne_top_of_natCard_eq_prime hG.nonabelian hp hPcard)
  have key : ∀ q : ℕ, q.Prime → ∃ V : Subgroup G, V ≤ C ∧
      Nat.card ↥V = q ^ (Nat.card ↥C).factorization q ∧ V ≤ centralizer (R : Set G) := by
    intro q hq
    obtain ⟨V, hVsyl, -, hRV⟩ := exists_isSylowSubgroupOf_ge_le_normalizer (D := C) (A := R)
      (Q := ⊥) hsolv hRC hcopCR hq bot_le
      (by rw [Subgroup.normalizer_eq_top]; exact le_top) (IsPGroup.of_card (n := 0) (by simp))
    obtain ⟨hVC, hVcard⟩ := isSylowSubgroupOf_iff.1 hVsyl
    by_cases hcomm : (⁅V, R⁆ : Subgroup G) = ⊥
    · exact ⟨V, hVC, hVcard, Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm⟩
    ·
      exact absurd (hd G hG M E hM hEM hsup hinf p r q ((Nat.card ↥C).factorization q) hp hr hq
        hpτ P R V T hPE hPcard hRCE hRcard (hVC.trans hCS) hVcard hRV hcomm hT hNT hadm
        (hdisj q hq (by
          have hVne : V ≠ ⊥ := by
            intro h
            exact hcomm (by rw [h]; simp)
          have hane : (Nat.card ↥C).factorization q ≠ 0 := by
            intro h
            exact hVne (Subgroup.card_eq_one.1 (by rw [hVcard, h, pow_zero]))
          exact dvd_trans (dvd_pow_self q hane) (hVcard ▸ Subgroup.card_dvd_of_le hVC)))) id
  have hS : C ⊓ centralizer (R : Set G) = C := by
    refine eq_of_le_of_forall_pow_factorization_dvd inf_le_left fun q hq => ?_
    obtain ⟨V, hVC, hVcard, hVR⟩ := key q hq
    exact hVcard ▸ Subgroup.card_dvd_of_le (le_inf hVC hVR)
  exact hS.ge.trans inf_le_right

theorem FTS_admissible_tau_one_prime_centralizer_inclusion
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_nonabelian_prime_subgroup_unique_maximum.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_beta_prime_centralizing_sylow.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_three_prime_normalizer_transfer.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_admissible_tau_one_prime_centralizer_inclusion.{u} := by
  intro G _ _ hG M E hM hEM hsup hinf p r hp hr hpτ P R hPE hPcard hRCE hRcard hadm
  have hd := FTS_admissible_tau_one_displacement_contradiction h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
  have hM' : IsCoatom M := hM
  have := hG.simple
  have hG2 : IsOddOrderMinimalSimple G := ⟨hG.odd, hG.simple, hG.nonabelian, hG.solvable⟩
  obtain ⟨hHallOf, -, -⟩ := h₁ G hG2 M hM'
  have hsd : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E :=
    ⟨hsup, le_normalizer_sigmaCore M, disjoint_iff.2 hinf⟩
  have hcop : (Nat.card ↥(sigmaCore M)).Coprime (Nat.card ↥E) :=
    (isHallOf_and_coprime_of_isInternalSemidirectProduct hHallOf hEM hsd).2
  have hRE : R ≤ E := hRCE.trans inf_le_left
  have hRM : R ≤ M := hRE.trans hEM
  have hRcP : R ≤ centralizer (P : Set G) := hRCE.trans inf_le_right
  have hRnormCP : R ≤ normalizer ((centralizer (P : Set G) : Subgroup G) : Set G) := fun x hx =>
    le_normalizer (hRcP hx)
  have hAS : Prep06.alphaCoreIn M ≤ sigmaCore M := by
    rw [Prep06.alphaCoreIn_eq]
    exact map_subtype_alphaCore_le_sigmaCore hG.nonabelian hG.odd hG.solvable hM'
  have hRnormA : R ≤ normalizer ((Prep06.alphaCoreIn M : Subgroup G) : Set G) := by
    rw [Prep06.alphaCoreIn_eq]
    exact hRM.trans (le_normalizer_map_subtype_of_normal (alphaCore_normal ↥M))
  have hstage1 : Prep06.alphaCoreIn M ⊓ centralizer (P : Set G) ≤
      Prep06.alphaCoreIn M ⊓ centralizer (R : Set G) := by
    refine le_inf inf_le_left ?_
    refine le_centralizer_of_isMinimalOddSimple_of_forall_prime hd hG hM hEM hsup hinf hp hr hpτ
      hPE hPcard hRCE hRcard hadm hcop (le_inf (inf_le_left.trans hAS) inf_le_right)
      (fun x hx => normalizer_inf_le_normalizer_inf _ _ ⟨hRnormA hx, hRnormCP hx⟩) ?_
    intro q hq hqd
    refine Or.inl ?_
    have hdvd : q ∣ Nat.card ↥(Prep06.alphaCoreIn M) :=
      hqd.trans (Subgroup.card_dvd_of_le inf_le_left)
    have hcard : Nat.card ↥(Prep06.alphaCoreIn M) = Nat.card ↥(alphaCore ↥M) := by
      rw [Prep06.alphaCoreIn_eq]
      exact Subgroup.card_map_of_injective (K := alphaCore ↥M) M.subtype_injective
    rw [hcard] at hdvd
    exact primeFactors_natCard_alphaCore_subset ↥M
      (Nat.mem_primeFactors.2 ⟨hq, hdvd, Nat.card_pos.ne'⟩)
  refine le_inf inf_le_left ?_
  refine le_centralizer_of_isMinimalOddSimple_of_forall_prime hd hG hM hEM hsup hinf hp hr hpτ
    hPE hPcard hRCE hRcard hadm hcop le_rfl
    (fun x hx => normalizer_inf_le_normalizer_inf _ _
      ⟨hRM.trans (le_normalizer_sigmaCore M) hx, hRnormCP hx⟩)
    (fun q _ _ => Or.inr hstage1)

end

end CFSG.FeitThompson.Proofs
