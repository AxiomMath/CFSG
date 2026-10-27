module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
import CFSG.FeitThompson.Local.KappaFixedSubgroupDerivedAndHall
import CFSG.FeitThompson.Local.ExceptionalPrimeFixedConfiguration
import CFSG.FeitThompson.Local.AbelianSylowNormalPrimeCentralizerFitting
import CFSG.FeitThompson.Representations.TypeIIDerivedFrobeniusOrEqualDegreePair
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Presheaf

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G]

theorem inf_eq_bot_of_natCard_prime_of_ne [Finite G] {A B : Subgroup G} {a b : ℕ}
    (ha : a.Prime) (hb : b.Prime) (hA : Nat.card ↥A = a) (hB : Nat.card ↥B = b) (hne : A ≠ B) :
    A ⊓ B = ⊥ := by
  by_contra hbot
  have hdvdA : Nat.card ↥(A ⊓ B : Subgroup G) ∣ a := hA ▸ Subgroup.card_dvd_of_le inf_le_left
  have hdvdB : Nat.card ↥(A ⊓ B : Subgroup G) ∣ b := hB ▸ Subgroup.card_dvd_of_le inf_le_right
  have hne1 : Nat.card ↥(A ⊓ B : Subgroup G) ≠ 1 := fun h => hbot (Subgroup.card_eq_one.1 h)
  have heqA : Nat.card ↥(A ⊓ B : Subgroup G) = a := ((Nat.dvd_prime ha).1 hdvdA).resolve_left hne1
  have heqB : Nat.card ↥(A ⊓ B : Subgroup G) = b := ((Nat.dvd_prime hb).1 hdvdB).resolve_left hne1
  have h1 : (A ⊓ B : Subgroup G) = A :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hA, heqA])
  have h2 : (A ⊓ B : Subgroup G) = B :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hB, heqB])
  exact hne (h1 ▸ h2)

theorem commutator_le_of_sup_eq_of_isMulCommutative {H P R : Subgroup G} (hPH : P ≤ H)
    (hRH : R ≤ H) (hsup : P ⊔ R = H) (hPn : (P.subgroupOf H).Normal)
    (hRab : IsMulCommutative ↥R) : ⁅H, H⁆ ≤ P := by
  have := hPn
  have hsup' : P.subgroupOf H ⊔ R.subgroupOf H = ⊤ :=
    CFSG.FeitThompson.Proofs.sup_subgroupOf_eq_top_of_sup_eq hPH hRH hsup
  have hRab' : IsMulCommutative ↥(R.subgroupOf H) := isMulCommutative_subgroupOf_of_le hRH hRab
  have key : _root_.commutator ↥H ≤ P.subgroupOf H :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup' hRab'
  have h2 := Subgroup.map_mono (f := H.subtype) key
  rwa [Subgroup.map_subtype_commutator, Subgroup.map_subgroupOf_eq_of_le hPH] at h2

theorem natCard_dvd_sub_one_of_forall_inf_centralizer [Finite G] {K Z C : Subgroup G}
    (hZnorm : K ≤ normalizer ((Z : Subgroup G) : Set G))
    (hC : ∀ k ∈ K, k ≠ 1 → Z ⊓ centralizer ({k} : Set G) ≤ C) (hCZ : C ⊓ Z = ⊥) :
    Nat.card ↥K ∣ Nat.card ↥Z - 1 := by
  refine natCard_dvd_natCard_sub_one_of_mulAut (conjOnNormalized Z hZnorm) ?_
  intro z hz k hk
  by_contra hk1
  have hk1' : (k : G) ≠ 1 := fun h => hk1 (Subtype.ext h)
  have hconj : (k : G) * (z : G) * (k : G)⁻¹ = (z : G) := by
    have h2 := congrArg (fun w : ↥Z => (w : G)) hk
    rwa [conjOnNormalized_apply_coe] at h2
  have hmem : (z : G) ∈ Z ⊓ centralizer ({(k : G)} : Set G) := by
    refine ⟨z.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc (z : G) * (k : G) = ((k : G) * (z : G) * (k : G)⁻¹) * (k : G) := by rw [hconj]
      _ = (k : G) * (z : G) := by group
  have hmem2 : (z : G) ∈ C ⊓ Z := ⟨hC (k : G) k.2 hk1' hmem, z.2⟩
  rw [hCZ, Subgroup.mem_bot] at hmem2
  exact hz (Subtype.ext hmem2)

private theorem fittingIn_eq_mixedFitting [Finite G] (M : Subgroup G) :
    CFSG.FeitThompson.fittingIn M = mixedFitting M := by
  rw [mixedFitting_eq]; exact rfl

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson

universe u

theorem FBG_overlap_kappa_fixed_line_order_position
    (h₁ : Statements.FBG_nonabelian_fitting_overlap_central_lines.{u})
    (h₂ : Statements.FBG_nonabelian_fitting_overlap_primary.{u})
    (h₃ : Statements.FBG_nonnilpotent_sigma_core_hall_structure.{u})
    (h₄ : Statements.FNI_kappa_local_pair.{u})
    (h₅ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₆ : Statements.FNI_kappa_trivial_residual_prime_fixed_core.{u}) :
    Statements.FBG_overlap_kappa_fixed_line_order_position.{u} := by
  intro G _ _ hG M hM g hg X hX hXbot H hH hHab K hKbot hKhall hHS hsd p hp P hP Z₀ hZ₀ Kstar
    hKstar
  have hamb : CFSG.FeitThompson.IsFBGAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hamb3 : CFSG.FeitThompson.Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hsetup : CFSG.FeitThompson.IsFittingOverlapSetup M X g :=
    ⟨hM, hg, by rw [hX, fittingIn_eq_mixedFitting], hXbot⟩
  have hHab' : ¬ IsMulCommutative ↥(CFSG.FeitThompson.hallCoreIn M) := by rwa [← hH]
  obtain ⟨hpprime0, -, hZfam⟩ := h₁ G hamb M X g hsetup hHab'
  have hpprime : p.Prime := by rw [hp]; exact hpprime0
  have hpmem : p ∈ (Nat.card ↥X).primeFactors := by
    rw [← hp, hpprime.primeFactors]
    exact Finset.mem_singleton_self p
  obtain ⟨-, -, -, -, hRab, hdir, -⟩ := h₂ G hamb M X g hsetup hHab' p hpmem
  have hdir' : IsInternalDirectProduct H (pCoreIn p H) (pComplCoreIn p H) := by rw [hH]; exact hdir
  have hRab' : IsMulCommutative ↥(pComplCoreIn p H) := by rw [hH]; exact hRab
  have hPP' : P = pCoreIn p H := by rw [hP]
  have hHallPi : CFSG.FeitThompson.Prep03.IsHallPiOf (kappaPrimes M) K M :=
    isHallPiOf_of_isHallPiSubgroup_subgroupOf hKhall.1 hKhall.2
  have hκ : (kappaPrimes M).Nonempty := by
    obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (n := Nat.card ↥K)
      (fun h => hKbot (Subgroup.card_eq_one.1 h))
    exact ⟨r, hHallPi.2.1 r (Nat.mem_primeFactors.2 ⟨hr, hrd, Nat.card_pos.ne'⟩)⟩
  have hsdS : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) K := by rw [← hHS]; exact hsd
  have hsetupK : CFSG.FeitThompson.Prep03.IsKappaSetup G M K
      (CFSG.FeitThompson.Prep03.cent (sigmaCore M) (K : Set G))
      (K ⊔ CFSG.FeitThompson.Prep03.cent (sigmaCore M) (K : Set G)) :=
    { ambient := hamb3, isCoatom := hM, kappa_nonempty := hκ, isHall_K := hHallPi,
      A_eq := rfl, Z_eq := rfl }
  have hKstarA : Kstar = CFSG.FeitThompson.Prep03.cent (sigmaCore M) (K : Set G) := by
    rw [hKstar, hHS]; exact rfl
  have hKstarW : Kstar = CFSG.FeitThompson.centralizerWithin (sigmaCore M) K := by
    rw [hKstar, hHS]; exact rfl
  obtain ⟨hKcyc, hM'S, hAprime, -⟩ := h₆ G M K _ _ hsetupK
    (isSemidirect_of_isInternalSemidirectProduct hsdS)
  obtain ⟨-, -, hAle, hcentM'⟩ :=
    FBG_kappa_fixed_subgroup_derived_and_hall h₃ h₄ h₅ h₆ G hamb M K hM hKbot hKhall.1 hKhall.2
  have hM'H : (⁅M, M⁆ : Subgroup G) = H := by rw [hM'S, ← hHS]
  have hKstarHH : Kstar ≤ ⁅H, H⁆ := by
    rw [hKstarW]
    refine le_trans hAle ?_
    rw [hM'H]
    exact inf_le_right
  have hPsubNormal : ((pCoreIn p H).subgroupOf H).Normal := by
    have h1 : (pCoreIn p H).subgroupOf H = pCore p ↥H := by
      rw [pCoreIn_eq, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    rw [h1]
    infer_instance
  have hHHP : ⁅H, H⁆ ≤ pCoreIn p H :=
    commutator_le_of_sup_eq_of_isMulCommutative (pCoreIn_le p H) (pComplCoreIn_le p H)
      hdir'.sup_eq hPsubNormal hRab'
  have hKstarP : Kstar ≤ P := by rw [hPP']; exact le_trans hKstarHH hHHP
  have hKstarPrime : (Nat.card ↥Kstar).Prime := by rw [hKstarA]; exact hAprime
  have hcard : Nat.card ↥Kstar = p := by
    have := Fact.mk hpprime
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := ↥(pCoreIn p H))).1
      (isPGroup_pCoreIn hpprime H)
    have hdvd : Nat.card ↥Kstar ∣ p ^ n := by
      rw [← hn]
      exact Subgroup.card_dvd_of_le (by rw [hPP'] at hKstarP; exact hKstarP)
    exact (Nat.prime_dvd_prime_iff_eq hKstarPrime hpprime).1
      (hKstarPrime.dvd_of_dvd_pow hdvd)
  have hZfam' : ∀ q ∈ (Nat.card ↥H).primeFactors, ∃ Zq : Subgroup G,
      (Zq : Set G) = pTorsionSet q (centreIn (pCoreIn q H)) ∧
        (Zq.subgroupOf H).Characteristic ∧ Nat.card ↥Zq = q := by
    rw [hH]; exact hZfam
  have hZle : ∀ (q : ℕ) (Zq : Subgroup G),
      (Zq : Set G) = pTorsionSet q (centreIn (pCoreIn q H)) → Zq ≤ H := by
    intro q Zq hset z hz
    have h1 : z ∈ pTorsionSet q (centreIn (pCoreIn q H)) := by rw [← hset]; exact hz
    exact pCoreIn_le q H (centreIn_le _ (mem_pTorsionSet.1 h1).1)
  have hKnormH : K ≤ normalizer ((H : Subgroup G) : Set G) := by
    rw [hHS]; exact le_trans hKhall.1 (le_normalizer_sigmaCore M)
  have hfree : ∀ q ∈ (Nat.card ↥H).primeFactors, ∀ Zq : Subgroup G, Zq ≤ H →
      (Zq.subgroupOf H).Characteristic → Nat.card ↥Zq = q → Kstar ≠ Zq →
      Nat.card ↥K ∣ q - 1 := by
    intro q hq Zq hZqH hZqchar hZqcard hne
    have := hZqchar
    have hnorm : K ≤ normalizer ((Zq : Subgroup G) : Set G) := by
      have h2 := le_normalizer_map_subtype_of_characteristic (M := H) (Zq.subgroupOf H) hKnormH
      rwa [Subgroup.map_subgroupOf_eq_of_le hZqH] at h2
    have hinf : Kstar ⊓ Zq = ⊥ :=
      inf_eq_bot_of_natCard_prime_of_ne hpprime (Nat.prime_of_mem_primeFactors hq) hcard
        hZqcard hne
    have hdvd : Nat.card ↥K ∣ Nat.card ↥Zq - 1 := by
      refine natCard_dvd_sub_one_of_forall_inf_centralizer hnorm ?_ hinf
      intro k hk hk1 z hz
      have hz1 : z ∈ (⁅M, M⁆ : Subgroup G) ⊓ centralizer ({k} : Set G) :=
        ⟨by rw [hM'H]; exact hZqH hz.1, hz.2⟩
      have heq := hcentM' k hk hk1
      rw [hKstarW, ← heq]
      exact hz1
    rwa [hZqcard] at hdvd
  refine ⟨hpprime, hKcyc, hcard, hKstarP, ?_⟩
  by_cases hcase : Nat.card ↥K ∣ p - 1
  ·
    left
    intro q hq
    by_cases hqp : q = p
    · rwa [hqp]
    · obtain ⟨Zq, hZqset, hZqchar, hZqcard⟩ := hZfam' q hq
      refine hfree q hq Zq (hZle q Zq hZqset) hZqchar hZqcard ?_
      intro hKZ
      exact hqp (by rw [← hZqcard, ← hKZ]; exact hcard)
  ·
    right
    refine ⟨?_, hcase⟩
    have hpH : p ∈ (Nat.card ↥H).primeFactors := by
      refine Nat.mem_primeFactors.2 ⟨hpprime, ?_, Nat.card_pos.ne'⟩
      rw [← hcard]
      exact Subgroup.card_dvd_of_le (le_trans hKstarP (by rw [hPP']; exact pCoreIn_le p H))
    obtain ⟨Zp, hZpset, hZpchar, hZpcard⟩ := hZfam' p hpH
    have hKZ : Kstar = Zp := by
      by_contra hne
      exact hcase (hfree p hpH Zp (hZle p Zp hZpset) hZpchar hZpcard hne)
    rw [hKZ, hZpset, hZ₀, hPP']
    ext z
    rw [mem_pTorsionSet, centreIn_eq]
    exact Iff.rfl

end CFSG.FeitThompson.Proofs

end
