module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.OverlapKappaExceptionalPrimeCube
import CFSG.FeitThompson.Local.LocalTypeIAlternative
import CFSG.FeitThompson.Local.OddCoprimeCyclicAutPrimeCube
import CFSG.FeitThompson.Local.ElementaryAbelianCubeInvariantPlane
import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib
import CFSG.FeitThompson.Local.PCubeCentralTrivialActionInner

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup _root_.CFSG.FeitThompson

namespace LocalPTrivialU

variable {G : Type*} [Group G]

theorem eq_bot_of_isHallPiSubgroup_subgroupOf_empty [Finite G] {A E : Subgroup G} (hle : A ≤ E)
    (h : IsHallPiSubgroup (∅ : Set ℕ) (A.subgroupOf E)) : A = ⊥ := by
  have hcard : Nat.card ↥(A.subgroupOf E) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hpf : (Nat.card ↥A).primeFactors = ∅ := by
    ext q
    simp only [Finset.notMem_empty, iff_false]
    intro hq
    exact isPiSubgroup_iff.1 h.isPiSubgroup q (by rw [hcard]; exact hq)
  rcases Nat.primeFactors_eq_empty.1 hpf with h0 | h1
  · exact absurd h0 Nat.card_pos.ne'
  · exact Subgroup.card_eq_one.1 h1

theorem injective_conjOnNormalized_of_faithful {K P : Subgroup G}
    (hKnP : K ≤ normalizer (P : Set G)) (hfaith : ∀ k ∈ K, (∀ x ∈ P, k⁻¹ * x * k = x) → k = 1) :
    Function.Injective (conjOnNormalized P hKnP) := by
  rw [injective_iff_map_eq_one]
  intro b hb
  have hb1 : (b : G) = 1 := by
    refine hfaith (b : G) b.2 fun x hx => ?_
    have h1 := congrArg (fun (f : MulAut ↥P) => ((f ⟨x, hx⟩ : ↥P) : G)) hb
    have h2 : (b : G) * x * (b : G)⁻¹ = x := by
      simpa [conjOnNormalized_apply_coe] using h1
    have hc : (b : G) * x = x * (b : G) := mul_inv_eq_iff_eq_mul.mp h2
    rw [mul_assoc, ← hc, inv_mul_cancel_left]
  exact Subtype.ext (by simpa using hb1)

end LocalPTrivialU

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup CFSG.FeitThompson CFSG.FeitThompson.LocalPTrivialU
  CFSG.FeitThompson

universe u

theorem FBG_local_p_trivial_U_alternative
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_abelian_fitting_overlap_rank_two.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_local_nilpotent_hall_core.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FBG_nonabelian_fitting_overlap_central_lines.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FBG_nonabelian_fitting_overlap_maximal_plane.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FBG_overlap_kappa_fixed_line_order_position.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_trivial_residual_prime_fixed_core.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FBG_local_p_trivial_U_alternative.{u} := by
  intro G _ _ hG M K U hsetup hK hU hHS
  obtain ⟨⟨hHbot, -, -, -, -, -, -⟩, -⟩ := h₂ G hG M K U hsetup
  by_cases hTI : IsTIWithNormalizer (sharp (hallCoreIn M)) M
  · exact Or.inl hTI
  have hg : ∃ g : G, g ∉ M ∧
      ¬ Disjoint (sharp (hallCoreIn M)) (MulAut.conj g '' sharp (hallCoreIn M)) := by
    by_contra hc
    refine hTI ⟨sharp_nonempty_iff.2 hHbot.ne', one_notMem_sharp _,
      normalizer_sharp_hallCoreIn_eq hG hsetup.isCoatom hHbot.ne', fun g hgM => ?_⟩
    by_contra hdis
    exact hc ⟨g, hgM, hdis⟩
  obtain ⟨g, hgM, hd⟩ := hg
  obtain ⟨X, hX⟩ := exists_isFittingOverlapSetup_of_not_disjoint hsetup.isCoatom hgM hd
  have hnabH : ¬ IsMulCommutative ↥(hallCoreIn M) := by
    intro habel
    have hκ := (h₁ G hG M X g⁻¹ hX habel).2
    exact hK (eq_bot_of_isHallPiSubgroup_subgroupOf_empty hsetup.le_M_K (hκ ▸ hsetup.hall_K))
  obtain ⟨hXprime, hcyc, -⟩ := h₃ G hG M X g⁻¹ hX hnabH
  have _fin : Fintype G := Fintype.ofFinite G
  have hG2 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hsemi : FreeCore.IsInternalSemidirectProduct M (hallCoreIn M) K := by
    have h := hsetup.semidirect_M
    rw [hU, bot_sup_eq] at h
    rw [hHS]
    exact h
  have hXeq : X = CFSG.FeitThompson.fittingIn M ⊓ conjSubgroup (CFSG.FeitThompson.fittingIn M) g⁻¹ := by
    rw [CFSG.FeitThompson.fittingIn_eq_mixedFitting]; exact hX.eq
  have hKhall : IsHallPiSubgroupOf (kappaPrimes M) K M := ⟨hsetup.le_M_K, hsetup.hall_K⟩
  have hginv : g⁻¹ ∉ M := fun hc => hgM (by simpa using M.inv_mem hc)
  set p : ℕ := Nat.card ↥X with hpdef
  set P : Subgroup G := _root_.CFSG.FeitThompson.pCoreIn p (hallCoreIn M) with hPdef
  have hPbridge : P = CFSG.FeitThompson.pCoreIn p (hallCoreIn M) :=
    rfl
  obtain ⟨-, hKcyc, hKstarCard, hKstarLeP, halt⟩ :=
    h₅ G hG2 M hsetup.isCoatom g⁻¹ hginv X hXeq hX.ne_bot
      (hallCoreIn M) rfl hnabH K hK hKhall hHS hsemi p rfl P hPbridge _ rfl _ rfl
  have hpdvdP : p ∣ Nat.card ↥P := by
    have h := Subgroup.card_dvd_of_le hKstarLeP
    rwa [hKstarCard] at h
  have hpmemH : p ∈ (Nat.card ↥(hallCoreIn M)).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hXprime,
      hpdvdP.trans (Subgroup.card_dvd_of_le
        (_root_.CFSG.FeitThompson.pCoreIn_le p (hallCoreIn M))),
      Nat.card_pos.ne'⟩
  rcases halt with hall | ⟨hCZ, hKnd⟩
  ·
    exact Or.inr (Or.inl ⟨p, hpmemH, hcyc, hall _ hpmemH⟩)
  obtain ⟨-, hpodd, -, -, -, hPcard, hPexp, hfaith, hcop, hKfix⟩ :=
    FBG_overlap_kappa_exceptional_prime_cube h₄ h₅ h₆ h₇ G hG2 M hsetup.isCoatom g⁻¹ hginv X hXeq
      hX.ne_bot (hallCoreIn M) rfl hnabH K hK hKhall hHS hsemi p rfl P hPbridge _ rfl hCZ hKnd
  have hpmemX : p ∈ (Nat.card ↥X).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hXprime, dvd_rfl, hXprime.pos.ne'⟩
  obtain ⟨hPnab, -⟩ := h₄ G hG M X g⁻¹ hX hnabH p hpmemX X le_rfl rfl
  have hKnH : K ≤ normalizer ((hallCoreIn M : Subgroup G) : Set G) :=
    hsetup.le_M_K.trans hsemi.le_normalizer
  have hKnP : K ≤ normalizer (P : Set G) :=
    _root_.CFSG.FeitThompson.le_normalizer_pCoreIn p hKnH
  set ρ : ↥K →* MulAut ↥P := conjOnNormalized P hKnP with hρdef
  have hρinj : Function.Injective ρ := injective_conjOnNormalized_of_faithful hKnP hfaith
  have hAcard : Nat.card ↥ρ.range = Nat.card ↥K := by
    rw [ρ.range_eq_map, Subgroup.card_map_of_injective (f := ρ) hρinj, Subgroup.card_top]
  have hAcyc : IsCyclic ↥ρ.range :=
    isCyclic_of_surjective (hH := hKcyc) ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hAodd : Odd (Nat.card ↥ρ.range) := by
    rw [hAcard]
    exact Odd.of_dvd_nat hG.odd_natCard (Subgroup.card_subgroup_dvd_card K)
  have hAfix : ∀ a ∈ ρ.range, ∀ z ∈ center ↥P, (a : MulAut ↥P) z = z := by
    intro a ha z hz
    obtain ⟨k, rfl⟩ := ha
    have hzc : (z : G) ∈ P ⊓ centralizer (P : Set G) := by
      refine Subgroup.mem_inf.2 ⟨z.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
      have h := Subgroup.mem_center_iff.1 hz ⟨y, hy⟩
      exact congrArg (fun w : ↥P => (w : G)) h
    have hcomm := hKfix (k : G) k.2 (z : G) hzc
    apply Subtype.ext
    rw [hρdef, conjOnNormalized_apply_coe]
    have hzk : (k : G) * (z : G) = (z : G) * (k : G) := by
      calc (k : G) * (z : G) = (k : G) * ((k : G)⁻¹ * (z : G) * (k : G)) := by rw [hcomm]
        _ = (z : G) * (k : G) := by group
    rw [hzk, mul_inv_cancel_right]
  have hdvd := natCard_dvd_sub_one_or_natCard_dvd_add_one_of_cyclic_odd_coprime
    (p := p) (P := ↥P) hXprime hpodd hPcard hPnab
    (fun x => Subtype.ext (by simpa using hPexp (x : G) x.2))
    hAcyc hAodd (by rw [hAcard]; exact hcop) hAfix
  rw [hAcard] at hdvd
  rcases hdvd with h | h
  · exact absurd h hKnd
  exact Or.inr (Or.inr ⟨p, hpmemH, hcyc, hPcard, h⟩)

end

end CFSG.FeitThompson.Proofs
