module

public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.SigmaNormalizerComplement
import CFSG.FeitThompson.Local.CentralizerTransitiveOnMaximalsSigmaCoreQ
import CFSG.FeitThompson.Local.SigmaOvergroupConjugacy
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.OddOrder.MaximalOvergroupExistence

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson
  CFSG.FeitThompson
  CFSG.FeitThompson.Prep09

universe u

variable {G : Type*} [Group G]

theorem centralizer_le_centralizer_of_le_zpowers {x : G} {Q : Subgroup G} (hQ : Q ≤ zpowers x) :
    centralizer ({x} : Set G) ≤ centralizer (Q : Set G) := by
  have h1 : centralizer ((zpowers x : Subgroup G) : Set G) = centralizer ({x} : Set G) := by
    rw [zpowers_eq_closure]
    exact Subgroup.centralizer_closure {x}
  rw [← h1]
  exact Subgroup.centralizer_le hQ

theorem conjSub_eq_self {N : Subgroup G} {g : G} (hg : g ∈ N) : conjSub g N = N := by
  rw [conjSub_def]
  exact map_conj_eq_self (inv_mem hg)

theorem eq_of_conjSub_eq_of_mem {M N : Subgroup G} {c : G} (hc : c ∈ N)
    (h : conjSub c M = N) : M = N := by
  have := congrArg (conjSub c⁻¹) h
  rwa [conjSub_conjSub, mul_inv_cancel, conjSub_one, conjSub_eq_self (inv_mem hc)] at this

theorem FTS_signalizer_auxiliary_base
    (h₁ : Statements.FTS_outside_sigma_plane_structure.{u})
    (h₂ : Statements.FTS_plane_maximal_overgroups.{u})
    (h₃ : Statements.FTS_sigma_prime_separation.{u}) :
    Statements.FTS_signalizer_auxiliary_base.{u} := by
  intro G _ _ hG x hx hk M hM
  have := hG.isSimpleGroup
  have hna := hG.not_isMulCommutative
  have hodd := hG.odd_natCard
  have hsolv := hG.isSolvable_of_ne_top
  obtain ⟨hMco, hxM⟩ := mem_sigmaSupportingMaximals.1 hM
  obtain ⟨-, -, -, hx1⟩ := mem_sigmaSupport.1 hx
  have hne1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.1 h)
  set q : ℕ := (orderOf x).minFac with hqdef
  have hq : q.Prime := Nat.minFac_prime hne1
  have hqdvd : q ∣ orderOf x := Nat.minFac_dvd _
  set y : G := x ^ (orderOf x / q) with hydef
  have hyord : orderOf y = q := orderOf_pow_orderOf_div (orderOf_pos x).ne' hqdvd
  set Q : Subgroup G := zpowers y with hQdef
  have hQcard : Nat.card Q = q := by rw [hQdef, Nat.card_zpowers, hyord]
  have hQx : Q ≤ zpowers x := by
    rw [hQdef, zpowers_le]; exact pow_mem (mem_zpowers x) _
  have hyQ : y ∈ Q := by rw [hQdef]; exact mem_zpowers y
  have hQM : Q ≤ sigmaCore M := hQx.trans (by rwa [zpowers_le])
  have hqM : q ∈ sigmaPrimes M := by
    refine primeFactors_orderOf_subset_sigmaPrimes (hQM hyQ) q ?_
    rw [hyord, hq.primeFactors]
    exact Finset.mem_singleton_self q
  set 𝓢 : Set (Subgroup G) := {T : Subgroup G | IsCoatom T ∧ Q ≤ sigmaCore T} with hSdef
  have hMS : M ∈ 𝓢 := ⟨hMco, hQM⟩
  obtain ⟨T, hTx, hTM⟩ : ∃ T, T ∈ sigmaSupportingMaximals (G := G) x ∧ T ≠ M :=
    Set.exists_ne_of_one_lt_ncard (by rwa [← sigmaMultiplicity_eq_ncard]) M
  obtain ⟨hTco, hxT⟩ := mem_sigmaSupportingMaximals.1 hTx
  have hTS : T ∈ 𝓢 := ⟨hTco, hQx.trans (by rwa [zpowers_le])⟩
  have htrans := FTS_sigma_prime_centralizer_transitivity h₃ G hG q hq Q hQcard ⟨M, hMS⟩
  have hCnotM : ¬ centralizer (Q : Set G) ≤ M := by
    intro hle
    obtain ⟨c, hc, hconj⟩ := htrans M hMS T hTS
    exact hTM (by rw [← hconj, conjSub_eq_self (hle hc)])
  have hQbot : Q ≠ ⊥ := ne_bot_of_natCard_eq_prime hq hQcard
  have hnorm : normalizer (Q : Set G) ≠ ⊤ :=
    (normalizer_lt_top_of_isPGroup hna hq hQbot (isPGroup_of_natCard_eq_prime hQcard)).ne
  obtain ⟨N, hNco, hNQ⟩ := exists_isCoatom_ge_of_ne_top hnorm
  have hCN : centralizer (Q : Set G) ≤ N := (Subgroup.centralizer_le_normalizer _).trans hNQ
  have hNM : N ≠ M := fun h => hCnotM (h ▸ hCN)
  have hCxN : centralizer ({x} : Set G) ≤ N :=
    (centralizer_le_centralizer_of_le_zpowers hQx).trans hCN
  have hxN : x ∈ N := hCxN (mem_centralizer_iff.2 (by simp))
  have hyN : y ∈ N := hNQ (le_normalizer hyQ)
  have hqN : q ∉ sigmaPrimes N := by
    intro hqN
    have hyS : y ∈ sigmaCore N := by
      refine mem_sigmaCore_of_primeFactors_orderOf hna hodd hsolv hNco hyN ?_
      intro p hp
      rw [hyord, hq.primeFactors, Finset.mem_singleton] at hp
      rwa [hp]
    have hNS : N ∈ 𝓢 := ⟨hNco, by rw [hQdef, zpowers_le]; exact hyS⟩
    obtain ⟨c, hc, hconj⟩ := htrans M hMS N hNS
    exact hNM (eq_of_conjSub_eq_of_mem (hCN hc) hconj).symm
  obtain ⟨-, -, hsemi⟩ := FTS_sigma_normalizer_complement h₁ h₂ G hG M N hMco hNco hNM.symm q hqM
    Q (hQM.trans (sigmaCore_le M)) hQcard hNQ hqN
  have hsep : sigmaPrimes N ∩ sigmaPrimes M = ∅ := by
    refine h₃ G hG N M hNco hMco ?_
    intro g hgeq
    exact hqN (by rw [← sigmaPrimes_conjSub g N, ← hgeq]; exact hqM)
  exact ⟨q, hq, hqdvd, Q, hQx, hQcard, N, hNco, hNM, hNQ, hCxN,
    Subgroup.mem_inf.2 ⟨sigmaCore_le M hxM, hxN⟩, hsemi, hsep⟩

end

end CFSG.FeitThompson.Proofs
