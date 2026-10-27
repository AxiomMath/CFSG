module

public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.SigmaOvergroupConjugacy
import CFSG.FeitThompson.OddOrder.SigmaCentralizerTransitivity
import CFSG.FeitThompson.Local.PrimeCubeOddScalarObstruction
import CFSG.FeitThompson.Local.PrimeCubeNoncentralLineTransitivity

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson
  CFSG.FeitThompson
  CFSG.FeitThompson.Prep09

universe u

variable {G : Type*} [Group G]

theorem ne_bot_of_natCard_eq_prime {q : ℕ} (hq : q.Prime) {Q : Subgroup G}
    (hQ : Nat.card Q = q) : Q ≠ ⊥ := by
  intro h
  rw [h, Subgroup.card_bot] at hQ
  exact hq.one_lt.ne' hQ.symm

theorem isPGroup_of_natCard_eq_prime {q : ℕ} {Q : Subgroup G} (hQ : Nat.card Q = q) :
    IsPGroup q Q :=
  IsPGroup.of_card (n := 1) (by rw [hQ, pow_one])

theorem le_iff_mem_of_natCard_eq_prime [Finite G] {q : ℕ} (hq : q.Prime) {Q : Subgroup G}
    (hQ : Nat.card Q = q) {x : G} (hxQ : x ∈ Q) (hx1 : x ≠ 1) {H : Subgroup G} :
    Q ≤ H ↔ x ∈ H := by
  refine ⟨fun h => h hxQ, fun h => ?_⟩
  rw [← zpowers_eq_of_card_eq_prime hq hQ hxQ hx1, zpowers_le]
  exact h

theorem exists_mem_centralizer_conjSub_of_mem_sigmaPrimes [Finite G] [IsSimpleGroup G] {q : ℕ}
    {M : Subgroup G} (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) (hM : IsCoatom M)
    (hqM : q ∈ sigmaPrimes M) {X : Subgroup G} (hXq : IsPGroup q X) {a b : G}
    (ha : X ≤ conjSub a M) (hb : X ≤ conjSub b M) :
    ∃ c ∈ centralizer (X : Set G), conjSub c (conjSub a M) = conjSub b M := by
  rw [conjSub_eq_conj_smul] at ha hb
  obtain ⟨c, hc, hconj⟩ :=
    exists_mem_centralizer_conj_smul_of_mem_sigmaPrimes hna hodd hsolv hM hqM hXq ha hb
  refine ⟨c⁻¹, inv_mem hc, ?_⟩
  rw [conjSub_eq_conj_smul, inv_inv, conjSub_eq_conj_smul, conjSub_eq_conj_smul, ← hconj]

theorem FTS_sigma_prime_centralizer_transitivity
    (h₁ : Statements.FTS_sigma_prime_separation.{u}) :
    Statements.FTS_sigma_prime_centralizer_transitivity.{u} := by
  intro G _ _ hG q hq Q hQcard _hne M hM T hT
  obtain ⟨hMco, hMQ⟩ := hM
  obtain ⟨hTco, hTQ⟩ := hT
  have := hG.isSimpleGroup
  have hna := hG.not_isMulCommutative
  have hodd := hG.odd_natCard
  have hsolv := hG.isSolvable_of_ne_top
  obtain ⟨⟨x, hxQ⟩, hx1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.1 (ne_bot_of_natCard_eq_prime hq hQcard)
  have hx1' : x ≠ (1 : G) := fun h => hx1 (Subtype.ext h)
  have hord : orderOf x = q := orderOf_eq_of_card_eq_prime hq hQcard hxQ hx1'
  have hqM : q ∈ sigmaPrimes M := by
    refine primeFactors_orderOf_subset_sigmaPrimes (hMQ hxQ) q ?_
    rw [hord]
    exact Nat.mem_primeFactors.2 ⟨hq, dvd_rfl, hq.ne_zero⟩
  obtain ⟨g, hg, hxg⟩ : ∃ g : G, T = conjSub g M ∧ x ∈ conjSub g M := by
    have hoc := (FTS_sigma_overgroup_conjugacy h₁ G hG M hMco x (hMQ hxQ) hx1').1
    have hTmem : T ∈ sigmaSupportingMaximals (G := G) x :=
      mem_sigmaSupportingMaximals.2 ⟨hTco, hTQ hxQ⟩
    rw [hoc] at hTmem
    obtain ⟨g, hg, hx⟩ := hTmem
    exact ⟨g, hg, hg ▸ hx⟩
  have hQM : Q ≤ conjSub 1 M := by
    rw [conjSub_eq_conj_smul]; simpa using hMQ.trans (sigmaCore_le M)
  have hQT : Q ≤ conjSub g M := (le_iff_mem_of_natCard_eq_prime hq hQcard hxQ hx1').2 hxg
  obtain ⟨c, hc, hconj⟩ := exists_mem_centralizer_conjSub_of_mem_sigmaPrimes hna hodd hsolv hMco
    hqM (isPGroup_of_natCard_eq_prime hQcard) hQM hQT
  refine ⟨c, hc, ?_⟩
  rw [hg, ← hconj, conjSub_eq_conj_smul (1 : G), inv_one, map_one, one_smul]

end

end CFSG.FeitThompson.Proofs
