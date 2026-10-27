module

public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.SigmaCoreNormalHallDerived
import CFSG.FeitThompson.Local.PrimeFreeFactorizationFixedSubgroupTransport
import CFSG.FeitThompson.OddOrder.SigmaPrimesWellDefined
import CFSG.FeitThompson.OddOrder.SigmaCentralizerTransitivity

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson
  CFSG.FeitThompson
  CFSG.FeitThompson.Prep09

universe u

variable {G : Type*} [Group G]

theorem conjSub_eq_conj_smul (g : G) (M : Subgroup G) : conjSub g M = MulAut.conj g⁻¹ • M := rfl

theorem conjSub_conjSub (g a : G) (M : Subgroup G) :
    conjSub g (conjSub a M) = conjSub (a * g) M := by
  ext y; simp [mul_assoc]

theorem isCoatom_conjSub {M : Subgroup G} (hM : IsCoatom M) (g : G) : IsCoatom (conjSub g M) :=
  conjSub_eq_conj_smul g M ▸ isCoatom_conj_smul hM g⁻¹

theorem sigmaPrimes_conjSub [Finite G] (g : G) (M : Subgroup G) :
    sigmaPrimes (conjSub g M) = sigmaPrimes M := by
  rw [conjSub_eq_conj_smul, sigmaPrimes_conj_smul]

theorem primeFactors_orderOf_subset_sigmaPrimes [Finite G] {M : Subgroup G} {x : G}
    (hx : x ∈ sigmaCore M) : ∀ p ∈ (orderOf x).primeFactors, p ∈ sigmaPrimes M := fun p hp =>
  isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) p
    (Nat.primeFactors_mono ((sigmaCore M).orderOf_dvd_natCard hx) Nat.card_pos.ne' hp)

theorem mem_sigmaCore_of_primeFactors_orderOf [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) {M : Subgroup G} (hM : IsCoatom M)
    {y : G} (hy : y ∈ M) (h : ∀ p ∈ (orderOf y).primeFactors, p ∈ sigmaPrimes M) :
    y ∈ sigmaCore M := by
  have hHall := (isHallSubgroup_subgroupOf_sigmaCore hna hodd hsolv hM).isHallPiSubgroup
  have key := hHall.mem_iff (⟨y, hy⟩ : M)
  rw [mem_subgroupOf] at key
  exact key.2 (by simpa [orderOf_coe] using h)

theorem mem_sigmaCore_iff_primeFactors_orderOf [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) {M : Subgroup G} (hM : IsCoatom M)
    {y : G} (hy : y ∈ M) :
    y ∈ sigmaCore M ↔ ∀ p ∈ (orderOf y).primeFactors, p ∈ sigmaPrimes M :=
  ⟨primeFactors_orderOf_subset_sigmaPrimes,
    mem_sigmaCore_of_primeFactors_orderOf hna hodd hsolv hM hy⟩

theorem FTS_sigma_overgroup_conjugacy
    (h₁ : Statements.FTS_sigma_prime_separation.{u}) :
    Statements.FTS_sigma_overgroup_conjugacy.{u} := by
  intro G _ _ hG M hM x hxM hx1
  have := hG.isSimpleGroup
  have hna := hG.not_isMulCommutative
  have hodd := hG.odd_natCard
  have hsolv := hG.isSolvable_of_ne_top
  obtain ⟨q, hq⟩ : (orderOf x).primeFactors.Nonempty := by
    rw [Nat.nonempty_primeFactors]
    have h0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
    have h1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.1 h)
    omega
  have hconj : ∀ N : Subgroup G, IsCoatom N → x ∈ sigmaCore N → ∃ g : G, N = conjSub g M := by
    intro N hN hxN
    by_contra hcon
    have hsep := h₁ G hG M N hM hN fun g h => hcon ⟨g, h⟩
    have hmem : q ∈ sigmaPrimes M ∩ sigmaPrimes N :=
      ⟨primeFactors_orderOf_subset_sigmaPrimes hxM q hq,
        primeFactors_orderOf_subset_sigmaPrimes hxN q hq⟩
    rw [hsep] at hmem
    exact hmem
  refine ⟨?_, ?_⟩
  · ext N
    simp only [mem_sigmaSupportingMaximals, Set.mem_ofPred]
    refine ⟨fun h => ?_, ?_⟩
    · obtain ⟨g, hg⟩ := hconj N h.1 h.2
      exact ⟨g, hg, sigmaCore_le N h.2⟩
    ·
      rintro ⟨g, rfl, hxN⟩
      refine ⟨isCoatom_conjSub hM g,
        mem_sigmaCore_of_primeFactors_orderOf hna hodd hsolv (isCoatom_conjSub hM g) hxN ?_⟩
      rw [sigmaPrimes_conjSub]
      exact primeFactors_orderOf_subset_sigmaPrimes hxM
  · intro N hN T hT
    rw [mem_sigmaSupportingMaximals] at hN hT
    obtain ⟨a, ha⟩ := hconj N hN.1 hN.2
    obtain ⟨b, hb⟩ := hconj T hT.1 hT.2
    exact ⟨a⁻¹ * b, by rw [ha, hb, conjSub_conjSub, mul_inv_cancel_left]⟩

end

end CFSG.FeitThompson.Proofs
