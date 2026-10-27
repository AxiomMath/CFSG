module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
import CFSG.FeitThompson.Local.SigmaCoreNormalHallDerived
import CFSG.FeitThompson.Local.MixedFittingCentralizerConstrained
import CFSG.FeitThompson.Local.KappaPrimeLineFixedEquivalence
import CFSG.FeitThompson.Foundations.LiftHallByNormalComplement
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Presheaf

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise CFSG.FeitThompson.Prep03

variable {G : Type*} [Group G]

theorem coprime_natCard_of_primeFactors_disjoint [Finite G] {H L : Subgroup G} {π ρ : Set ℕ}
    (hH : ∀ r ∈ (Nat.card ↥H).primeFactors, r ∈ π)
    (hL : ∀ r ∈ (Nat.card ↥L).primeFactors, r ∈ ρ) (hdisj : ∀ r ∈ π, r ∉ ρ) :
    (Nat.card ↥H).Coprime (Nat.card ↥L) := by
  by_contra hc
  obtain ⟨p, hp, hpH, hpL⟩ := Nat.Prime.not_coprime_iff_dvd.1 hc
  exact hdisj p (hH p (Nat.mem_primeFactors.2 ⟨hp, hpH, Nat.card_pos.ne'⟩))
    (hL p (Nat.mem_primeFactors.2 ⟨hp, hpL, Nat.card_pos.ne'⟩))

theorem natCard_of_isSemidirect [Finite G] {X Y W : Subgroup G} (h : IsSemidirect X Y W) :
    Nat.card ↥X = Nat.card ↥Y * Nat.card ↥W :=
  natCard_eq_mul_of_mul_eq_of_inf_eq_bot
    (by rw [← coe_mul_of_right_le_normalizer_left Y W (h.2.1.trans h.2.2.1), h.2.2.2.1])
    h.2.2.2.2

theorem le_normalizer_sup_of_isSemidirect {M N U K : Subgroup G}
    (h : IsSemidirect M N (U ⊔ K)) (hE : IsSemidirect (U ⊔ K) U K) :
    M ≤ normalizer ((N ⊔ U : Subgroup G) : Set G) := by
  intro m hm
  have hUKnN : U ⊔ K ≤ normalizer (N : Set G) := h.2.1.trans h.2.2.1
  have hmem : m ∈ (M : Set G) := hm
  rw [← h.2.2.2.1, coe_mul_of_right_le_normalizer_left N (U ⊔ K) hUKnN] at hmem
  obtain ⟨n, hn, e, he, hne⟩ := hmem
  subst hne
  exact mul_mem (le_normalizer ((le_sup_left : N ≤ N ⊔ U) hn))
    (normalizer_inf_normalizer_le_normalizer_sup N U ⟨hUKnN he, hE.2.2.1 he⟩)

theorem inf_eq_bot_of_isSemidirect {M N U K : Subgroup G}
    (h : IsSemidirect M N (U ⊔ K)) (hE : IsSemidirect (U ⊔ K) U K) :
    (N ⊔ U) ⊓ K = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxNU : x ∈ N ⊔ U := hx.1
  have hxK : x ∈ K := hx.2
  have hcoe : x ∈ ((N ⊔ U : Subgroup G) : Set G) := hxNU
  rw [coe_mul_of_right_le_normalizer_left N U
    ((le_sup_left.trans h.2.1).trans h.2.2.1)] at hcoe
  obtain ⟨n, hn, u, hu, hxeq⟩ := hcoe
  have hnN : n ∈ N := hn
  have huU : u ∈ U := hu
  have hxeq' : n * u = x := hxeq
  have hu' : u ∈ (U ⊔ K : Subgroup G) := Subgroup.mem_sup_left huU
  have hxUK : x ∈ (U ⊔ K : Subgroup G) := Subgroup.mem_sup_right hxK
  have hn' : n ∈ N ⊓ (U ⊔ K) := by
    refine ⟨hnN, ?_⟩
    have hne : n = x * u⁻¹ := by rw [← hxeq']; group
    rw [hne]
    exact Subgroup.mul_mem _ hxUK (Subgroup.inv_mem _ hu')
  rw [h.2.2.2.2, mem_bot] at hn'
  have hxu : x = u := by rw [← hxeq', hn', one_mul]
  have hmem : u ∈ U ⊓ K := ⟨huU, hxu ▸ hxK⟩
  rw [hE.2.2.2.2, mem_bot] at hmem
  simp [hxu, hmem]

theorem isSemidirect_sup_complement {M N U K : Subgroup G}
    (h : IsSemidirect M N (U ⊔ K)) (hE : IsSemidirect (U ⊔ K) U K) :
    IsSemidirect M (N ⊔ U) K :=
  ⟨sup_le h.1 (hE.1.trans h.2.1), hE.2.1.trans h.2.1,
    le_normalizer_sup_of_isSemidirect h hE,
    by rw [sup_assoc, h.2.2.2.1], inf_eq_bot_of_isSemidirect h hE⟩

theorem commutator_le_of_sup_eq_of_isCyclic {M D K : Subgroup G} [IsCyclic ↥K]
    (hnorm : M ≤ normalizer (D : Set G)) (hsup : D ⊔ K = M) : ⁅M, M⁆ ≤ D := by
  have hDM : D ≤ M := le_sup_left.trans hsup.le
  have hKM : K ≤ M := le_sup_right.trans hsup.le
  have : (D.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hnorm
  have : IsCyclic ↥(K.subgroupOf M) := (subgroupOfEquivOfLe hKM).isCyclic.2 ‹_›
  have h := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
    (N := D.subgroupOf M) (H := K.subgroupOf M)
    (by rw [← subgroupOf_sup hDM hKM, hsup, subgroupOf_self]) IsCyclic.isMulCommutative
  calc (⁅M, M⁆ : Subgroup G) = map M.subtype (_root_.commutator ↥M) :=
        (map_subtype_commutator M).symm
    _ ≤ map M.subtype (D.subgroupOf M) := map_mono h
    _ = D := map_subgroupOf_eq_of_le hDM

theorem natCard_mul_relIndex_of_le [Finite G] {H L : Subgroup G} (h : H ≤ L) :
    Nat.card ↥H * H.relIndex L = Nat.card ↥L := by
  have hidx := Subgroup.card_mul_index (G := L) (H.subgroupOf L)
  rwa [← Subgroup.card_subtype L (H.subgroupOf L), Subgroup.map_subgroupOf_eq_of_le h] at hidx

theorem natCard_commutator_eq_relIndex [Finite G] {M K : Subgroup G} (hKM : K ≤ M)
    (hmain : IsSemidirect M (⁅M, M⁆ : Subgroup G) K) :
    Nat.card (⁅M, M⁆ : Subgroup G) = K.relIndex M := by
  refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥K)) ?_
  rw [← natCard_of_isSemidirect hmain, ← natCard_mul_relIndex_of_le hKM]
  ring

theorem kappaPrimes_eq_tau1Primes_of_isSemidirect_commutator [Finite G] {M K : Subgroup G}
    (hHall : IsHallPiOf (kappaPrimes M) K M)
    (hmain : IsSemidirect M (⁅M, M⁆ : Subgroup G) K) :
    kappaPrimes M = tau1Primes M := by
  have hcard := natCard_of_isSemidirect hmain
  have hM' := natCard_commutator_eq_relIndex hHall.1 hmain
  ext p
  constructor
  · intro hp
    obtain ⟨hprime, hdM, hσ, S, hScyc, -⟩ := mem_kappaPrimes_iff.1 hp
    refine mem_tau1Primes_iff.2 ⟨hprime, hdM, hσ,
      elementaryAbelianPRank_eq_one_of_isCyclic_sylow hprime hdM ⟨S, hScyc⟩, ?_⟩
    intro hdvd
    refine hHall.2.2 p (Nat.mem_primeFactors.2 ⟨hprime, hM' ▸ hdvd, ?_⟩) hp
    rw [← hM']
    exact (Nat.card_pos (α := ↥(⁅M, M⁆ : Subgroup G))).ne'
  · intro hp
    obtain ⟨hprime, hdM, -, -, hnd⟩ := mem_tau1Primes_iff.1 hp
    have hpK : p ∣ Nat.card ↥K := by
      rw [hcard] at hdM
      exact Nat.Coprime.dvd_of_dvd_mul_left ((Nat.Prime.coprime_iff_not_dvd hprime).2 hnd) hdM
    exact hHall.2.1 p (Nat.mem_primeFactors.2 ⟨hprime, hpK, (Nat.card_pos (α := ↥K)).ne'⟩)

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup Pointwise CFSG.FeitThompson
open CFSG.FeitThompson.Prep03

universe u

theorem FNI_kappa_derived_complement (h₁ : Statements.FNI_kappa_local_pair.{u})
    (h₂ : Statements.FNI_kappa_semiprime_complement_existence.{u}) :
    Statements.FNI_kappa_derived_complement.{u} := by
  intro G _ _ M K A Z hsetup
  have hamb := hsetup.ambient
  have hsimple := hamb.isSimpleGroup
  have hM := hsetup.isCoatom
  have hMtop : M ≠ ⊤ := hM.1
  obtain ⟨Mstar, -, -, -, -, -, -, hdirect, hZcyc, -⟩ := h₁ G M K A Z hsetup
  have hKcyc : IsCyclic ↥K := Subgroup.isCyclic_of_le hdirect.1
  obtain ⟨hKbot, U₀, E₁, hU₀ab, hU₀hall, hdec, hdecE, -, -, -, -, -, -, hfree⟩ :=
    h₂ G hamb M K hM hsetup.kappa_nonempty hsetup.isHall_K
  have hKM : K ≤ M := hsetup.isHall_K.1
  have hU₀M : U₀ ≤ M := hU₀hall.1
  have hsplit : IsSemidirect M (sigmaCore M ⊔ U₀) K := isSemidirect_sup_complement hdec hdecE
  have hcommle : (⁅M, M⁆ : Subgroup G) ≤ sigmaCore M ⊔ U₀ :=
    commutator_le_of_sup_eq_of_isCyclic hsplit.2.2.1 hsplit.2.2.2.1
  have hSle : sigmaCore M ≤ (⁅M, M⁆ : Subgroup G) :=
    sigmaCore_le_commutator hamb.not_isMulCommutative hamb.odd_natCard hamb.forall_isSolvable hM
  have hKne : K ≠ ⊤ := fun h => hMtop (top_le_iff.1 (h ▸ hKM))
  have hU₀ne : U₀ ≠ ⊤ := fun h => hMtop (top_le_iff.1 (h ▸ hU₀M))
  have hKsolv : Group.IsSolvable ↥K := hamb.forall_isSolvable K hKne
  have hU₀solv : Group.IsSolvable ↥U₀ := hamb.forall_isSolvable U₀ hU₀ne
  have hKnormU₀ : K ≤ normalizer ((U₀ : Subgroup G) : Set G) := hdecE.2.1.trans hdecE.2.2.1
  have hcop : (Nat.card ↥K).Coprime (Nat.card ↥U₀) :=
    coprime_natCard_of_primeFactors_disjoint hsetup.isHall_K.2.1 hU₀hall.2.1
      (fun r hr hr' => hr' (Or.inr hr))
  have hfix : U₀ ⊓ centralizer ((K : Subgroup G) : Set G) = ⊥ := by
    obtain ⟨k, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hKbot
    refine le_antisymm ?_ bot_le
    have h := hfree (k : G) k.2 (by simpa using hk1)
    exact le_trans (inf_le_inf_left U₀ (Subgroup.centralizer_le
      (Set.singleton_subset_iff.2 k.2))) h.le
  have hU₀le : U₀ ≤ (⁅M, M⁆ : Subgroup G) :=
    (le_commutator_of_coprime_of_inf_centralizer_eq_bot hKnormU₀ hcop hfix).trans
      (commutator_mono hU₀M hKM)
  have hcommeq : (⁅M, M⁆ : Subgroup G) = sigmaCore M ⊔ U₀ :=
    le_antisymm hcommle (sup_le hSle hU₀le)
  have hmain : IsSemidirect M (⁅M, M⁆ : Subgroup G) K := hcommeq ▸ hsplit
  refine ⟨hmain, kappaPrimes_eq_tau1Primes_of_isSemidirect_commutator hsetup.isHall_K hmain, ?_⟩
  intro U hdecU hdecEU
  have hsplitU : IsSemidirect M (sigmaCore M ⊔ U) K := isSemidirect_sup_complement hdecU hdecEU
  have hle : (⁅M, M⁆ : Subgroup G) ≤ sigmaCore M ⊔ U :=
    commutator_le_of_sup_eq_of_isCyclic hsplitU.2.2.1 hsplitU.2.2.2.1
  have hcards : Nat.card ↥(sigmaCore M ⊔ U) = Nat.card (⁅M, M⁆ : Subgroup G) := by
    refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥K)) ?_
    rw [← natCard_of_isSemidirect hsplitU, ← natCard_of_isSemidirect hmain]
  exact Subgroup.eq_of_le_of_card_ge hle hcards.le

end CFSG.FeitThompson.Proofs

end
