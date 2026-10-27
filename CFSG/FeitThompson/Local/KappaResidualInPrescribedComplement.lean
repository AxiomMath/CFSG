module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
import CFSG.FeitThompson.Local.SigmaCoreNormalHallDerived
import CFSG.FeitThompson.Foundations.SolvableHallExistence
import CFSG.FeitThompson.Foundations.SolvableHallConjugacy
import CFSG.FeitThompson.Local.PrimeCentralizerAbelianCommutatorConjugates
import CFSG.FeitThompson.Local.PrimeFreeFactorizationFixedSubgroupTransport
import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction
import CFSG.FeitThompson.Representations.ConjugationTransportsDadeSignalizers
public import Mathlib.Topology.Sheaves.Presheaf

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G : Type*} [Group G] {π π' : Set ℕ} {H A B X Y N S E : Subgroup G}

theorem eq_of_subgroupOf_eq (hX : X ≤ H) (hY : Y ≤ H)
    (h : X.subgroupOf H = Y.subgroupOf H) : X = Y := by
  have h' := congrArg (Subgroup.map H.subtype) h
  rwa [Subgroup.map_subgroupOf_eq_of_le hX, Subgroup.map_subgroupOf_eq_of_le hY] at h'

theorem isInternalSemidirectProduct_conj_smul
    (h : FreeCore.IsInternalSemidirectProduct X A B) (g : G) :
    FreeCore.IsInternalSemidirectProduct (MulAut.conj g • X) (MulAut.conj g • A)
      (MulAut.conj g • B) where
  sup_eq := by rw [← Subgroup.smul_sup, h.sup_eq]
  le_normalizer := conj_smul_le_normalizer_conj_smul g h.le_normalizer
  disjoint := by
    rw [disjoint_iff, ← Subgroup.smul_inf, ← Subgroup.smul_bot (MulAut.conj g),
      disjoint_iff.1 h.disjoint]

theorem isHallPiSubgroup_conj_smul {L : Type*} [Group L] [Finite L] {A : Subgroup L}
    (h : IsHallPiSubgroup π A) (g : L) : IsHallPiSubgroup π (MulAut.conj g • A) := by
  refine ⟨isPiSubgroup_iff.2 fun p hp => isPiSubgroup_iff.1 h.isPiSubgroup p ?_,
    fun p hp => h.notMem_of_mem_primeFactors_index p ?_⟩
  · rwa [natCard_conj_smul] at hp
  · rwa [index_conj_pointwise_smul] at hp

theorem isHallPiSubgroupOf_conj_smul [Finite G] (h : CFSG.FeitThompson.IsHallPiSubgroupOf π X N)
    {n : G} (hn : n ∈ N) : CFSG.FeitThompson.IsHallPiSubgroupOf π (MulAut.conj n • X) N := by
  refine ⟨Subgroup.conj_smul_le_of_le h.1 ⟨n, hn⟩, ?_⟩
  rw [← Subgroup.conj_smul_subgroupOf h.1 ⟨n, hn⟩]
  exact isHallPiSubgroup_conj_smul h.2 _

theorem isHallPiSubgroupOf_of_isHallPiOf [Finite G]
    (h : CFSG.FeitThompson.Prep03.IsHallPiOf π X N)
    (hπ : ∀ r : ℕ, r.Prime → (r ∈ π ↔ r ∈ π')) : CFSG.FeitThompson.IsHallPiSubgroupOf π' X N := by
  refine ⟨h.1, isPiSubgroup_iff.2 fun p hp => ?_, fun p hp hp' => ?_⟩
  · rw [natCard_subgroupOf h.1] at hp
    exact (hπ p (Nat.prime_of_mem_primeFactors hp)).1 (h.2.1 p hp)
  · exact h.2.2 p hp ((hπ p (Nat.prime_of_mem_primeFactors hp)).2 hp')

theorem isHallPiOf_of_isHallSubgroup_subgroupOf [Finite G]
    (hX : X ≤ N) (h : IsHallSubgroup π (X.subgroupOf N)) :
    CFSG.FeitThompson.Prep03.IsHallPiOf π X N := by
  refine ⟨hX, fun r hr => isPiNumber_iff.1 h.natCard r ?_,
    fun r hr => isPiNumber_iff.1 h.index r hr⟩
  rwa [natCard_subgroupOf hX]

theorem isHallSubgroup_subgroupOf_of_isInternalSemidirectProduct [Finite G]
    (hS : IsHallSubgroup π (S.subgroupOf N))
    (hSE : FreeCore.IsInternalSemidirectProduct N S E) :
    IsHallSubgroup πᶜ (E.subgroupOf N) := by
  have hcard : Nat.card ↥N = Nat.card ↥S * Nat.card ↥E := hSE.natCard_eq_mul
  have hcS : Nat.card ↥(S.subgroupOf N) = Nat.card ↥S := natCard_subgroupOf hSE.left_le
  have hcE : Nat.card ↥(E.subgroupOf N) = Nat.card ↥E := natCard_subgroupOf hSE.right_le
  have hiS : (S.subgroupOf N).index = Nat.card ↥E := by
    have h := Subgroup.card_mul_index (S.subgroupOf N)
    rw [hcS] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h.trans hcard)
  have hiE : (E.subgroupOf N).index = Nat.card ↥S := by
    have h := Subgroup.card_mul_index (E.subgroupOf N)
    rw [hcE] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h.trans (hcard.trans (Nat.mul_comm _ _)))
  exact ⟨by rw [hcE, ← hiS]; exact hS.index, by rw [hiE, compl_compl, ← hcS]; exact hS.natCard⟩

theorem isInternalSemidirectProduct_of_isSemidirect
    (h : CFSG.FeitThompson.Prep03.IsSemidirect X A B) :
    FreeCore.IsInternalSemidirectProduct X A B :=
  ⟨h.2.2.2.1, h.2.2.1, disjoint_iff.2 h.2.2.2.2⟩

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup Pointwise CFSG.FeitThompson
open CFSG.FeitThompson

universe u

theorem FTS_kappa_residual_in_prescribed_complement
    (h₁ : Statements.FNI_kappa_semiprime_complement_existence.{u}) :
    Statements.FTS_kappa_residual_in_prescribed_complement.{u} := by
  intro G _ _ hG N hN hκ E hEN hNE
  have : Fintype G := Fintype.ofFinite G
  have hamb : Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hNco : IsCoatom N := hN
  have hsolvN : Group.IsSolvable ↥N := hG.isSolvable N hNco.1
  have hsimple := hG.isSimpleGroup
  have hS : IsHallSubgroup (sigmaPrimes N) ((sigmaCore N).subgroupOf N) :=
    isHallSubgroup_subgroupOf_sigmaCore hG.not_isMulCommutative hG.odd_natCard hG.isSolvable hNco
  obtain ⟨K', hK'⟩ := exists_isHallSubgroup (X := ↥N) (kappaPrimes N)
  set K₀ : Subgroup G := K'.map N.subtype with hK₀def
  have hK₀N : K₀ ≤ N := map_subtype_le _
  have hK₀sub : K₀.subgroupOf N = K' :=
    comap_map_eq_self_of_injective N.subtype_injective K'
  have hK₀hall : IsHallSubgroup (kappaPrimes N) (K₀.subgroupOf N) := hK₀sub ▸ hK'
  have hK₀pi : Prep03.IsHallPiOf (kappaPrimes N) K₀ N :=
    isHallPiOf_of_isHallSubgroup_subgroupOf hK₀N hK₀hall
  obtain ⟨-, U₀, E₁, hU₀comm, hU₀hall, hsemi1, hsemi2, -, -, -, -, -, -, hfree⟩ :=
    h₁ G hamb N K₀ hNco hκ hK₀pi
  have hNE₀ : FreeCore.IsInternalSemidirectProduct N (sigmaCore N) (U₀ ⊔ K₀) :=
    isInternalSemidirectProduct_of_isSemidirect hsemi1
  have hE₀split : FreeCore.IsInternalSemidirectProduct (U₀ ⊔ K₀) U₀ K₀ :=
    isInternalSemidirectProduct_of_isSemidirect hsemi2
  have hE₀N : U₀ ⊔ K₀ ≤ N := hNE₀.right_le
  have hE₀hall : IsHallSubgroup (sigmaPrimes N)ᶜ ((U₀ ⊔ K₀).subgroupOf N) :=
    isHallSubgroup_subgroupOf_of_isInternalSemidirectProduct hS hNE₀
  have hEhall : IsHallSubgroup (sigmaPrimes N)ᶜ (E.subgroupOf N) :=
    isHallSubgroup_subgroupOf_of_isInternalSemidirectProduct hS hNE
  obtain ⟨n, hn⟩ := exists_conj_smul_eq_of_isHallSubgroup hE₀hall hEhall
  have hconj : MulAut.conj (n : G) • (U₀ ⊔ K₀) = E := by
    refine eq_of_subgroupOf_eq (Subgroup.conj_smul_le_of_le hE₀N n) hEN ?_
    rw [← Subgroup.conj_smul_subgroupOf hE₀N n]
    exact hn
  refine ⟨MulAut.conj (n : G) • K₀, MulAut.conj (n : G) • U₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hconj, Subgroup.smul_sup]; exact le_sup_right
  · rw [← hconj, Subgroup.smul_sup]; exact le_sup_left
  · exact isHallPiSubgroupOf_conj_smul ⟨hK₀N, hK₀hall.isHallPiSubgroup⟩ n.2
  · exact @isMulCommutative_conj_pointwise_smul _ _ (n : G) U₀ hU₀comm
  · refine isHallPiSubgroupOf_conj_smul (isHallPiSubgroupOf_of_isHallPiOf hU₀hall ?_) n.2
    refine fun r hr => ⟨fun h => ⟨hr, fun hs => h (Or.inl hs), fun hk => h (Or.inr hk)⟩, ?_⟩
    rintro h (hs | hk)
    · exact h.2.1 hs
    · exact h.2.2 hk
  · rw [← hconj]; exact isInternalSemidirectProduct_conj_smul hE₀split _
  · rw [← Subgroup.smul_sup, hconj]; exact hNE
  · intro k hk hk1
    obtain ⟨k₀, hk₀, rfl⟩ := Subgroup.mem_smul_pointwise_iff_exists k _ K₀ |>.1 hk
    have hk₀1 : k₀ ≠ 1 := fun h => hk1 (by rw [h]; simp)
    have hfree' := hfree k₀ hk₀ hk₀1
    rw [Prep03.cent1] at hfree'
    have hbot : MulAut.conj (n : G) • (U₀ ⊓ Subgroup.centralizer {k₀}) = ⊥ := by
      rw [hfree', Subgroup.smul_bot]
    rwa [Subgroup.smul_inf, smul_centralizer_singleton] at hbot

end

end CFSG.FeitThompson.Proofs
