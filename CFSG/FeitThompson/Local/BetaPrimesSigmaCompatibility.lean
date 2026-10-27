module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.NarrowPGroupsAndBetaPrimes
public import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
public import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
public import CFSG.FeitThompson.Local.AlphaPrimesInSigmaPrimes
import CFSG.FeitThompson.OddOrder.SigmaSylowIsAmbientSylow
import CFSG.FeitThompson.Definitions.LocalComplementaryPrimeConstraint
import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.OddOrder.SigmaPrimesWellDefined
import CFSG.FeitThompson.Definitions.TauTwoPrimes
import CFSG.FeitThompson.Definitions.TheThreeTauPrimeSets
import CFSG.FeitThompson.Foundations.NormalHallContainsPiSubgroups
import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy
import CFSG.FeitThompson.Representations.NoInducedIrreducibleFixedOrbitOrder
import Mathlib.GroupTheory.Nilpotent
import CFSG.FeitThompson.Definitions.PowerOperationOnClassFunctions
import CFSG.FeitThompson.Representations.TensorAndDualCharacters
import Mathlib.Data.Complex.Basic

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {p : ℕ} {X Y : Type*} [Group X] [Group Y]

theorem betaPrimes_subset_of_mulEquiv [Finite X] [Finite Y] (e : X ≃* Y) :
    betaPrimes X ⊆ betaPrimes Y := by
  intro p hp
  have hpp := prime_of_mem_betaPrimes hp
  have := Fact.mk hpp
  have hcard : Nat.card X = Nat.card Y := Nat.card_congr e.toEquiv
  set P : Sylow p X := default with hPdef
  have hQcard : Nat.card ((P : Subgroup X).map (e : X →* Y))
      = p ^ (Nat.card Y).factorization p := by
    rw [Subgroup.card_map_of_injective e.injective, P.card_eq_multiplicity, hcard]
  rw [mem_betaPrimes_iff_exists hpp]
  refine ⟨by rw [← hcard]; exact dvd_card_of_mem_betaPrimes hp, Sylow.ofCard _ hQcard, ?_⟩
  rw [Sylow.coe_ofCard]
  exact fun h => not_isPNarrow_of_mem_betaPrimes hp P ((isPNarrow_congr hpp.one_lt
    ((P : Subgroup X).equivMapOfInjective (e : X →* Y) e.injective)).2 h)

theorem betaPrimes_eq_of_mulEquiv [Finite X] [Finite Y] (e : X ≃* Y) :
    betaPrimes X = betaPrimes Y :=
  Set.Subset.antisymm (betaPrimes_subset_of_mulEquiv e) (betaPrimes_subset_of_mulEquiv e.symm)

theorem betaPrimes_subset_alphaPrimes [Finite X] : betaPrimes X ⊆ alphaPrimes X := by
  intro p hp
  have hpp := prime_of_mem_betaPrimes hp
  have := Fact.mk hpp
  refine mem_alphaPrimes.2 ⟨hpp, ?_⟩
  have h : ¬ elementaryAbelianPRank p ↥((default : Sylow p X) : Subgroup X) ≤ 2 := fun hle =>
    not_isPNarrow_of_mem_betaPrimes hp default (isPNarrow_of_elementaryAbelianPRank_le_two hle)
  have h3 := elementaryAbelianPRank_subgroup_le (X := X) (p := p) hpp.one_lt
    ((default : Sylow p X) : Subgroup X)
  omega

section

variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

def betaCore (M : Subgroup G) : Subgroup G := (piCore (betaPrimes ↥M) ↥M).map M.subtype

theorem betaCore_eq_map_piCore (M : Subgroup G) :
    betaCore M = (piCore (betaPrimes ↥M) ↥M).map M.subtype := (rfl)

theorem betaCore_le (M : Subgroup G) : betaCore M ≤ M := Subgroup.map_subtype_le _

theorem subgroupOf_betaCore (M : Subgroup G) :
    (betaCore M).subgroupOf M = piCore (betaPrimes ↥M) ↥M :=
  Subgroup.comap_map_eq_self_of_injective M.subtype_injective _

instance betaCore_normal_subgroupOf (M : Subgroup G) : ((betaCore M).subgroupOf M).Normal := by
  rw [subgroupOf_betaCore]; exact piCore_normal _ _

theorem le_normalizer_betaCore (M : Subgroup G) :
    M ≤ normalizer ((betaCore M : Subgroup G) : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (betaCore_le M)).1 (betaCore_normal_subgroupOf M)

theorem isPiSubgroup_betaCore (M : Subgroup G) : IsPiSubgroup (betaPrimes ↥M) (betaCore M) :=
  isPiSubgroup_map_subtype_iff.2 (isPiSubgroup_piCore _ _)

theorem le_betaCore {N : Subgroup G} (hNM : N ≤ M) (hN : (N.subgroupOf M).Normal)
    (hπ : IsPiSubgroup (betaPrimes ↥M) N) : N ≤ betaCore M := by
  rw [betaCore_eq_map_piCore, le_map_piCore_iff _ hNM]
  exact le_piCore hN
    (isPiSubgroup_map_subtype_iff.1 (by rwa [Subgroup.map_subgroupOf_eq_of_le hNM]))

theorem isGreatest_betaCore (M : Subgroup G) :
    IsGreatest {N : Subgroup G | N ≤ M ∧ (N.subgroupOf M).Normal ∧
      IsPiSubgroup (betaPrimes ↥M) N} (betaCore M) :=
  ⟨⟨betaCore_le M, betaCore_normal_subgroupOf M, isPiSubgroup_betaCore M⟩,
    fun _ h => le_betaCore h.1 h.2.1 h.2.2⟩

@[simp]
theorem betaCore_bot : betaCore (⊥ : Subgroup G) = ⊥ := le_bot_iff.1 (betaCore_le _)

theorem isPNarrow_map_subtype_iff (hp : p.Prime) (S : Sylow p ↥M) :
    IsPNarrow p ↥((S : Subgroup ↥M).map M.subtype) ↔ IsPNarrow p ↥(S : Subgroup ↥M) :=
  (isPNarrow_congr hp.one_lt
    ((S : Subgroup ↥M).equivMapOfInjective M.subtype M.subtype_injective)).symm

theorem mem_betaPrimes_subgroup_iff_of_mem_sigmaPrimes (hpM : p ∈ sigmaPrimes M) :
    p ∈ betaPrimes ↥M ↔ p ∈ betaPrimes G := by
  have hpp := prime_of_mem_sigmaPrimes hpM
  have := Fact.mk hpp
  obtain ⟨T, hT⟩ := exists_sylow_coe_eq_map_subtype hpM (default : Sylow p ↥M)
  have hdvdG : p ∣ Nat.card G :=
    (dvd_natCard_of_mem_sigmaPrimes hpM).trans (Subgroup.card_subgroup_dvd_card M)
  rw [mem_betaPrimes_iff_exists hpp, mem_betaPrimes_iff_exists hpp]
  constructor
  · rintro ⟨-, S, hS⟩
    refine ⟨hdvdG, T, ?_⟩
    rw [hT, isPNarrow_map_subtype_iff hpp]
    exact fun h => hS ((isPNarrow_congr hpp.one_lt (Sylow.equiv default S)).1 h)
  · rintro ⟨-, T', hT'⟩
    refine ⟨dvd_natCard_of_mem_sigmaPrimes hpM, default, ?_⟩
    rw [← isPNarrow_map_subtype_iff hpp, ← hT]
    exact fun h => hT' ((isPNarrow_congr hpp.one_lt (Sylow.equiv T T')).1 h)

theorem betaPrimes_map_conj (M : Subgroup G) (g : G) :
    betaPrimes ↥(M.map (MulAut.conj g : G →* G)) = betaPrimes ↥M :=
  (betaPrimes_eq_of_mulEquiv ((MulAut.conj g).subgroupMap M)).symm

theorem betaPrimes_conj_smul (M : Subgroup G) (g : G) :
    betaPrimes ↥(MulAut.conj g • M) = betaPrimes ↥M := by
  rw [conj_smul_eq_map_conj (X := G), betaPrimes_map_conj]

theorem betaCore_map_conj (M : Subgroup G) (g : G) :
    betaCore (M.map (MulAut.conj g : G →* G)) = (betaCore M).map (MulAut.conj g : G →* G) := by
  rw [betaCore_eq_map_piCore, betaCore_eq_map_piCore, betaPrimes_map_conj,
    map_map_subtype_comm (MulAut.conj g) M, map_piCore_of_mulEquiv]

theorem betaCore_conj_smul (M : Subgroup G) (g : G) :
    betaCore (MulAut.conj g • M) = MulAut.conj g • betaCore M := by
  rw [conj_smul_eq_map_conj (X := G), conj_smul_eq_map_conj (X := G), betaCore_map_conj]

theorem betaPrimes_eq_of_coe_eq_conj_image {N : Subgroup G} {g : G}
    (h : (N : Set G) = (fun a => g⁻¹ * a * g) '' (M : Set G)) :
    betaPrimes ↥N = betaPrimes ↥M := by
  have hN : N = MulAut.conj g⁻¹ • M := SetLike.coe_injective (by rw [h, coe_conj_inv_smul])
  rw [hN, betaPrimes_conj_smul]

theorem coe_betaCore_eq_conj_image_of_coe_eq_conj_image {N : Subgroup G} {g : G}
    (h : (N : Set G) = (fun a => g⁻¹ * a * g) '' (M : Set G)) :
    (betaCore N : Set G) = (fun a => g⁻¹ * a * g) '' (betaCore M : Set G) := by
  have hN : N = MulAut.conj g⁻¹ • M := SetLike.coe_injective (by rw [h, coe_conj_inv_smul])
  rw [hN, betaCore_conj_smul, coe_conj_inv_smul]

section Ambient

variable [IsSimpleGroup G]

theorem betaPrimes_subset_sigmaPrimes (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M) :
    betaPrimes ↥M ⊆ sigmaPrimes M :=
  betaPrimes_subset_alphaPrimes.trans (alphaPrimes_subset_sigmaPrimes hna hodd hsolv hM)

theorem betaPrimes_subgroup_eq_sigmaPrimes_inter (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    (hM : IsCoatom M) : betaPrimes ↥M = sigmaPrimes M ∩ betaPrimes G := by
  refine Set.Subset.antisymm (fun p hp => ?_) (fun p hp => ?_)
  · have hσ := betaPrimes_subset_sigmaPrimes hna hodd hsolv hM hp
    exact ⟨hσ, (mem_betaPrimes_subgroup_iff_of_mem_sigmaPrimes hσ).1 hp⟩
  · exact (mem_betaPrimes_subgroup_iff_of_mem_sigmaPrimes hp.1).2 hp.2

theorem betaPrimes_and_betaCore_of_isCoatom (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    (hM : IsCoatom M) {g : G} {N : Subgroup G}
    (hN : (N : Set G) = (fun a => g⁻¹ * a * g) '' (M : Set G)) :
    betaPrimes ↥M ⊆ sigmaPrimes M ∧ betaPrimes ↥M = sigmaPrimes M ∩ betaPrimes G ∧
      betaPrimes ↥N = betaPrimes ↥M ∧
      (betaCore N : Set G) = (fun a => g⁻¹ * a * g) '' (betaCore M : Set G) :=
  ⟨betaPrimes_subset_sigmaPrimes hna hodd hsolv hM,
    betaPrimes_subgroup_eq_sigmaPrimes_inter hna hodd hsolv hM,
    betaPrimes_eq_of_coe_eq_conj_image hN,
    coe_betaCore_eq_conj_image_of_coe_eq_conj_image hN⟩

end Ambient

end

end

end CFSG.FeitThompson
