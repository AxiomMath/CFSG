module

public import CFSG.FeitThompson.Local.CommonPrimeFixedNormalSylow
import CFSG.FeitThompson.OddOrder.CommutingSubgroupsJoinProduct
import CFSG.FeitThompson.Foundations.PGroupNilpotent

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise Subgroup

universe u

variable {X : Type u} [Group X] {q : ℕ} {S K Z D : Subgroup X}

theorem exists_eq_pow_of_isPiNumber_singleton {q n : ℕ} (hn : n ≠ 0)
    (h : IsPiNumber ({q} : Set ℕ) n) : ∃ a, n = q ^ a :=
  ⟨n.primeFactorsList.length, Nat.eq_prime_pow_of_unique_prime_dvd hn
    (fun hd hdvd => isPiNumber_iff.1 h _ (Nat.mem_primeFactors.2 ⟨hd, hdvd, hn⟩))⟩

theorem not_dvd_of_isPiNumber_compl_singleton {q n : ℕ} (hq : q.Prime) (hn : n ≠ 0)
    (h : IsPiNumber ({q}ᶜ : Set ℕ) n) : ¬ q ∣ n :=
  fun hd => isPiNumber_iff.1 h q (Nat.mem_primeFactors.2 ⟨hq, hd, hn⟩) rfl

namespace IsCommonPrimeFixedSetup

variable (h : IsCommonPrimeFixedSetup X q S K Z)

include h

variable [Finite X]

theorem exists_isHallSubgroup_subgroupOf_le_normalizer :
    ∃ D : Subgroup X, D ≤ S ∧ IsHallSubgroup ({q}ᶜ : Set ℕ) (D.subgroupOf S) ∧
      K ≤ normalizer (D : Set X) := by
  have : Group.IsSolvable X := h.isSolvable
  have := h.normal_S
  obtain ⟨D, hDS, hDhall, -, hDK⟩ :=
    exists_isHallSubgroup_subgroupOf_ge_le_normalizer (K := S) (A := K) (R := ⊥)
      h.isComplement.sup_eq_top h.coprime ({q}ᶜ) bot_le (by simp) le_normalizer_of_normal
  exact ⟨D, hDS, hDhall, hDK⟩

theorem not_dvd_natCard_K : ¬ q ∣ Nat.card ↥K := fun hd =>
  h.prime.one_lt.ne' (Nat.eq_one_of_dvd_one (h.coprime ▸ Nat.dvd_gcd h.dvd_natCard_S hd))

theorem isNilpotent_pCoreIn : Group.IsNilpotent ↥(pCoreIn q S) :=
  isNilpotent_of_natCard_eq_prime_pow h.prime h.natCard_pCoreIn_eq_pow_factorization_S

theorem inf_pCoreIn_centralizer_eq (k : X) (hk : k ∈ K) (hk1 : k ≠ 1) :
    pCoreIn q S ⊓ centralizer ({k} : Set X) = Z := by
  rw [← inf_eq_left.2 (pCoreIn_le q S), inf_assoc, h.inf_centralizer_S k hk hk1,
    inf_eq_right.2 h.Z_le_pCoreIn]

section HallCompl

variable (hDS : D ≤ S) (hDhall : IsHallSubgroup ({q}ᶜ : Set ℕ) (D.subgroupOf S))

include hDS hDhall

theorem not_dvd_natCard_of_isHallSubgroup : ¬ q ∣ Nat.card ↥D := by
  refine not_dvd_of_isPiNumber_compl_singleton h.prime Nat.card_pos.ne' ?_
  have := hDhall.natCard
  rwa [Nat.card_eq_of_bijective _ (Subgroup.subgroupOfEquivOfLe hDS).bijective] at this

omit h hDS in
theorem exists_relIndex_eq_pow_of_isHallSubgroup : ∃ a, D.relIndex S = q ^ a := by
  refine exists_eq_pow_of_isPiNumber_singleton ?_ ?_
  · rw [← index_subgroupOf]; exact Subgroup.index_ne_zero_of_finite
  · have := hDhall.index
    rw [compl_compl, index_subgroupOf] at this
    exact this

theorem sup_pCoreIn_eq' : pCoreIn q S ⊔ D = S :=
  h.sup_pCoreIn_eq hDS (h.not_dvd_natCard_of_isHallSubgroup hDS hDhall)
    (exists_relIndex_eq_pow_of_isHallSubgroup hDhall)

theorem inf_pCoreIn_eq_bot' : pCoreIn q S ⊓ D = ⊥ :=
  h.inf_pCoreIn_eq_bot hDS (h.not_dvd_natCard_of_isHallSubgroup hDS hDhall)
    (exists_relIndex_eq_pow_of_isHallSubgroup hDhall)

theorem natCard_mul_natCard_pCoreIn' : Nat.card ↥D * Nat.card ↥(pCoreIn q S) = Nat.card ↥S :=
  h.natCard_mul_natCard_pCoreIn hDS (h.not_dvd_natCard_of_isHallSubgroup hDS hDhall)
    (exists_relIndex_eq_pow_of_isHallSubgroup hDhall)

theorem isNilpotent_of_isHallSubgroup : Group.IsNilpotent ↥D :=
  h.isNilpotent_of_hallQCompl hDS (h.not_dvd_natCard_of_isHallSubgroup hDS hDhall)
    (exists_relIndex_eq_pow_of_isHallSubgroup hDhall)

theorem ne_bot_of_isHallSubgroup : D ≠ ⊥ := by
  intro hb
  refine h.not_isNilpotent_S ?_
  have hQS : pCoreIn q S = S := by
    have := h.sup_pCoreIn_eq' hDS hDhall
    rwa [hb, sup_bot_eq] at this
  have hc := h.natCard_pCoreIn_eq_pow_factorization_S
  rw [hQS] at hc
  exact isNilpotent_of_natCard_eq_prime_pow h.prime hc

theorem inf_centralizer_eq_bot_of_mem (k : X) (hk : k ∈ K) (hk1 : k ≠ 1) :
    D ⊓ centralizer ({k} : Set X) = ⊥ := by
  have hDZ : D ⊓ centralizer ({k} : Set X) ≤ pCoreIn q S ⊓ D := by
    refine le_inf (le_trans ?_ h.Z_le_pCoreIn) inf_le_left
    rw [← h.inf_centralizer_S k hk hk1]
    exact le_inf (inf_le_left.trans hDS) inf_le_right
  exact le_bot_iff.1 (hDZ.trans (h.inf_pCoreIn_eq_bot' hDS hDhall).le)

theorem inf_centralizer_lt_pCoreIn :
    pCoreIn q S ⊓ centralizer (D : Set X) < pCoreIn q S := by
  refine lt_of_le_of_ne inf_le_left fun heq => h.not_isNilpotent_S ?_
  have hQC : pCoreIn q S ≤ centralizer (D : Set X) := heq.ge.trans inf_le_right
  have hcomm : ∀ x ∈ pCoreIn q S, ∀ y ∈ D, Commute x y := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.1 (hQC hx) y hy).symm
  have hcoe := coe_sup_eq_mul_of_commute hcomm
  rw [h.sup_pCoreIn_eq' hDS hDhall] at hcoe
  have := h.isNilpotent_pCoreIn
  have := h.isNilpotent_of_isHallSubgroup hDS hDhall
  exact Group.nilpotent_of_mulEquiv
    (mulEquivProdOfCoeEqMul hcoe (h.inf_pCoreIn_eq_bot' hDS hDhall) hcomm)

section Invariant

variable (hDK : K ≤ normalizer (D : Set X))

include hDK

omit [Finite X] hDhall hDK in
theorem inf_D_K_eq_bot : D ⊓ K = ⊥ :=
  le_bot_iff.1 ((inf_le_inf_right K hDS).trans (disjoint_iff.1 h.isComplement.disjoint).le)

omit [Finite X] hDhall in
theorem natCard_sup_D_K : Nat.card ↥(D ⊔ K) = Nat.card ↥D * Nat.card ↥K :=
  natCard_sup_eq_mul_of_le_normalizer hDK (h.inf_D_K_eq_bot hDS)

omit hDhall in
theorem isComplement'_subgroupOf_sup :
    (D.subgroupOf (D ⊔ K)).IsComplement' (K.subgroupOf (D ⊔ K)) := by
  refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ ?_
  · rw [Nat.card_eq_of_bijective _ (Subgroup.subgroupOfEquivOfLe (le_sup_left (b := K))).bijective,
      Nat.card_eq_of_bijective _ (Subgroup.subgroupOfEquivOfLe (le_sup_right (a := D))).bijective]
    exact (h.natCard_sup_D_K hDS hDK).symm
  · have he : D.subgroupOf (D ⊔ K) ⊓ K.subgroupOf (D ⊔ K) = (D ⊓ K).subgroupOf (D ⊔ K) :=
      (Subgroup.comap_inf _ _ _).symm
    rw [disjoint_iff, he, h.inf_D_K_eq_bot hDS, Subgroup.bot_subgroupOf]

omit h [Finite X] hDS hDhall in
theorem normal_subgroupOf_sup : (D.subgroupOf (D ⊔ K)).Normal :=
  normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer hDK)

theorem coprime_natCard_pCoreIn_sup :
    (Nat.card ↥(pCoreIn q S)).Coprime (Nat.card ↥(D ⊔ K)) := by
  rw [h.natCard_pCoreIn_eq_pow_factorization_S, h.natCard_sup_D_K hDS hDK]
  refine Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd h.prime).2 fun hd => ?_)
  exact (h.prime.dvd_mul.1 hd).elim (h.not_dvd_natCard_of_isHallSubgroup hDS hDhall)
    h.not_dvd_natCard_K

theorem natCard_pCoreIn_mul_natCard_sup :
    Nat.card ↥(pCoreIn q S) * Nat.card ↥(D ⊔ K) = Nat.card X := by
  have h1 := h.natCard_mul_natCard_pCoreIn' hDS hDhall
  have h2 := h.isComplement.card_mul_card
  rw [h.natCard_sup_D_K hDS hDK, ← h2, ← h1]
  ring

theorem isComplement'_pCoreIn_sup : (pCoreIn q S).IsComplement' (D ⊔ K) := by
  refine Subgroup.isComplement'_of_card_mul_and_disjoint
    (h.natCard_pCoreIn_mul_natCard_sup hDS hDhall hDK) ?_
  rw [disjoint_iff]
  exact Subgroup.card_eq_one.1 (Nat.eq_one_of_dvd_coprimes
    (h.coprime_natCard_pCoreIn_sup hDS hDhall hDK)
    (Subgroup.card_dvd_of_le inf_le_left) (Subgroup.card_dvd_of_le inf_le_right))

omit hDS hDhall in
theorem le_normalizer_inf_centralizer :
    D ⊔ K ≤ normalizer ((pCoreIn q S ⊓ centralizer (D : Set X) : Subgroup X) : Set X) := by
  have := h.normal_pCoreIn
  refine le_trans (sup_le ?_ ?_) Subgroup.inf_normalizer_le_normalizer_inf
  · exact le_inf le_normalizer_of_normal
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_centralizer D))
  · exact le_inf le_normalizer_of_normal (hDK.trans (normalizer_le_normalizer_centralizer D))

end Invariant

end HallCompl

end IsCommonPrimeFixedSetup

theorem exists_hall_qCompl_normalized_by {X : Type u} [Group X] {q : ℕ} {S K Z : Subgroup X}
    (h : IsCommonPrimeFixedSetup X q S K Z) :
    haveI := h.finite
    ∃ D : Subgroup X, D ≤ S ∧ IsHallSubgroup ({q}ᶜ : Set ℕ) (D.subgroupOf S) ∧
      K ≤ Subgroup.normalizer (D : Set X) :=
  haveI := h.finite
  h.exists_isHallSubgroup_subgroupOf_le_normalizer

theorem common_prime_fixed_complement_layout {X : Type u} [Group X] {q : ℕ}
    {S K Z D : Subgroup X} (h : IsCommonPrimeFixedSetup X q S K Z) (hDS : D ≤ S)
    (hDhall : IsHallSubgroup ({q}ᶜ : Set ℕ) (D.subgroupOf S))
    (hDK : K ≤ Subgroup.normalizer (D : Set X)) :
    haveI := h.finite
    D ≠ ⊥ ∧ Group.IsNilpotent ↥D ∧
      (pCoreIn q S ⊔ D = S ∧ pCoreIn q S ⊓ D = ⊥) ∧
      (pCoreIn q S).IsComplement' (D ⊔ K) ∧
      (D.subgroupOf (D ⊔ K)).Normal ∧
      (D.subgroupOf (D ⊔ K)).IsComplement' (K.subgroupOf (D ⊔ K)) ∧
      (Nat.card ↥(pCoreIn q S)).Coprime (Nat.card ↥(D ⊔ K)) ∧
      (∀ k ∈ K, k ≠ 1 → D ⊓ Subgroup.centralizer ({k} : Set X) = ⊥) ∧
      (∀ k ∈ K, k ≠ 1 → pCoreIn q S ⊓ Subgroup.centralizer ({k} : Set X) = Z) ∧
      D ⊔ K ≤ Subgroup.normalizer
        ((pCoreIn q S ⊓ Subgroup.centralizer (D : Set X) : Subgroup X) : Set X) ∧
      pCoreIn q S ⊓ Subgroup.centralizer (D : Set X) < pCoreIn q S :=
  haveI := h.finite
  ⟨h.ne_bot_of_isHallSubgroup hDS hDhall, h.isNilpotent_of_isHallSubgroup hDS hDhall,
    ⟨h.sup_pCoreIn_eq' hDS hDhall, h.inf_pCoreIn_eq_bot' hDS hDhall⟩,
    h.isComplement'_pCoreIn_sup hDS hDhall hDK,
    IsCommonPrimeFixedSetup.normal_subgroupOf_sup hDK,
    h.isComplement'_subgroupOf_sup hDS hDK,
    h.coprime_natCard_pCoreIn_sup hDS hDhall hDK,
    fun k hk hk1 => h.inf_centralizer_eq_bot_of_mem hDS hDhall k hk hk1,
    fun k hk hk1 => h.inf_pCoreIn_centralizer_eq k hk hk1,
    h.le_normalizer_inf_centralizer hDK,
    h.inf_centralizer_lt_pCoreIn hDS hDhall⟩

end

end CFSG.FeitThompson
