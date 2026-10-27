module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylowContainment
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointOppositePair
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddCentralSylowIndex

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow

open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem class_card_mul_fixed_card (A : Subgroup G) (z : G) :
    Nat.card (conjugacyWithin A z) *
      Nat.card (A ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G) = Nat.card A := by
  rw [conjugacyWithin_card_eq_centralizer_index]
  change (Subgroup.centralizer ({z} : Set G)).relIndex A * _ = _
  simpa only [inf_comm] using (Subgroup.centralizer ({z} : Set G)).relIndex_mul_card A

theorem centralizer_index_prime_part_mul (p : ℕ) (A : Subgroup G) (z : G) :
    p ^ (Nat.card A).factorization p =
      p ^ ((Subgroup.centralizer ({z} : Set G)).relIndex A).factorization p *
        p ^ (Nat.card (A ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G)).factorization p := by
  have hcard := (Subgroup.centralizer ({z} : Set G)).relIndex_mul_card A
  have hindex : (Subgroup.centralizer ({z} : Set G)).relIndex A ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hcard
    exact Nat.card_pos.ne' hcard.symm
  rw [← hcard, Nat.factorization_mul hindex Nat.card_pos.ne', Finsupp.add_apply, pow_add]
  rw [inf_comm]

theorem p_subgroup_card_le_prime_part (p : ℕ) (hp : p.Prime)
    (B U : Subgroup G) (hUB : U ≤ B) (hU : IsPGroup p U) :
    Nat.card U ≤ p ^ (Nat.card B).factorization p := by
  let : Fact p.Prime := ⟨hp⟩
  have hUp : IsPGroup p (U.subgroupOf B) :=
    hU.of_injective (Subgroup.subgroupOfEquivOfLe hUB).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hUB).injective
  obtain ⟨P, hP⟩ := hUp.exists_le_sylow
  have hle := Subgroup.card_le_of_le hP
  rw [P.card_eq_multiplicity] at hle
  have hcard : Nat.card (U.subgroupOf B) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUB).toEquiv
  rw [hcard] at hle
  exact hle

theorem p_subgroup_sylow_of_full_card (p : ℕ) (hp : p.Prime)
    (B U : Subgroup G) (hUB : U ≤ B)
    (hcard : Nat.card U = p ^ (Nat.card B).factorization p) :
    ∃ P : Sylow p B, (P : Subgroup B).map B.subtype = U := by
  let : Fact p.Prime := ⟨hp⟩
  have hcardB : Nat.card (U.subgroupOf B) = p ^ (Nat.card B).factorization p :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUB).toEquiv).trans hcard
  refine ⟨Sylow.ofCard (U.subgroupOf B) hcardB, ?_⟩
  rw [Sylow.coe_ofCard, Subgroup.map_subgroupOf_eq_of_le hUB]

theorem p_subgroup_sylow_of_motion_threshold
    (p : ℕ) (hp : p.Prime) (B U : Subgroup G) (z : G)
    (hUB : U ≤ B) (hU : IsPGroup p U)
    (R : Sylow p (B ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G))
    (hRimage : (R : Subgroup (B ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G)).map
      (B ⊓ Subgroup.centralizer ({z} : Set G)).subtype =
        U ⊓ Subgroup.centralizer ({z} : Set G))
    (hmotion : p ^ ((Subgroup.centralizer ({z} : Set G)).relIndex B).factorization p ≤
      Nat.card (conjugacyWithin U z)) :
    ∃ P : Sylow p B, (P : Subgroup B).map B.subtype = U := by
  let : Fact p.Prime := ⟨hp⟩
  have hfixed : Nat.card (U ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G) =
      p ^ (Nat.card (B ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G)).factorization p := by
    rw [← hRimage, Subgroup.card_map_of_injective
      (B ⊓ Subgroup.centralizer ({z} : Set G)).subtype_injective, R.card_eq_multiplicity]
  have hcardU := class_card_mul_fixed_card U z
  have hlower : p ^ (Nat.card B).factorization p ≤ Nat.card U := by
    rw [centralizer_index_prime_part_mul p B z, ← hfixed, ← hcardU]
    exact Nat.mul_le_mul_right _ hmotion
  have hcard := le_antisymm (p_subgroup_card_le_prime_part p hp B U hUB hU) hlower
  exact p_subgroup_sylow_of_full_card p hp B U hUB hcard

theorem sylow_of_overgroup_with_contained_sylow
    (p : ℕ) (hp : p.Prime) (B E : Subgroup G) (hEB : E ≤ B)
    (hcontains : ∃ Q : Sylow p B, (Q : Subgroup B).map B.subtype ≤ E)
    (P : Sylow p E) :
    ∃ Q : Sylow p B, (Q : Subgroup B).map B.subtype = (P : Subgroup E).map E.subtype := by
  obtain ⟨Q, hQ⟩ := hcontains
  exact sylow_extension_same_ambient_image p hp B E hEB
    (sylow_overgroup_relIndex_prime_to p hp B E Q hQ) P

theorem triple_full_pair_sylow_motion
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) (P : Sylow p (triplePointStabilizer H z beta))
    (hPnorm : z ∈ Subgroup.normalizer (((P : Subgroup (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype : Subgroup G) : Set G))
    (hfull : ∃ Q : Sylow p (pairPointStabilizer H beta),
      (Q : Subgroup (pairPointStabilizer H beta)).map (pairPointStabilizer H beta).subtype =
        (P : Subgroup (triplePointStabilizer H z beta)).map (triplePointStabilizer H z beta).subtype) :
    Nat.card (conjugacyWithin ((P : Subgroup (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype) z) =
      p ^ (Nat.card (conjugacyWithin H z)).factorization p := by
  obtain ⟨Q, hQ⟩ := hfull
  obtain ⟨R, hR⟩ := triple_invariant_sylow_fixed h S hzS hzcenter beta hbeta p hp P hPnorm
  rw [← hQ] at hR ⊢
  rw [conjugacyWithin_card_eq_centralizer_index]
  change (Subgroup.centralizer ({z} : Set G)).relIndex
    ((Q : Subgroup (pairPointStabilizer H beta)).map (pairPointStabilizer H beta).subtype) = _
  rw [sylow_fixed_intersection_relIndex_prime_part p hp (pairPointStabilizer H beta) z Q R hR]
  obtain ⟨t, ht⟩ := original_pair_flip_exists h beta hbeta
  rw [show (Subgroup.centralizer ({z} : Set G)).relIndex (pairPointStabilizer H beta) =
      Nat.card (conjugacyWithin H z) from
    pair_stabilizer_z_centralizer_index_eq_class_card h S hzS hzcenter hbeta ht]

theorem triple_motion_threshold_contains_pair_sylow
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) (X : Subgroup G)
    (hXB : X ≤ pairPointStabilizer H beta) (hX : IsPGroup p X)
    (hXnorm : z ∈ Subgroup.normalizer (X : Set G))
    (hmotion : p ^ (Nat.card (conjugacyWithin H z)).factorization p ≤
      Nat.card (conjugacyWithin X z)) :
    ∃ Q : Sylow p (pairPointStabilizer H beta),
      X ≤ (Q : Subgroup (pairPointStabilizer H beta)).map
        (pairPointStabilizer H beta).subtype ∧
      (Q : Subgroup (pairPointStabilizer H beta)).map
        (pairPointStabilizer H beta).subtype ≤ triplePointStabilizer H z beta ∧
      z ∈ Subgroup.normalizer (((Q : Subgroup (pairPointStabilizer H beta)).map
        (pairPointStabilizer H beta).subtype : Subgroup G) : Set G) := by
  obtain ⟨_, P, hXP, hPnorm, R, hR⟩ :=
    triple_invariant_subgroup_extends h S hzS hzcenter beta hbeta p hp X hXB hX hXnorm
  let U := (P : Subgroup (triplePointStabilizer H z beta)).map
    (triplePointStabilizer H z beta).subtype
  have hUE : U ≤ triplePointStabilizer H z beta := Subgroup.map_subtype_le _
  have hUB : U ≤ pairPointStabilizer H beta := hUE.trans inf_le_left
  have hUp : IsPGroup p U := P.isPGroup'.map (triplePointStabilizer H z beta).subtype
  have hmotionU : p ^ (Nat.card (conjugacyWithin H z)).factorization p ≤
      Nat.card (conjugacyWithin U z) :=
    hmotion.trans (Nat.card_mono (Set.toFinite _) (conjugacyWithin_mono hXP z))
  obtain ⟨t, ht⟩ := original_pair_flip_exists h beta hbeta
  have hindex : (Subgroup.centralizer ({z} : Set G)).relIndex
      (pairPointStabilizer H beta) = Nat.card (conjugacyWithin H z) :=
    pair_stabilizer_z_centralizer_index_eq_class_card h S hzS hzcenter hbeta ht
  obtain ⟨Q, hQ⟩ := p_subgroup_sylow_of_motion_threshold p hp
    (pairPointStabilizer H beta) U z hUB hUp R hR (by simpa only [hindex] using hmotionU)
  refine ⟨Q, ?_, ?_, ?_⟩
  · rw [hQ]
    exact hXP
  · rw [hQ]
    exact hUE
  · rw [hQ]
    exact hPnorm

theorem triple_exact_motion_of_contains_pair_sylow
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime)
    (hcontains : ∃ Q : Sylow p (pairPointStabilizer H beta),
      (Q : Subgroup (pairPointStabilizer H beta)).map
        (pairPointStabilizer H beta).subtype ≤ triplePointStabilizer H z beta) :
    ∃ X : Subgroup G, X ≤ pairPointStabilizer H beta ∧ IsPGroup p X ∧
      z ∈ Subgroup.normalizer (X : Set G) ∧
      Nat.card (conjugacyWithin X z) = p ^ (Nat.card (conjugacyWithin H z)).factorization p := by
  have hbotnorm : z ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    apply (Subgroup.mem_normalizer_iff_map_conj_eq).mpr
    exact Subgroup.map_bot _
  obtain ⟨_, P, _, hPnorm, _⟩ := triple_invariant_subgroup_extends h S hzS hzcenter
    beta hbeta p hp ⊥ bot_le (IsPGroup.of_subsingleton p (⊥ : Subgroup G)) hbotnorm
  obtain ⟨Q, hQ⟩ := sylow_of_overgroup_with_contained_sylow p hp
    (pairPointStabilizer H beta) (triplePointStabilizer H z beta) inf_le_left hcontains P
  let X := (P : Subgroup (triplePointStabilizer H z beta)).map
    (triplePointStabilizer H z beta).subtype
  refine ⟨X, (Subgroup.map_subtype_le _).trans inf_le_left,
    P.isPGroup'.map (triplePointStabilizer H z beta).subtype, hPnorm, ?_⟩
  exact triple_full_pair_sylow_motion h S hzS hzcenter beta hbeta p hp P hPnorm ⟨Q, hQ⟩

theorem triple_contains_pair_sylow_iff_motion
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) :
    (∃ Q : Sylow p (pairPointStabilizer H beta),
      (Q : Subgroup (pairPointStabilizer H beta)).map (pairPointStabilizer H beta).subtype ≤
        triplePointStabilizer H z beta) ↔
    ∃ X : Subgroup G, X ≤ pairPointStabilizer H beta ∧ IsPGroup p X ∧
      z ∈ Subgroup.normalizer (X : Set G) ∧
      p ^ (Nat.card (conjugacyWithin H z)).factorization p ≤ Nat.card (conjugacyWithin X z) := by
  constructor
  · intro hcontains
    obtain ⟨X, hXB, hX, hXnorm, hmotion⟩ :=
      triple_exact_motion_of_contains_pair_sylow h S hzS hzcenter beta hbeta p hp hcontains
    exact ⟨X, hXB, hX, hXnorm, hmotion.ge⟩
  · rintro ⟨X, hXB, hX, hXnorm, hmotion⟩
    obtain ⟨Q, _, hQE, _⟩ := triple_motion_threshold_contains_pair_sylow
      h S hzS hzcenter beta hbeta p hp X hXB hX hXnorm hmotion
    exact ⟨Q, hQE⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
