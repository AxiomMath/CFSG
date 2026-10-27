module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFreeSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeFixedSets

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_zpowers_eq_bot_iff (X : Subgroup G) (t : G) :
    ⁅X, Subgroup.zpowers t⁆ = ⊥ ↔ X ≤ Subgroup.centralizer ({t} : Set G) := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer,
    Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem pair_normalized_noncentral_subgroup_sylow
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta)
    (X : Subgroup G) (hXD : X ≤ pairPointStabilizer H beta)
    (hXnorm : t ∈ Subgroup.normalizer (X : Set G))
    (hnoncentral : ¬ X ≤ Subgroup.centralizer ({t} : Set G)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ P : Sylow p X,
      t ∈ Subgroup.normalizer (((P : Subgroup X).map X.subtype : Subgroup G) : Set G) ∧
      ¬ (P : Subgroup X).map X.subtype ≤ Subgroup.centralizer ({t} : Set G) := by
  let K := pairFlipGroup H beta t
  let J := (pairOddCore H beta).subgroupOf K
  let B := X.subgroupOf K
  let tK : K := ⟨t, flip_mem_pairFlipGroup H beta t⟩
  have hXK : X ≤ K := hXD.trans (pairPointStabilizer_le_pairFlipGroup H beta t)
  let : J.Normal := pairOddCore_normal_in_pair_group h.distinguished_order hbeta ht
  have hJodd : Odd (Nat.card J) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pairOddCore_le H beta t).2.1).toEquiv]
    exact pairOddCore_odd H beta
  have hcentral : QuotientGroup.mk' J tK ∈ Subgroup.center (K ⧸ J) :=
    (pair_flip_zStar_factorization h S hzS hzcenter hbeta ht).1
  have hBnorm : tK ∈ Subgroup.normalizer (B : Set K) := by
    apply Subgroup.mem_normalizer_iff.mpr
    intro x
    exact Subgroup.mem_normalizer_iff.mp hXnorm (x : G)
  have hBnoncentral : ¬ B ≤ Subgroup.centralizer ({tK} : Set K) := by
    intro hBC
    apply hnoncentral
    intro x hx
    have hxB : (⟨x, hXK hx⟩ : K) ∈ B := hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hBC hxB)))
  have htorder : orderOf tK = 2 := (Subgroup.orderOf_coe tK).symm.trans
    (order_two_of_mem_pointClass h.distinguished_order ht.1)
  obtain ⟨p, hp, hpodd, P₀, hPnorm, hPnoncentral⟩ :=
    normalized_subgroup_noncentral_invariant_sylow J B tK htorder hJodd hBnorm hcentral hBnoncentral
  obtain ⟨P, _, hPnormG, hPnoncentralG⟩ :=
    internal_noncentral_sylow_transport X K hXK t tK.property p hp P₀ hPnorm hPnoncentral
  exact ⟨p, hp, hpodd, P, hPnormG, hPnoncentralG⟩

theorem original_three_point_noncentral_sylow_selection
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta)
    (X : Subgroup G) (hXD : X ≤ pairPointStabilizer H beta)
    (hXnorm : t ∈ Subgroup.normalizer (X : Set G))
    (hnoncentral : ⁅X, Subgroup.zpowers t⁆ ≠ ⊥)
    (hthree : 3 ≤ Nat.card (pointFixedSet H X)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ P : Sylow p X,
      t ∈ Subgroup.normalizer (((P : Subgroup X).map X.subtype : Subgroup G) : Set G) ∧
      ⁅(P : Subgroup X).map X.subtype, Subgroup.zpowers t⁆ ≠ ⊥ ∧
      pointFixedSet H X ⊆ pointFixedSet H ((P : Subgroup X).map X.subtype) ∧
      3 ≤ Nat.card (pointFixedSet H ((P : Subgroup X).map X.subtype)) := by
  have hXC : ¬ X ≤ Subgroup.centralizer ({t} : Set G) :=
    fun hc => hnoncentral ((commutator_zpowers_eq_bot_iff X t).mpr hc)
  obtain ⟨p, hp, hpodd, P, hPnorm, hPnoncentral⟩ :=
    pair_normalized_noncentral_subgroup_sylow h S hzS hzcenter beta hbeta t ht X hXD hXnorm hXC
  have hfixed := pointFixedSet_antitone (Subgroup.map_subtype_le (P : Subgroup X)) (H := H)
  have hcard := Nat.card_le_card_of_injective (Set.inclusion hfixed) (Set.inclusion_injective hfixed)
  exact ⟨p, hp, hpodd, P, hPnorm,
    fun heq => hPnoncentral ((commutator_zpowers_eq_bot_iff _ t).mp heq),
    hfixed, hthree.trans hcard⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
