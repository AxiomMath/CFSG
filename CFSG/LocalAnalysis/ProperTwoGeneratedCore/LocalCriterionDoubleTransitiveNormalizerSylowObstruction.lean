module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizerTransport

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSet

variable {G : Type*} [Group G] [Finite G]

theorem three_le_original_fixed_set_card (H A : Subgroup G)
    (a b c : pointRightCosetSpace H) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∈ pointFixedSet H A) (hb : b ∈ pointFixedSet H A)
    (hc : c ∈ pointFixedSet H A) : 3 ≤ Nat.card (pointFixedSet H A) := by
  have hsubset : ({a, b, c} : Set (pointRightCosetSpace H)) ⊆ pointFixedSet H A := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hcard := Set.ncard_le_ncard hsubset
  have ha' : a ∉ ({b, c} : Set (pointRightCosetSpace H)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, hab, hac, or_self, not_false_eq_true]
  rw [Set.ncard_insert_of_notMem ha', Set.ncard_pair hbc] at hcard
  exact hcard

theorem not_sylow_of_own_normalizer_of_not_ambient
    (p : ℕ) (hp : p.Prime) (A : Subgroup G) (hA : IsPGroup p A)
    (hambient : ¬ ∃ P : Sylow p G, (P : Subgroup G) = A) :
    ¬ ∃ P : Sylow p (Subgroup.normalizer (A : Set G)),
      (P : Subgroup (Subgroup.normalizer (A : Set G))).map
        (Subgroup.normalizer (A : Set G)).subtype = A := by
  obtain ⟨Q, hAQ⟩ := hA.exists_le_sylow
  have hstrict : A < (Q : Subgroup G) := lt_of_le_of_ne hAQ (by
    intro heq
    exact hambient ⟨Q, heq.symm⟩)
  let N := Subgroup.normalizer (A : Set G)
  let R := (Q : Subgroup G) ⊓ N
  have hgrowth : A < R := pSubgroup_lt_normalizer_intersection p hp A
    (Q : Subgroup G) Q.isPGroup' hstrict
  have hRp : IsPGroup p R := Q.isPGroup'.of_injective
    (Subgroup.inclusion (show R ≤ (Q : Subgroup G) from inf_le_left))
    (Subgroup.inclusion_injective _)
  have hRN : R ≤ N := inf_le_right
  have hRi : IsPGroup p (R.subgroupOf N) := hRp.of_injective
    (Subgroup.subgroupOfEquivOfLe hRN).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hRN).injective
  rintro ⟨P, hP⟩
  have hPR : (P : Subgroup N) ≤ R.subgroupOf N := by
    intro x hx
    apply (Subgroup.mem_subgroupOf).mpr
    exact hgrowth.le (hP ▸ Subgroup.mem_map_of_mem N.subtype hx)
  have heq := P.is_maximal' hRi hPR
  have hmap := congrArg (Subgroup.map N.subtype) heq
  rw [hP, Subgroup.map_subgroupOf_eq_of_le hRN] at hmap
  exact hgrowth.ne hmap.symm

theorem original_triple_sylow_full_fixed_count_and_sylow_obstructions
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime)
    (hambient : ∀ Q : Sylow p G, Nat.card (pointFixedSet H (Q : Subgroup G)) = 2)
    (P : Sylow p (triplePointStabilizer H z beta))
    (hzP : z ∈ Subgroup.normalizer
      (((P : Subgroup (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype : Subgroup G) : Set G)) :
    let U : Subgroup G := (P : Subgroup (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype
    let Delta := pointFixedSet H U
    let N := Subgroup.normalizer (U : Set G)
    Nat.card Delta ≡ 2 [MOD p] ∧ 3 ≤ Nat.card Delta ∧
      (¬ ∃ Q : Sylow p G, (Q : Subgroup G) = U) ∧
      (¬ ∃ Q : Sylow p N, (Q : Subgroup N).map N.subtype = U) := by
  let U : Subgroup G := (P : Subgroup (triplePointStabilizer H z beta)).map
    (triplePointStabilizer H z beta).subtype
  have hUp : IsPGroup p U := P.isPGroup'.map _
  have ha := original_triple_sylow_normalizer_action
    h S hzS hzcenter hdoubly beta hbeta p hp P hzP
  have hthree : 3 ≤ Nat.card (pointFixedSet H U) :=
    three_le_original_fixed_set_card H U (rightCosetMk H 1) beta
      (pointRightCosetMul H beta z) ha.1.1 ha.1.2.1 ha.1.2.2
      ha.2.1.1 ha.2.1.2.1 ha.2.1.2.2
  have hnotambient : ¬ ∃ Q : Sylow p G, (Q : Subgroup G) = U := by
    rintro ⟨Q, hQ⟩
    have htwo := hambient Q
    rw [hQ] at htwo
    omega
  let Q : Sylow p G := Classical.choice inferInstance
  have hdegree : Nat.card (pointRightCosetSpace H) ≡ 2 [MOD p] := by
    have hc := pointFixedSet_card_modEq p hp H (Q : Subgroup G) Q.isPGroup'
    rwa [hambient Q] at hc
  have hcount : Nat.card (pointFixedSet H U) ≡ 2 [MOD p] :=
    (pointFixedSet_card_modEq p hp H U hUp).symm.trans hdegree
  exact ⟨hcount, hthree, hnotambient,
    not_sylow_of_own_normalizer_of_not_ambient p hp U hUp hnotambient⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
