module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleNormalizerNoncentralQuotient
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleNormalizerNoncentralFixedPoint
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleNormalizerNoncentralSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizerSylowObstruction

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSet
open CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleNormalizerNoncentral
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

theorem local_involution_point_triple_sylow_normalizer_noncentral_odd_quotient
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hambient : ∀ Q : Sylow p G, Nat.card (pointFixedSet H (Q : Subgroup G)) = 2)
    (P : Sylow p (triplePointStabilizer H z beta))
    (hzP : z ∈ Subgroup.normalizer
      (((P : Subgroup (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype : Subgroup G) : Set G)) :
    let U : Subgroup G := (P : Subgroup (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype
    let N := Subgroup.normalizer (U : Set G)
    QuotientGroup.mk' (CFSG.oddCore N) (⟨z, hzP⟩ : N) ∉
      Subgroup.center (N ⧸ CFSG.oddCore N) := by
  let : Fact p.Prime := ⟨hp⟩
  let E := triplePointStabilizer H z beta
  let U : Subgroup G := (P : Subgroup E).map E.subtype
  let N := Subgroup.normalizer (U : Set G)
  let B := H.subgroupOf N
  let zN : N := ⟨z, hzP⟩
  let zB : B := ⟨zN, h.distinguished_mem⟩
  have hUE : U ≤ E := Subgroup.map_subtype_le _
  have hUH : U ≤ H :=
    hUE.trans (inf_le_left.trans (pairPointStabilizer_le_point H beta))
  have hUp : IsPGroup p U := P.isPGroup'.map E.subtype
  have hUN : U ≤ N := Subgroup.le_normalizer
  have hstats := original_triple_sylow_full_fixed_count_and_sylow_obstructions
    h S hzS hzcenter hdoubly beta hbeta p hp hambient P hzP
  have htrans := original_triple_sylow_normalizer_transitive
    h S hzS hzcenter hdoubly beta hbeta p hp P hzP
  have hindex : B.index ≡ 2 [MOD p] := by
    rw [normalizer_point_index_eq_fixed_set_card H U hUH htrans]
    exact hstats.1
  have hzBorder : orderOf zB = 2 := by
    calc
      orderOf zB = orderOf zN :=
        (orderOf_injective B.subtype B.subtype_injective zB).symm
      _ = orderOf z := (orderOf_injective N.subtype N.subtype_injective zN).symm
      _ = 2 := h.distinguished_order
  change QuotientGroup.mk' (CFSG.oddCore N) zN ∉
    Subgroup.center (N ⧸ CFSG.oddCore N)
  intro hcentral
  obtain ⟨Q, hQnorm⟩ := central_odd_quotient_invariant_subgroup_sylow
    (CFSG.oddCore N) B (CFSG.ComponentClassification.OddCore.odd_card N)
    zB hzBorder hcentral p hp hodd
  obtain ⟨R, hRQ⟩ := residue_two_subgroup_sylow_promotes p hp hodd B hindex Q
  let V : Subgroup G := (R : Subgroup N).map N.subtype
  have hVn : V ≤ N := Subgroup.map_subtype_le _
  have hVp : IsPGroup p V := R.isPGroup'.map N.subtype
  have hRB : (R : Subgroup N) ≤ B := by
    rw [hRQ]
    exact Subgroup.map_subtype_le _
  have hVH : V ≤ H := by
    intro g hg
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hg
    exact hRB hr
  have hzV : z ∈ Subgroup.normalizer (V : Set G) := by
    have hzR : zN ∈ Subgroup.normalizer ((R : Subgroup N) : Set N) := by
      rw [hRQ]
      exact hQnorm
    exact Subgroup.le_normalizer_map N.subtype
      (Subgroup.mem_map_of_mem N.subtype hzR)
  obtain ⟨delta, _, hdeltaV, hdelta_ne⟩ :=
    normalizing_p_subgroup_has_nonbase_fixed_point H U V p hp hodd hVp hVn hstats.1
  have hdelta_z : pointRightCosetMul H delta z ∈ pointFixedSet H V :=
    normalizer_preserves_pointFixedSet hzV hdeltaV
  let F := triplePointStabilizer H z delta
  have hVF : V ≤ F := by
    change V ≤ triplePointStabilizer H z delta
    rw [triplePointStabilizer, pairPointStabilizer, rightCosetStabilizer_base,
      ← pointRightCosetMul_eq_translate]
    exact le_inf (le_inf hVH ((mem_pointFixedSet_iff H V delta).mp hdeltaV))
      ((mem_pointFixedSet_iff H V _).mp hdelta_z)
  let := pointRightCosetOppositeMulAction H
  have hunique : ∀ a : pointRightCosetSpace H,
      rightAct a z = a ↔ a = rightCosetMk H 1 :=
    ((involution_point_unique_containment_action h.distinguished_mem h.distinguished_order).2
      h.unique_containment).2.2.1
  obtain ⟨c, hc, hbetac⟩ := full_centralizer_transitive_on_original_nonbase_points
    h S hzS hzcenter hdoubly beta delta hbeta hdelta_ne
  have hEF : rightConjugate E c = F := by
    simpa only [point_tripleStabilizer_eq, point_rightAct_eq, hbetac] using
      tripleStabilizer_rightConjugate hunique beta c hc
  have hFEcard : Nat.card F = Nat.card E := by
    rw [← hEF]
    exact (Nat.card_congr (E.equivMapOfInjective
      (MulAut.conj c⁻¹).toMonoidHom (MulAut.conj c⁻¹).injective).toEquiv).symm
  have hUcard : Nat.card U = p ^ (Nat.card E).factorization p := by
    rw [Subgroup.card_map_of_injective E.subtype_injective, P.card_eq_multiplicity]
  have hVcard : Nat.card V = p ^ (Nat.card N).factorization p := by
    rw [Subgroup.card_map_of_injective N.subtype_injective, R.card_eq_multiplicity]
  have hVleU : Nat.card V ≤ Nat.card U := by
    have hbound := p_subgroup_card_le_prime_part p hp F V hVF hVp
    rwa [hFEcard, ← hUcard] at hbound
  have hUfull : Nat.card U = p ^ (Nat.card N).factorization p :=
    le_antisymm (p_subgroup_card_le_prime_part p hp N U hUN hUp)
      (hVcard ▸ hVleU)
  exact hstats.2.2.2 (p_subgroup_sylow_of_full_card p hp N U hUN hUfull)

end CFSG.ProperTwoGeneratedCore
