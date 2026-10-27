module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionArbitraryCentralizerHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityGeometry
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RankOnePairOddFactor
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RankOnePairThreeInvolutions
public import CFSG.LocalAnalysis.RankTwoShapes.SingleInvolutionClass

public section

namespace CFSG.ProperTwoGeneratedCore.RankOnePair

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionArbitraryCentralizerHull
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

theorem index_ne_two_of_isSimpleGroup [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (K : Subgroup G) : K.index ≠ 2 := by
  intro hK
  rcases (Subgroup.normal_of_index_eq_two hK).eq_bot_or_eq_top with rfl | rfl
  · rw [Subgroup.index_bot] at hK
    have : IsCyclic G := isCyclic_of_prime_card hK
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (mul_comm' a b)
  · rw [Subgroup.index_top] at hK
    exact absurd hK (by norm_num)

theorem rightCosetStabilizer_pointRightCosetMul (H : Subgroup G) (ω : pointRightCosetSpace H)
    (x : G) :
    rightCosetStabilizer H (pointRightCosetMul H ω x) =
      (rightCosetStabilizer H ω).map (MulAut.conj x⁻¹).toMonoidHom := by
  change MulAction.stabilizer G (QuotientGroup.quotientRightRelEquivQuotientLeftRel H
      ((QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm
        (x⁻¹ • QuotientGroup.quotientRightRelEquivQuotientLeftRel H ω))) = _
  rw [Equiv.apply_symm_apply, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rfl

theorem card_involutions_eq_three_of_image {M : Subgroup G} (P : Subgroup M) {u z : G}
    (hinv : ∀ t : G, t ∈ P.map M.subtype ∧ orderOf t = 2 ↔ t = u ∨ t = z ∨ t = u * z)
    (huz : u ≠ z) (hu : u ≠ 1) (hz : z ≠ 1) :
    Nat.card {t : P // orderOf t = 2} = 3 := by
  have hmem : ∀ t : {t : P // orderOf t = 2}, ((t.1 : M) : G) ∈ ({u, z, u * z} : Set G) := by
    intro t
    have hord : orderOf ((t.1 : M) : G) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact t.2
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      (hinv ((t.1 : M) : G)).mp ⟨Subgroup.mem_map_of_mem M.subtype t.1.2, hord⟩
  let f : {t : P // orderOf t = 2} → ({u, z, u * z} : Set G) := fun t => ⟨_, hmem t⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => Subtype.ext (Subtype.ext (Subtype.ext
      (congrArg (fun x : ({u, z, u * z} : Set G) => (x : G)) hab))), ?_⟩
    rintro ⟨x, hx⟩
    obtain ⟨hxP, hxord⟩ := (hinv x).mpr (by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx)
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hxP
    refine ⟨⟨⟨m, hm⟩, ?_⟩, rfl⟩
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact hxord
  rw [Nat.card_eq_of_bijective f hf, Nat.card_coe_set_eq, Set.ncard_eq_three]
  refine ⟨u, z, u * z, huz, fun h => hz ?_, fun h => hu ?_, rfl⟩
  · simpa using h
  · simpa using h

variable [Finite G]

theorem pRank_inf_conj_eq_pair_twoRank {H : Subgroup G}
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    {beta : pointRightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1) {g : G} (hg : g ∉ H) :
    CFSG.Open.pRank 2 (H ⊓ H.map (MulAut.conj g⁻¹).toMonoidHom) =
      twoRank (pairPointStabilizer H beta) := by
  have hmove : pointRightCosetMul H (rightCosetMk H 1) g = rightCosetMk H g := by
    change pointRightCosetMul H (Quotient.mk _ 1) g = Quotient.mk _ g
    rw [pointRightCosetMul_mk, one_mul]
  have hne : rightCosetMk H g ≠ rightCosetMk H 1 := fun heq =>
    hg ((point_right_base_fixed_iff H g).mp (hmove.trans heq))
  obtain ⟨x, hxα, hxβ⟩ := hdoubly _ _ _ _ hbeta.symm hne.symm
  have hpair : H ⊓ H.map (MulAut.conj g⁻¹).toMonoidHom =
      (pairPointStabilizer H beta).map (MulAut.conj x⁻¹).toMonoidHom := by
    rw [pairPointStabilizer, Subgroup.map_inf _ _ _ (MulAut.conj x⁻¹).injective,
      ← rightCosetStabilizer_pointRightCosetMul, ← rightCosetStabilizer_pointRightCosetMul, hxα,
      hxβ, rightCosetStabilizer_base, rightCosetStabilizer_mk]
    rfl
  rw [hpair, pRank_map_automorphism 2 (by norm_num),
    pRank_subgroup_eq_internal_top 2 (by norm_num)]
  rfl

theorem two_le_twoRank_localInvolutionPointHull_of_pair_rank_one
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hpairRank : twoRank (pairPointStabilizer H beta) = 1)
    {u : G} (huB : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H) :
    2 ≤ twoRank (localInvolutionPointHull z u) := by
  classical
  obtain ⟨hsimple, hnonab⟩ := minimalLocalFailure_nonabelian_simple h
  have huH : u ∈ H := pairPointStabilizer_le_point H beta huB
  have huclass : u ∉ involutionPointClass z :=
    LocalCriterionDegreeIdentity.pair_stabilizer_not_distinguished h.local_datum beta hbeta u huB
  have hhull := minimalLocalFailure_arbitrary_involution_centralizer_hull h hcomm hsmallerR1
    huH hu huz hescape
  dsimp only at hhull
  obtain ⟨-, -, -, -, -, -, -, hxor⟩ := hhull
  rcases hxor.or with ⟨-, -, -, hMfac, hHM⟩ | ⟨hrank, -⟩
  swap
  · exact hrank
  exfalso
  set M := Subgroup.centralizer ({u} : Set G)
  set O := (CFSG.oddCore M).map M.subtype with hO
  have hz : orderOf z = 2 := h.local_datum.distinguished_order
  have hzM : z ∈ M := Subgroup.mem_centralizer_singleton_iff.mpr huz.symm.eq
  have huM : u ∈ M := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have huCentral : u ∈ Subgroup.centralizer (M : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun m hm => Subgroup.mem_centralizer_singleton_iff.mp hm
  have hzCentral : z ∈ Subgroup.centralizer ((H ⊓ M : Subgroup G) : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    have hx' : x ∈ M ⊓ Subgroup.centralizer ({z} : Set G) := hHM ▸ hx
    exact Subgroup.mem_centralizer_singleton_iff.mp hx'.2
  have huz' : u ≠ z := fun heq => huclass (heq ▸ distinguished_mem_pointClass z)
  have hOnormal : (O.subgroupOf M).Normal := by
    have hcomap : O.subgroupOf M = CFSG.oddCore M :=
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
    rw [hcomap]
    infer_instance
  have hOodd : Odd (Nat.card O) := by
    rw [hO, Subgroup.card_map_of_injective M.subtype_injective]
    exact CFSG.ComponentClassification.OddCore.odd_card M
  have hMJO : ((H ⊓ M : Subgroup G) : Set G) * (O : Set G) = (M : Set G) := by
    rw [hHM]
    exact hMfac.symm
  have hdoubly := (minimalLocalFailureSylowFixedPointsFromProperCommutingImages h hcomm).2.2.1
  have hrankg : ∀ g ∈ M, g ∉ H →
      CFSG.Open.pRank 2 (H ⊓ H.map (MulAut.conj g⁻¹).toMonoidHom) ≤ 1 :=
    fun g _ hg => ((pRank_inf_conj_eq_pair_twoRank hdoubly hbeta hg).trans hpairRank).le
  have hfactor := odd_factor_rank_one_intersections_force_three_involutions hescape huH huM
    huCentral ⟨h.local_datum.distinguished_mem, hzM⟩ hzCentral hu hz huz'
    (Subgroup.map_subtype_le _) hOnormal hOodd hMJO hrankg
  dsimp only at hfactor
  obtain ⟨⟨P, hP⟩, hinvP, -, -⟩ := hfactor.2 default
  have hu1 : u ≠ 1 := (orderOf_eq_prime_iff.mp hu).2
  have hz1 : z ≠ 1 := (orderOf_eq_prime_iff.mp hz).2
  have hcount := card_involutions_eq_three_of_image (P : Subgroup M) (by rw [hP]; exact hinvP)
    huz' hu1 hz1
  have : IsSimpleGroup G := hsimple
  have htwo := three_involution_centralizer_forces_two_rank_two
    (index_ne_two_of_isSimpleGroup hnonab) u hu P hcount
  obtain ⟨w, -, hall⟩ := CFSG.RankTwoShapes.rank_two_simple_involutions_conjugate hnonab htwo
  obtain ⟨g₁, hg₁⟩ := hall u hu
  obtain ⟨g₂, hg₂⟩ := hall z hz
  refine huclass ⟨g₂ * g₁⁻¹, ?_⟩
  calc rightConjugateElem z (g₂ * g₁⁻¹) = g₁ * (g₂⁻¹ * z * g₂) * g₁⁻¹ := by
        simp only [rightConjugateElem]
        group
    _ = g₁ * (g₁⁻¹ * u * g₁) * g₁⁻¹ := by rw [hg₂, hg₁]
    _ = u := by group

theorem minimalLocalFailure_pair_involution_hull_rank_at_least_two
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hpairRank : twoRank (pairPointStabilizer H beta) = 1)
    {u : G} (huB : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H) :
    let M := Subgroup.centralizer ({u} : Set G)
    let L := Subgroup.closure (conjugacyWithin M z)
    2 ≤ twoRank L := by
  intro M L
  have hclass := (minimalLocalFailure_arbitrary_involution_centralizer_hull h hcomm hsmallerR1
    (pairPointStabilizer_le_point H beta huB) hu huz hescape).2.2.2.1
  have hL : L = localInvolutionPointHull z u := by
    change Subgroup.closure (conjugacyWithin M z) =
      Subgroup.closure (involutionPointClass z ∩ (M : Set G))
    rw [hclass]
  rw [hL]
  exact two_le_twoRank_localInvolutionPointHull_of_pair_rank_one h hcomm hsmallerR1 beta hbeta
    hpairRank huB hu huz hescape

end CFSG.ProperTwoGeneratedCore.RankOnePair
