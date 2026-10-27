module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSetAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointOppositePair

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSet
open scoped Pointwise

variable {G : Type*} [Group G]

theorem point_subgroup_transitive_of_original_double_transitivity
    (H : Subgroup G)
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (b c : pointRightCosetSpace H)
    (hb : b ≠ rightCosetMk H 1) (hc : c ≠ rightCosetMk H 1) :
    ∃ g ∈ H, pointRightCosetMul H b g = c := by
  obtain ⟨g, hgbase, hgb⟩ := hdoubly (rightCosetMk H 1) b (rightCosetMk H 1) c
    hb.symm hc.symm
  exact ⟨g, (point_right_base_fixed_iff H g).mp hgbase, hgb⟩

theorem point_subgroup_eq_pair_mul_full_centralizer [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : pointRightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1) :
    (H : Set G) = (Subgroup.centralizer ({z} : Set G) : Set G) *
        (pairPointStabilizer H beta : Set G) ∧
      (H : Set G) = (pairPointStabilizer H beta : Set G) *
        (Subgroup.centralizer ({z} : Set G) : Set G) := by
  obtain ⟨t, ht⟩ := original_pair_flip_exists h beta hbeta
  have hfactor := point_subgroup_eq_centralizer_mul_inverted_set h S hzS hzcenter hbeta ht
  have hCB : (H : Set G) = (Subgroup.centralizer ({z} : Set G) : Set G) *
      (pairPointStabilizer H beta : Set G) := by
    ext g
    constructor
    · intro hg
      rw [hfactor] at hg
      obtain ⟨c, hc, i, hi, rfl⟩ := Set.mem_mul.mp hg
      exact Set.mem_mul.mpr ⟨c, hc, i, (pairOddCore_le H beta t).1 hi.1, rfl⟩
    · intro hg
      obtain ⟨c, hc, b, hb, rfl⟩ := Set.mem_mul.mp hg
      exact H.mul_mem (point_centralizer_le h hc) ((pairPointStabilizer_le_point H beta) hb)
  refine ⟨hCB, ?_⟩
  ext g
  constructor
  · intro hg
    have hinv : g⁻¹ ∈ (H : Set G) := H.inv_mem hg
    rw [hCB] at hinv
    obtain ⟨c, hc, b, hb, hcb⟩ := Set.mem_mul.mp hinv
    refine Set.mem_mul.mpr ⟨b⁻¹, (pairPointStabilizer H beta).inv_mem hb,
      c⁻¹, (Subgroup.centralizer ({z} : Set G)).inv_mem hc, ?_⟩
    simpa only [mul_inv_rev, inv_inv] using congrArg Inv.inv hcb
  · intro hg
    obtain ⟨b, hb, c, hc, rfl⟩ := Set.mem_mul.mp hg
    exact H.mul_mem ((pairPointStabilizer_le_point H beta) hb) (point_centralizer_le h hc)

theorem full_centralizer_transitive_on_original_nonbase_points [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d) :
    ∀ b c : pointRightCosetSpace H,
      b ≠ rightCosetMk H 1 → c ≠ rightCosetMk H 1 →
        ∃ g ∈ Subgroup.centralizer ({z} : Set G), pointRightCosetMul H b g = c := by
  intro b c hb hc
  obtain ⟨g, hgH, hgc⟩ := point_subgroup_transitive_of_original_double_transitivity H hdoubly b c hb hc
  have hg : g ∈ (H : Set G) := hgH
  rw [(point_subgroup_eq_pair_mul_full_centralizer h S hzS hzcenter hb).2] at hg
  obtain ⟨a, ha, n, hn, rfl⟩ := Set.mem_mul.mp hg
  have hab : pointRightCosetMul H b a = b :=
    (mem_point_right_stabilizer_iff H b a).mp ha.2
  refine ⟨n, hn, ?_⟩
  rwa [← pointRightCosetMul_mul, hab] at hgc

end CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
