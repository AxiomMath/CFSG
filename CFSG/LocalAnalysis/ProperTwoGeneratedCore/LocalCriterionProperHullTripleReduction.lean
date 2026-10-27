module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullConfinement
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullZStar
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFreeFixedPoints

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

theorem properHull_normalizer_escape_centralizes
    {H W : Subgroup G} {z : G} (hzH : z ∈ H)
    (htriple : distinguishedTripleCentralization H z)
    (hWH : W ≤ H) (hzW : z ∈ Subgroup.normalizer (W : Set G))
    (b : G) (hb : b ∈ Subgroup.normalizer (W : Set G)) (hbH : b ∉ H) :
    W ≤ Subgroup.centralizer ({z} : Set G) := by
  let alpha := rightCosetMk H 1
  let beta := pointRightCosetMul H alpha b
  have hbeta : beta ≠ alpha := fun heq =>
    hbH ((point_right_base_fixed_iff H b).mp heq)
  have hfix : pointRightCosetMul H alpha z = alpha :=
    (point_right_base_fixed_iff H z).mpr hzH
  have hWbeta : W ≤ rightCosetStabilizer H beta := by
    intro w hw
    exact (mem_point_right_stabilizer_iff H beta w).mpr
      (normalizer_orbit_point_fixed hWH hb hw)
  have hWbetaFix : beta ∈ pointFixedSet H W :=
    (mem_pointFixedSet_iff H W beta).mpr hWbeta
  have hWbetaZ : W ≤ rightCosetStabilizer H (pointRightCosetMul H beta z) :=
    (mem_pointFixedSet_iff H W _).mp
      (normalizer_preserves_pointFixedSet hzW hWbetaFix)
  have hWalpha : W ≤ rightCosetStabilizer H alpha := by
    rw [rightCosetStabilizer_base]
    exact hWH
  have hle := le_inf (le_inf hWalpha hWbeta) hWbetaZ
  rw [htriple z (distinguished_mem_pointClass z) alpha beta hfix hbeta] at hle
  exact hle.trans inf_le_right

theorem properHull_normal_subgroup_centralizer
    (Y R : Subgroup G) {z : G} (hRY : R ≤ Y)
    (hnormal : (R.subgroupOf Y).Normal)
    (hRz : R ≤ Subgroup.centralizer ({z} : Set G)) :
    properHull Y z ≤ Subgroup.centralizer (R : Set G) := by
  have hYn : Y ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRY).mp hnormal
  apply (Subgroup.closure_le _).mpr
  rintro t ⟨y, rfl⟩
  apply Subgroup.mem_centralizer_iff.mpr
  intro r hr
  have hconjR : (y : G) * r * (y : G)⁻¹ ∈ R :=
    (Subgroup.mem_normalizer_iff.mp (hYn y.property) r).mp hr
  have hcomm : Commute ((y : G) * r * (y : G)⁻¹) z :=
    Subgroup.mem_centralizer_singleton_iff.mp (hRz hconjR)
  have hconj := hcomm.conj (y : G)⁻¹
  simpa only [rightConjugateElem, inv_inv, mul_assoc, inv_mul_cancel_left,
    inv_mul_cancel, mul_one] using hconj.eq

variable [Finite G]

theorem properHull_rank_two_oddCore_centralizer_of_triple
    {H Y : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (htriple : distinguishedTripleCentralization H z)
    (hY : Y < ⊤) (hzY : z ∈ Y) (hescape : ¬ Y ≤ H)
    (hrank : 2 ≤ twoRank (properHull Y z)) :
    properOddCore Y ≤ Subgroup.centralizer ({z} : Set G) := by
  obtain ⟨b, hbY, hbH⟩ := IsConcreteLE.not_le_iff_exists.mp hescape
  exact properHull_normalizer_escape_centralizes h.local_datum.distinguished_mem htriple
    (properHull_rank_two_entire_oddCore_le_point h hY hzY hescape hrank)
    (subgroup_normalizes_properOddCore Y hzY) b
    (subgroup_normalizes_properOddCore Y hbY) hbH

theorem properHull_rank_two_entire_oddCore_commutator_of_triple
    {H Y : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (htriple : distinguishedTripleCentralization H z)
    (hY : Y < ⊤) (hzY : z ∈ Y) (hescape : ¬ Y ≤ H)
    (hrank : 2 ≤ twoRank (properHull Y z)) :
    ⁅properOddCore Y, properHull Y z⁆ = ⊥ := by
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (properHull_normal_subgroup_centralizer Y (properOddCore Y) (properOddCore_le Y)
      (properOddCore_normal_in_subgroup Y)
      (properHull_rank_two_oddCore_centralizer_of_triple h htriple hY hzY hescape hrank))

theorem properHull_rank_one_point_eq_centralizer_of_triple
    {H Y : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (htriple : distinguishedTripleCentralization H z)
    (hY : Y < ⊤) (hzY : z ∈ Y) (hescape : ¬ Y ≤ H)
    (hrank : twoRank (properHull Y z) ≤ 1) :
    H ⊓ Y = Y ⊓ Subgroup.centralizer ({z} : Set G) := by
  obtain ⟨W, hWL, _, hWnormal, hproduct, hWescape⟩ :=
    properHull_rank_one_solvable_supplement h hY hzY hescape hrank
  have hHWnorm : H ⊓ properHull Y z ≤ Subgroup.normalizer (W : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWL).mp hWnormal
  have hzW : z ∈ Subgroup.normalizer (W : Set G) :=
    hHWnorm ⟨h.local_datum.distinguished_mem, distinguished_mem_properHull Y z⟩
  obtain ⟨b, hb, hbH⟩ := IsConcreteLE.not_le_iff_exists.mp hWescape
  have hWz : W ≤ Subgroup.centralizer ({z} : Set G) :=
    properHull_normalizer_escape_centralizes h.local_datum.distinguished_mem htriple
      (hWL.trans inf_le_left) hzW b hb.1 hbH
  have hHLz : H ⊓ properHull Y z ≤ Subgroup.centralizer ({z} : Set G) := by
    intro x hx
    have hx' : x ∈ (H ⊓ properHull Y z : Set G) := hx
    rw [hproduct] at hx'
    obtain ⟨w, hw, c, hc, rfl⟩ := hx'
    exact (Subgroup.centralizer ({z} : Set G)).mul_mem (hWz hw) hc.2
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ ((H ⊓ Y : Subgroup G) : Set G) := hx
    rw [properHull_point_factorization h.local_datum hzY hescape] at hx'
    obtain ⟨c, hc, l, hl, rfl⟩ := hx'
    exact ⟨Y.mul_mem hc.1 (properHull_le Y hzY hl.2),
      (Subgroup.centralizer ({z} : Set G)).mul_mem hc.2 (hHLz hl)⟩
  · exact le_inf (inf_le_right.trans (point_centralizer_le h.local_datum)) inf_le_left

end CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
