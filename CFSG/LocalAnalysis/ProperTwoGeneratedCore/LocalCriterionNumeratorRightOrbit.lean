module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorEquivariant
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeFixedSets

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.BenderSuzuki.PFchapter1section1

universe u v w

variable {G : Type u} [Group G]

@[expose] def numeratorRightOrbit (H L : Subgroup G) (a : pointRightCosetSpace H) :
    Set (pointRightCosetSpace H) :=
  {x | ∃ l ∈ L, pointRightCosetMul H a l = x}

theorem numeratorRightOrbit_base (H L : Subgroup G) (a : pointRightCosetSpace H) :
    a ∈ numeratorRightOrbit H L a :=
  ⟨1, L.one_mem, pointRightCosetMul_one H a⟩

theorem numeratorRightOrbit_stable (H L : Subgroup G) (a : pointRightCosetSpace H) :
    ∀ l ∈ L, ∀ x ∈ numeratorRightOrbit H L a,
      pointRightCosetMul H x l ∈ numeratorRightOrbit H L a := by
  rintro l hl x ⟨k, hk, rfl⟩
  exact ⟨k * l, L.mul_mem hk hl, (pointRightCosetMul_mul H a k l).symm⟩

@[expose, instance_reducible] def numeratorRightOrbitAction
    (H L : Subgroup G) (a : pointRightCosetSpace H) :
    MulAction L (numeratorRightOrbit H L a) :=
  pointInvariantSetInverseRightAction H L (numeratorRightOrbit H L a)
    (numeratorRightOrbit_stable H L a)

theorem numeratorRightOrbitAction_transitive (H L : Subgroup G) (a : pointRightCosetSpace H) :
    letI := numeratorRightOrbitAction H L a
    MulAction.IsPretransitive L (numeratorRightOrbit H L a) := by
  let := numeratorRightOrbitAction H L a
  constructor
  rintro ⟨x, k, hk, rfl⟩ ⟨y, l, hl, rfl⟩
  refine ⟨⟨l⁻¹ * k, L.mul_mem (L.inv_mem hl) hk⟩, ?_⟩
  apply Subtype.ext
  change pointRightCosetMul H (pointRightCosetMul H a k) (l⁻¹ * k)⁻¹ =
    pointRightCosetMul H a l
  rw [pointRightCosetMul_mul]
  congr 1
  group

theorem numeratorRightOrbitAction_stabilizer (H L : Subgroup G) (a : pointRightCosetSpace H)
    (x : numeratorRightOrbit H L a) :
    letI := numeratorRightOrbitAction H L a
    MulAction.stabilizer L x = (rightCosetStabilizer H x.val).subgroupOf L := by
  let := numeratorRightOrbitAction H L a
  ext l
  rw [MulAction.mem_stabilizer_iff]
  change (⟨pointRightCosetMul H x.val l.val⁻¹, _⟩ : numeratorRightOrbit H L a) = x ↔
    l.val ∈ rightCosetStabilizer H x.val
  rw [Subtype.ext_iff, ← mem_point_right_stabilizer_iff]
  exact (rightCosetStabilizer H x.val).inv_mem_iff

theorem original_right_orbit_model_identification
    [Finite G] {F : Type v} [Group F] [Finite F] {Ξ : Type w} [MulAction F Ξ]
    (H L : Subgroup G) (a : pointRightCosetSpace H)
    (hP : fusionStronglyEmbedded ((rightCosetStabilizer H a).subgroupOf L))
    (hrank : TwoRankAtLeastTwo F) (htrans : MulAction.IsPretransitive F Ξ)
    (b : Ξ) (hB : fusionStronglyEmbedded (MulAction.stabilizer F b)) (e : L ≃* F) :
    letI := numeratorRightOrbitAction H L a
    ∃ (E : L ≃* F) (f : numeratorRightOrbit H L a ≃ Ξ),
      ((rightCosetStabilizer H a).subgroupOf L).map E.toMonoidHom =
        MulAction.stabilizer F b ∧
      f ⟨a, numeratorRightOrbit_base H L a⟩ = b ∧
      ∀ (l : L) (x : numeratorRightOrbit H L a), f (l • x) = E l • f x := by
  let := numeratorRightOrbitAction H L a
  let aΓ : numeratorRightOrbit H L a := ⟨a, numeratorRightOrbit_base H L a⟩
  have hstab : MulAction.stabilizer L aΓ =
      (rightCosetStabilizer H a).subgroupOf L :=
    numeratorRightOrbitAction_stabilizer H L a aΓ
  have ha : fusionStronglyEmbedded (MulAction.stabilizer L aΓ) := hstab.symm ▸ hP
  obtain ⟨E, f, hE, hf, hequiv⟩ := strong_embedding_transitive_action_identification
    hrank (numeratorRightOrbitAction_transitive H L a) htrans aΓ b ha hB e
  exact ⟨E, f, hstab ▸ hE, hf, hequiv⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
