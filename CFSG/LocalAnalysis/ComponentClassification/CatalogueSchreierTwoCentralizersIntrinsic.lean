module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierTwoCentralizersConjugacy
public import CFSG.LocalAnalysis.ComponentClassification.ZStarTransport

public section

namespace CFSG.ComponentClassification.CatalogueSchreierTwoCentralizers

open OuterAutomorphisms
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def intrinsicCentralizer (T : Subgroup G) : Subgroup G :=
  Subgroup.centralizer (CFSG.centerIn T : Set G)

theorem intrinsicCentralizer_map {H : Type*} [Group H] (equivalence : G ≃* H)
    (T : Subgroup G) :
    (intrinsicCentralizer T).map equivalence.toMonoidHom =
      intrinsicCentralizer (T.map equivalence.toMonoidHom) := by
  unfold intrinsicCentralizer
  rw [UniversalComponentBlock.subgroup_centralizer_map]
  rw [CFSG.centerIn_eq_map_center, ZStarTransport.mapped_center,
    CFSG.centerIn_eq_map_center]

theorem sylow_image_eq_conjugate [Finite G] (p : ℕ) [Fact p.Prime]
    (T : Sylow p G) (automorphism : MulAut G) :
    ∃ element : G, (T : Subgroup G).map automorphism.toMonoidHom =
      (T : Subgroup G).map (MulAut.conj element).toMonoidHom := by
  obtain ⟨element, helement⟩ := MulAction.exists_smul_eq G T (automorphism • T)
  refine ⟨element, ?_⟩
  have hsubgroup := congrArg (fun P : Sylow p G => (P : Subgroup G)) helement.symm
  have haction (action : MulAut G) :
      (MulDistribMulAction.toMonoidEnd (MulAut G) G) action = action.toMonoidHom := by
    ext member
    rfl
  simpa only [Sylow.pointwise_smul_def, Sylow.coe_subgroup_smul,
    Subgroup.pointwise_smul_def, haction] using hsubgroup

theorem intrinsicCentralizer_conjugacyInvariant [Finite G] (p : ℕ) [Fact p.Prime]
    (T : Sylow p G) : ConjugacyInvariant (intrinsicCentralizer (T : Subgroup G)) := by
  intro automorphism
  obtain ⟨element, helement⟩ := sylow_image_eq_conjugate p T automorphism
  refine ⟨element, ?_⟩
  rw [intrinsicCentralizer_map, intrinsicCentralizer_map, helement]

theorem intrinsic_two_centralizer_schreier (G : Type*) [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (T : Sylow p G) (t : G)
    (ht : t ∈ intrinsicCentralizer (T : Subgroup G))
    (hgenerate : intrinsicCentralizer (T : Subgroup G) ⊔ secondCentralizer t = ⊤)
    [Group.IsSolvable (Outer (intrinsicCentralizer (T : Subgroup G)))]
    [Group.IsSolvable (Outer (secondCentralizer t))]
    [Group.IsSolvable (intersectionCentralizer (intrinsicCentralizer (T : Subgroup G)) t)] :
    Group.IsSolvable (Outer G) :=
  conjugacy_invariant_two_centralizer_schreier G (intrinsicCentralizer (T : Subgroup G))
    (intrinsicCentralizer_conjugacyInvariant p T) t ht hgenerate

end CFSG.ComponentClassification.CatalogueSchreierTwoCentralizers
