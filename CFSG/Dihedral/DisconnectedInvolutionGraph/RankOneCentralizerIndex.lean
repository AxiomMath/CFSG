module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneCentralConjugates

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem rank_one_two_central_coset_centralizer_index
    (hpgroup : IsPGroup 2 G) (hrank : NoCommutingDistinctInvolutions G)
    (hnonabelian : ∃ first second : G, first * second ≠ second * first)
    (element : G)
    (hcosetCentral : QuotientGroup.mk' (Subgroup.center G) element ∈
      Subgroup.center (G ⧸ Subgroup.center G))
    (hcosetOrder : orderOf (QuotientGroup.mk' (Subgroup.center G) element) = 2) :
    (Subgroup.centralizer {element}).index = 2 := by
  classical
  have hnoncentral : element ∉ Subgroup.center G := by
    intro hmem
    have hone := (QuotientGroup.eq_one_iff element).mpr hmem
    change QuotientGroup.mk' (Subgroup.center G) element = 1 at hone
    rw [hone, orderOf_one] at hcosetOrder
    omega
  obtain ⟨actor, hnoncommute⟩ : ∃ actor : G, actor * element ≠ element * actor := by
    by_contra hmissing
    push Not at hmissing
    exact hnoncentral (Subgroup.mem_center_iff.mpr hmissing)
  have hactorConjugate : actor * element * actor⁻¹ = element⁻¹ := by
    rcases rank_one_two_central_coset_conjugates hpgroup hrank hnonabelian element
      hcosetCentral hcosetOrder actor with hfixed | hinverse
    · exact (hnoncommute (mul_inv_eq_iff_eq_mul.mp hfixed)).elim
    · exact hinverse
  have helementNeInverse : element ≠ element⁻¹ := by
    intro heq
    exact hnoncommute (mul_inv_eq_iff_eq_mul.mp (hactorConjugate.trans heq.symm))
  have horbit : MulAction.orbit (ConjAct G) element = {element, element⁻¹} := by
    ext other
    constructor
    · intro hmem
      obtain ⟨mover, hmover⟩ := MulAction.mem_orbit_iff.mp hmem
      obtain ⟨mover, rfl⟩ := ConjAct.toConjAct.surjective mover
      rw [ConjAct.toConjAct_smul] at hmover
      rcases rank_one_two_central_coset_conjugates hpgroup hrank hnonabelian element
        hcosetCentral hcosetOrder mover with hfixed | hinverse
      · exact Set.mem_insert_iff.mpr (Or.inl (hmover.symm.trans hfixed))
      · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr
          (hmover.symm.trans hinverse)))
    · intro hmem
      rcases hmem with rfl | hmem
      · exact MulAction.mem_orbit_self _
      · have heq := Set.mem_singleton_iff.mp hmem
        subst other
        exact MulAction.mem_orbit_iff.mpr ⟨ConjAct.toConjAct actor, by
          rw [ConjAct.toConjAct_smul, hactorConjugate]⟩
  have horbitCard : Nat.card (MulAction.orbit (ConjAct G) element) = 2 := by
    rw [horbit]
    exact Set.ncard_pair helementNeInverse
  calc
    (Subgroup.centralizer {element}).index =
        ((MulAction.stabilizer (ConjAct G) element).comap
          (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom).index :=
      congrArg Subgroup.index (Subgroup.centralizer_eq_comap_stabilizer element)
    _ = (MulAction.stabilizer (ConjAct G) element).index :=
      Subgroup.index_comap_of_surjective
        (f := (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom) _
        (ConjAct.toConjAct : G ≃* ConjAct G).surjective
    _ = Nat.card (MulAction.orbit (ConjAct G) element) :=
      (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (ConjAct G) element)).symm
    _ = 2 := horbitCard

end CFSG.DisconnectedInvolutionGraph.Helpers
