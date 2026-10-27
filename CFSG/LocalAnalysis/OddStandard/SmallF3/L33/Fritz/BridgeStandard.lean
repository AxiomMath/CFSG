module

public import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.OddStandard.SmallF3.L33

open Subgroup CFSG.Blueprint CFSG.Open

@[expose] noncomputable def quotientCenterEquiv {G : Type} [Group G] {L : Subgroup G}
    (hZ : center L = ⊥) : ↥L ⧸ center ↥L ≃* ↥L :=
  (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot

theorem isSimple_of_standard_of_center_eq_bot {G : Type} [Group G] {L : Subgroup G}
    (hX : standardComponentIsStandard L) (hZ : center L = ⊥) : IsSimpleGroup ↥L := by
  have hs : IsSimpleGroup (↥L ⧸ center ↥L) := hX.1.2
  exact (quotientCenterEquiv hZ).symm.isSimpleGroup

theorem lieModel_of_center_eq_bot {G : Type} [Group G] {L : Subgroup G} (hZ : center L = ⊥)
    {t : StatedLieTag} {n p f : ℕ} (h : LieModel (↥L ⧸ center ↥L) t n p f) :
    LieModel ↥L t n p f :=
  LieModel.of_mulEquiv (quotientCenterEquiv hZ) h

theorem exists_involution_of_standard' {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hX : standardComponentIsStandard L) :
    ∃ t : G, t ∈ centralizer (L : Set G) ∧ orderOf t = 2 :=
  hX.exists_involution_centralizer

theorem le_centralizer_of_mem_centralizer {G : Type} [Group G] {L : Subgroup G} {t : G}
    (ht : t ∈ centralizer (L : Set G)) : L ≤ centralizer ({t} : Set G) := by
  intro l hl
  rw [mem_centralizer_singleton_iff]
  exact (mem_centralizer_iff.mp ht l hl)

theorem centralizer_le_normalizer_of_standard {G : Type} [Group G] {L : Subgroup G} {t : G}
    (hX : standardComponentIsStandard L) (ht : t ∈ centralizer (L : Set G))
    (ht2 : orderOf t = 2) : centralizer ({t} : Set G) ≤ normalizer (L : Set G) := by
  intro y hy
  exact hX.mem_normalizer_of_commute ht ht2 (mem_centralizer_singleton_iff.mp hy)

end CFSG.OddStandard.SmallF3.L33
