module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Five

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

@[expose] def L34StandardEvenInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog G → ∀ L : Subgroup G, IsStandardSubgroup L →
      Blueprint.LieModel (L ⧸ center L) .PSL 3 2 2 → Even (Nat.card (center L)) →
      Nonempty (G ≃* Blueprint.NativeSporadic.Suz) ∨
        Nonempty (G ≃* Blueprint.NativeSporadic.He) ∨
        Nonempty (G ≃* Blueprint.NativeSporadic.ON)

end CFSG.ComponentClassification.GSThmB

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem even_card_center_of_mem_zStarIn {J : Subgroup G} (hq : IsQuasisimple J)
    (hO : oddIn J ≤ (center ↥J).map J.subtype) {u : G} (hu2 : orderOf u = 2)
    (hu : u ∈ zStarIn J) : Even (Nat.card (center ↥J)) := by
  have hO' : pPrimeCore 2 ↥J ≤ center ↥J := by
    intro y hy
    obtain ⟨w, hw, hwy⟩ := hO ⟨y, hy, rfl⟩
    rwa [← Subtype.ext hwy]
  have heq := fusionZStar_eq_center_of_le hq.1.commutator_eq_top hO'
  obtain ⟨w, hw, rfl⟩ := hu
  rw [heq] at hw
  have hw2 : orderOf w = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hu2
  have h1 := orderOf_dvd_natCard (⟨w, hw⟩ : center ↥J)
  rw [Subgroup.orderOf_mk, hw2] at h1
  exact even_iff_two_dvd.mpr h1

theorem not_isStandardSubgroup_of_l34_even
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hStd : GSThmB.L34StandardEvenInput)
    (hbase : L34BaseSetting G) {J : Subgroup G} (htype : IsL34Type (J ⧸ Open.fusionZStar J))
    (hst : IsStandardSubgroup J) (hO : oddIn J ≤ (center ↥J).map J.subtype)
    (hev : Even (Nat.card (center ↥J))) : False := by
  have : IsSimpleGroup G := hbase.1
  exact false_of_l34StandardOutcome hU hbase
    (hStd G hbase.2.1 hbase.2.2.1 J hst (lieModel_center_of_isStandardSubgroup htype hst hO) hev)

theorem not_isStandardSubgroup_of_mem_zStarIn
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hStd : GSThmB.L34StandardEvenInput)
    (hbase : L34BaseSetting G) {J : Subgroup G} (htype : IsL34Type (J ⧸ Open.fusionZStar J))
    {u : G} (hu2 : orderOf u = 2) (hu : u ∈ zStarIn J) (hst : IsStandardSubgroup J)
    (hO : oddIn J ≤ (center ↥J).map J.subtype) : False :=
  not_isStandardSubgroup_of_l34_even hU hStd hbase htype hst hO
    (even_card_center_of_mem_zStarIn hst.1 hO hu2 hu)

end CFSG.ComponentClassification.GrSLit.GrS5
