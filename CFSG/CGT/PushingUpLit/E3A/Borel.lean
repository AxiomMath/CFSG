module

public import CFSG.RankThree.PartOne.S12.PushingUp
public import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.CGT.PushingUpLit.E3A

open CFSG CFSG.RankThree.PartOne

theorem isPerfect_alternatingGroup_odd {n : ℕ} (hn : 2 ≤ n) :
    Group.IsPerfect (alternatingGroup (Fin (2 * n + 1))) := by
  refine ⟨commutator_alternatingGroup_eq_top ?_⟩
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

theorem not_isSolvable_of_block {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (hnat : IsNaturalAltModule X n) : ¬ Group.IsSolvable X := by
  intro hsolv
  obtain ⟨f, -⟩ := hnat
  have hq : Group.IsSolvable (X ⧸ pCore 2 X) := inferInstance
  have hA : Group.IsSolvable (alternatingGroup (Fin (2 * n + 1))) :=
    Group.isSolvable_of_isSolvable_injective (f := f.symm.toMonoidHom) f.symm.injective
  have := isPerfect_alternatingGroup_odd hn
  have hnt : Nontrivial (alternatingGroup (Fin (2 * n + 1))) :=
    alternatingGroup.nontrivial_of_three_le_card (by
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
      omega)
  exact Group.IsPerfect.not_isSolvable _ hA

theorem isSolvable_normalizer_sylow {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) :
    Group.IsSolvable ↥(Subgroup.normalizer ((S : Subgroup G) : Set G)) := by
  set N : Subgroup G := Subgroup.normalizer ((S : Subgroup G) : Set G) with hN
  have hSN : (S : Subgroup G) ≤ N := Subgroup.le_normalizer
  have hnorm : ((S : Subgroup G).subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSN).2 le_rfl
  have hp : IsPGroup 2 ((S : Subgroup G).subgroupOf N) :=
    S.isPGroup'.comap_of_injective N.subtype N.subtype_injective
  have h1 : Group.IsSolvable ↥((S : Subgroup G).subgroupOf N) := by
    have := hp.isNilpotent
    infer_instance
  have hodd : Odd (Nat.card (↥N ⧸ (S : Subgroup G).subgroupOf N)) := by
    show Odd ((S : Subgroup G).relIndex N)
    have hrel : (S : Subgroup G).relIndex N ∣ (S : Subgroup G).index := by
      rw [← Subgroup.relIndex_mul_index hSN]
      exact dvd_mul_right _ _
    have h2 : ¬ 2 ∣ (S : Subgroup G).relIndex N := fun h =>
      S.not_dvd_index (h.trans hrel)
    exact Nat.odd_iff.2 (by omega)
  have h3 : Group.IsSolvable (↥N ⧸ (S : Subgroup G).subgroupOf N) :=
    CFSG.Milestones.odd_order_solvable hodd
  exact Group.isSolvable_of_ker_le_range ((S : Subgroup G).subgroupOf N).subtype
    (QuotientGroup.mk' ((S : Subgroup G).subgroupOf N)) (by simp)

theorem false_of_le_normalizer_sylow {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (S : Sylow 2 G) {n : ℕ} (hn : 2 ≤ n)
    (hX : X ≤ Subgroup.normalizer ((S : Subgroup G) : Set G))
    (hnat : IsNaturalAltModule ↥X n) : False := by
  have hsolv := isSolvable_normalizer_sylow S
  have : Group.IsSolvable ↥X :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hX)
  exact not_isSolvable_of_block hn hnat this

end CFSG.CGT.PushingUpLit.E3A
