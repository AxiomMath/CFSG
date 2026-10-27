module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.OutHom
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Util.Perfect
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial

theorem perfect_of_simple_nonab {G : Type*} [Group G] {S : Subgroup G} (hS : IsSimpleGroup ↥S)
    (hnab : ∃ a b : ↥S, a * b ≠ b * a) : Group.IsPerfect ↥S :=
  CFSG.EvenSporadicStandard.HSStd.InvCent.isPerfect_of_simple_of_nonab hS (by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨a, a.2, b, b.2, fun h' => hab (Subtype.ext h')⟩)

theorem equiv_commutator_commutator {G : Type*} [Group G] {S : Subgroup G}
    (h : ⁅commutator G, commutator G⁆ = S) :
    Nonempty (↥(commutator ↥(commutator G)) ≃* ↥S) :=
  ⟨(Subgroup.equivMapOfInjective _ (commutator G).subtype (commutator G).subtype_injective).trans
    (MulEquiv.subgroupCongr ((Subgroup.map_subtype_commutator (commutator G)).trans h))⟩

theorem card_outer_L225 {S : Type} [Group S] (h : LieModel S .PSL 2 5 2) :
    Nat.card (Outer S) ∣ 4 := by
  have hM := h.statedClassicalModel_of_ne_zero (by norm_num)
  exact ((linear_model_outer_two_part_bound S 2 5 2 hM).2.2.2.1 rfl).trans (by decide)

theorem card_outer_L35 {S : Type} [Group S] (h : LieModel S .PSL 3 5 1) :
    Nat.card (Outer S) ∣ 4 := by
  have hM := h.statedClassicalModel_of_ne_zero (by norm_num)
  exact ((linear_model_outer_two_part_bound S 3 5 1 hM).2.2.2.2 (by norm_num)).trans (by decide)

theorem card_outer_L34 {S : Type} [Group S] (h : LieModel S .PSL 3 2 2) :
    Nat.card (Outer S) ∣ 12 := by
  have hM := h.statedClassicalModel_of_ne_zero (by norm_num)
  exact ((linear_model_outer_two_part_bound S 3 2 2 hM).2.2.2.2 (by norm_num)).trans (by decide)

theorem card_outer_U35 {S : Type} [Group S] (h : LieModel S .PSU 3 5 1) :
    Nat.card (Outer S) ∣ 12 := by
  have hM := h.statedClassicalModel_of_ne_zero (by norm_num)
  rw [(unitary_model_outer_two_part_bound S 3 5 1 hM).2.2.1]
  decide

theorem lieModel_commutator_of_L225 {G : Type} [Group G] [Finite G] {S : Subgroup G}
    (hSn : S.Normal) (hS : IsSimpleGroup ↥S) (hnab : ∃ a b : ↥S, a * b ≠ b * a)
    (hcent : centralizer (S : Set G) = ⊥) (hL : LieModel ↥S .PSL 2 5 2) :
    LieModel ↥(commutator G) .PSL 2 5 2 := by
  haveI := hSn
  have hperf := perfect_of_simple_nonab hS hnab
  have heq : commutator G = S :=
    le_antisymm (commutator_le_of_card_outer_dvd_four hcent (card_outer_L225 hL))
      (le_commutator_of_perfect hperf)
  exact LieModel.of_mulEquiv (MulEquiv.subgroupCongr heq.symm) hL

theorem lieModel_commutator_of_L35 {G : Type} [Group G] [Finite G] {S : Subgroup G}
    (hSn : S.Normal) (hS : IsSimpleGroup ↥S) (hnab : ∃ a b : ↥S, a * b ≠ b * a)
    (hcent : centralizer (S : Set G) = ⊥) (hL : LieModel ↥S .PSL 3 5 1) :
    LieModel ↥(commutator G) .PSL 3 5 1 := by
  haveI := hSn
  have hperf := perfect_of_simple_nonab hS hnab
  have heq : commutator G = S :=
    le_antisymm (commutator_le_of_card_outer_dvd_four hcent (card_outer_L35 hL))
      (le_commutator_of_perfect hperf)
  exact LieModel.of_mulEquiv (MulEquiv.subgroupCongr heq.symm) hL

theorem lieModel_commutator_commutator_of_U35 {G : Type} [Group G] [Finite G] {S : Subgroup G}
    (hSn : S.Normal) (hS : IsSimpleGroup ↥S) (hnab : ∃ a b : ↥S, a * b ≠ b * a)
    (hcent : centralizer (S : Set G) = ⊥) (hL : LieModel ↥S .PSU 3 5 1) :
    LieModel ↥(commutator ↥(commutator G)) .PSU 3 5 1 := by
  haveI := hSn
  have hperf := perfect_of_simple_nonab hS hnab
  have heq : ⁅commutator G, commutator G⁆ = S :=
    le_antisymm (commutator_commutator_le_of_card_outer_dvd_twelve hcent (card_outer_U35 hL))
      (le_commutator_commutator_of_perfect hperf)
  obtain ⟨e⟩ := equiv_commutator_commutator heq
  exact LieModel.of_mulEquiv e.symm hL

theorem lieModel_commutator_commutator_of_L34 {G : Type} [Group G] [Finite G] {S : Subgroup G}
    (hSn : S.Normal) (hS : IsSimpleGroup ↥S) (hnab : ∃ a b : ↥S, a * b ≠ b * a)
    (hcent : centralizer (S : Set G) = ⊥) (hL : LieModel ↥S .PSL 3 2 2) :
    LieModel ↥(commutator ↥(commutator G)) .PSL 3 2 2 := by
  haveI := hSn
  have hperf := perfect_of_simple_nonab hS hnab
  have heq : ⁅commutator G, commutator G⁆ = S :=
    le_antisymm (commutator_commutator_le_of_card_outer_dvd_twelve hcent (card_outer_L34 hL))
      (le_commutator_commutator_of_perfect hperf)
  obtain ⟨e⟩ := equiv_commutator_commutator heq
  exact LieModel.of_mulEquiv e.symm hL

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harada
