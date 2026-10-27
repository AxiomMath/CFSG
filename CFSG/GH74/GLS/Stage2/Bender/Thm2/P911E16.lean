module

public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic
import CFSG.LocalAnalysis.ComponentInitial.FieldFourCoverMatrices
import CFSG.RankThree.OddKernel.OddLift
import CFSG.RankThree.PartOne.AUTSL.Interface
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

private theorem isElementaryAbelian_two_of {X : Type*} [Group X] {A : Subgroup X}
    (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (h2 : ∀ a ∈ A, a ^ 2 = 1) :
    IsElementaryAbelian 2 ↥A := CFSG.IsElementaryAbelian.of_forall hc h2

private theorem exists_elemAb16_projectiveSL {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) :
    ∃ E : Subgroup (projectiveSL 3 K), IsElementaryAbelian 2 ↥E ∧ Nat.card ↥E = 16 := by
  refine ⟨projRad K 0, isElementaryAbelian_two_of
    (fun a ha b hb => commute_of_mem_projRad 0 ha hb)
    (fun a ha => sq_eq_one_of_mem_projRad hK 0 ha), ?_⟩
  rw [card_projRad, hK]

theorem exists_elemAb16_of_lieModel {X : Type} [Group X] (h : LieModel X .PSL 3 2 2) :
    ∃ E : Subgroup X, IsElementaryAbelian 2 ↥E ∧ Nat.card ↥E = 16 := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel h
  obtain ⟨E, hE, hE16⟩ := exists_elemAb16_projectiveSL (K := K) (by rw [hK]; norm_num)
  have := hE
  refine ⟨E.map e.symm.toMonoidHom, IsElementaryAbelian.map e.symm.toMonoidHom, ?_⟩
  rw [Subgroup.card_map_of_injective e.symm.injective, hE16]

theorem exists_lift_elemAb16 {G : Type*} [Group G] [Finite G] (Z : Subgroup G) [Z.Normal]
    (hZ : Odd (Nat.card Z)) {E : Subgroup (G ⧸ Z)} (hE : IsElementaryAbelian 2 ↥E)
    (hE16 : Nat.card ↥E = 16) :
    ∃ V : Subgroup G, IsElementaryAbelian 2 ↥V ∧ Nat.card ↥V = 16 := by
  have hEp : IsPGroup 2 ↥E := IsElementaryAbelian.isPGroup 2 ↥E
  have hker : Odd (Nat.card (QuotientGroup.mk' Z).ker) := by
    rw [QuotientGroup.ker_mk']
    exact hZ
  obtain ⟨A, -, hAE, hinj⟩ := CFSG.RankThree.OddKernel.exists_two_subgroup_map_eq
    (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z) hker E hEp
  have hmem : ∀ a ∈ A, QuotientGroup.mk' Z a ∈ E := fun a ha => hAE ▸ mem_map_of_mem _ ha
  have hmul : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => by
    have h1 : QuotientGroup.mk' Z (a * b) = QuotientGroup.mk' Z (b * a) := by
      rw [map_mul, map_mul]
      exact congrArg Subtype.val
        ((IsMulCommutative.is_comm (M := E)).comm ⟨_, hmem a ha⟩ ⟨_, hmem b hb⟩)
    exact congrArg Subtype.val (@hinj ⟨a * b, mul_mem ha hb⟩ ⟨b * a, mul_mem hb ha⟩ h1)
  have hsq : ∀ a ∈ A, a ^ 2 = 1 := fun a ha => by
    have h1 : QuotientGroup.mk' Z (a ^ 2) = QuotientGroup.mk' Z 1 := by
      rw [map_pow, map_one]
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) _ (hmem a ha)
    exact congrArg Subtype.val (@hinj ⟨a ^ 2, pow_mem ha 2⟩ ⟨1, one_mem A⟩ h1)
  refine ⟨A, isElementaryAbelian_two_of hmul hsq, ?_⟩
  rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, MonoidHom.range_comp, range_subtype,
    hAE, hE16]

theorem exists_elemAb16 {N : Type} [Group N] [Finite N] {J : Subgroup N} (hJ : IsComponent J)
    (hL : LieModel (↥J ⧸ Subgroup.center ↥J) .PSL 3 2 2)
    (hZ : Odd (Nat.card ↥(Subgroup.center ↥J))) :
    ∃ E : Subgroup N, E ≤ J ∧ IsElementaryAbelian 2 ↥E ∧ Nat.card ↥E = 16 := by
  have _ := hJ
  obtain ⟨Eb, hEb, hEb16⟩ := exists_elemAb16_of_lieModel hL
  obtain ⟨V, hV, hV16⟩ := exists_lift_elemAb16 (Subgroup.center ↥J) hZ hEb hEb16
  have := hV
  refine ⟨V.map J.subtype, Subgroup.map_subtype_le V, IsElementaryAbelian.map_subtype, ?_⟩
  rw [Subgroup.card_map_of_injective J.subtype_injective, hV16]

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
