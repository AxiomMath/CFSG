module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Basic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.IVK.GHInv

open Subgroup CFSG CFSG.ABGLocalTools
open scoped commutatorElement

theorem eq_of_isCompIn_of_normal_quasisimple {X : Type} [Group X] [Finite X] {C S B : Subgroup X}
    (hS : IsQuasisimple ↥S) (hSC : S ≤ C) (hSn : ∀ x ∈ C, ∀ s ∈ S, x * s * x⁻¹ ∈ S)
    (hcomm : ∀ x ∈ C, ∀ z ∈ C, ⁅x, z⁆ ∈ S) (hB : IsCompIn C B) : B = S := by
  have hSCn : (S.subgroupOf C).Normal := ⟨fun s hs x => by
    rw [Subgroup.mem_subgroupOf] at hs ⊢
    exact hSn x x.2 s hs⟩
  have hSCq : IsQuasisimple ↥(S.subgroupOf C) :=
    LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hSC).symm hS
  have hSCc : IsComponent (S.subgroupOf C) := ⟨hSCq, hSCn.isSubnormal⟩
  rcases LocalCores.distinct_components_commute hB.2 hSCc with hEq | hbot
  · have h1 : B ⊓ C = S ⊓ C := (Subgroup.subgroupOf_inj).1 hEq
    rw [inf_eq_left.2 hB.1, inf_eq_left.2 hSC] at h1
    exact h1
  · exfalso
    have hperf : ⁅B.subgroupOf C, B.subgroupOf C⁆ = B.subgroupOf C :=
      Subgroup.isPerfect_iff.1 hB.2.1.1
    have hle : B.subgroupOf C ≤ S.subgroupOf C := by
      rw [← hperf, Subgroup.commutator_le]
      intro x _ z _
      rw [Subgroup.mem_subgroupOf]
      exact hcomm x x.2 z z.2
    have hbot' : ⁅B.subgroupOf C, B.subgroupOf C⁆ = ⊥ :=
      le_bot_iff.1 (hbot ▸ Subgroup.commutator_mono le_rfl hle)
    rw [hperf] at hbot'
    obtain ⟨-, -, a, b, hab⟩ := hB.2.1
    have hsub : Subsingleton ↥(B.subgroupOf C) := by
      rw [hbot']
      infer_instance
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (by rw [Subsingleton.elim a' b'])

theorem mem_of_isCompIn_of_normal_quasisimple {X : Type} [Group X] [Finite X] {y : X}
    {S B : Subgroup X} (hS : IsQuasisimple ↥S) (hyS : y ∈ S)
    (hSC : S ≤ Subgroup.centralizer ({y} : Set X))
    (hSn : ∀ x ∈ Subgroup.centralizer ({y} : Set X), ∀ s ∈ S, x * s * x⁻¹ ∈ S)
    (hcomm : ∀ x ∈ Subgroup.centralizer ({y} : Set X), ∀ z ∈ Subgroup.centralizer ({y} : Set X),
      ⁅x, z⁆ ∈ S)
    (hB : IsCompIn (Subgroup.centralizer ({y} : Set X)) B) : y ∈ B := by
  rw [eq_of_isCompIn_of_normal_quasisimple hS hSC hSn hcomm hB]
  exact hyS

end CFSG.GH74.GLS.IVK.GHInv
