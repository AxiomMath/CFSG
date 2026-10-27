module

import CFSG.GroupTheory.Fitting.SelfCentralizingComponent
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.ComponentClassification.SmallLocal

open Subgroup CFSG.LocalCores

variable {S : Type*} [Group S]

theorem mulAut_mul_conj_mul_inv (β : MulAut S) (s : S) :
    β * MulAut.conj s * β⁻¹ = MulAut.conj (β s) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem mulAut_conj_injective (hZ : center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  refine (MonoidHom.ker_eq_bot_iff _).mp (eq_bot_iff.mpr fun s hs => ?_)
  have hsZ : s ∈ center S := mem_center_iff.mpr fun x => by
    have h := congrArg (fun f : MulAut S => f x) (MonoidHom.mem_ker.mp hs)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc x * s = s * x * s⁻¹ * s := by rw [h]
      _ = s * x := by group
  rwa [hZ] at hsZ

theorem mulAut_conj_range_normal : (MulAut.conj : S →* MulAut S).range.Normal :=
  ⟨fun _ ⟨s, hs⟩ β => ⟨β s, by rw [← hs, mulAut_mul_conj_mul_inv]⟩⟩

theorem almost_simple_inner_generalized_fitting [Finite S] [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) (B : Subgroup (MulAut S))
    (hB : (MulAut.conj : S →* MulAut S).range ≤ B) :
    centralizer (((MulAut.conj : S →* MulAut S).range.subgroupOf B : Subgroup B) : Set B) = ⊥ ∧
      fittingSubgroup B = ⊥ ∧ layer B = (MulAut.conj : S →* MulAut S).range.subgroupOf B ∧
      generalizedFitting B = (MulAut.conj : S →* MulAut S).range.subgroupOf B ∧
      Nonempty ((MulAut.conj : S →* MulAut S).range.subgroupOf B ≃* S) := by
  obtain ⟨hQ, hZ⟩ := isQuasisimple_of_isSimpleGroup hS
  have hinj := mulAut_conj_injective hZ
  have : Finite (MulAut S) :=
    Finite.of_injective (fun f : MulAut S => (f : S → S)) fun f g h => MulEquiv.ext (congrFun h)
  set I := (MulAut.conj : S →* MulAut S).range.subgroupOf B with hI
  let e : I ≃* S := (subgroupOfEquivOfLe hB).trans (MonoidHom.ofInjective hinj).symm
  have hcent : centralizer (I : Set B) = ⊥ := by
    refine eq_bot_iff.mpr fun β hβ => (mem_bot).mpr (Subtype.ext (MulEquiv.ext fun s => ?_))
    have hmem : (⟨MulAut.conj s, hB ⟨s, rfl⟩⟩ : B) ∈ I := mem_subgroupOf.mpr ⟨s, rfl⟩
    have hcomm := congrArg Subtype.val (mem_centralizer_iff.mp hβ _ hmem)
    have h1 : (β : MulAut S) * MulAut.conj s * (β : MulAut S)⁻¹ = MulAut.conj s := by
      change MulAut.conj s * (β : MulAut S) = (β : MulAut S) * MulAut.conj s at hcomm
      rw [← hcomm, mul_inv_cancel_right]
    rw [mulAut_mul_conj_mul_inv] at h1
    exact hinj h1
  have hIn : I.Normal := mulAut_conj_range_normal.subgroupOf B
  have hIc : IsComponent I := ⟨isQuasisimple_of_mulEquiv e.symm hQ, hIn.isSubnormal⟩
  exact ⟨hcent, fittingSubgroup_eq_bot_of_isComponent_of_centralizer_eq_bot I hIc hcent,
    layer_eq_of_isComponent_of_centralizer_eq_bot I hIc hcent,
    generalizedFitting_eq_of_isComponent_of_centralizer_eq_bot I hIc hcent, ⟨e⟩⟩

end CFSG.ComponentClassification.SmallLocal
