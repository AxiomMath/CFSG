module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RankOneAutomorphisms
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.GLTheoremB.Defs
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.P51

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem eq_one_of_isPerfect_of_isSolvable {A M : Type*} [Group A] [Group M]
    [Group.IsPerfect A] [Group.IsSolvable M] (φ : A →* M) : φ = 1 := by
  have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have : Group.IsSolvable φ.range :=
    Group.isSolvable_of_isSolvable_injective (f := φ.range.subtype) φ.range.subtype_injective
  have hsub : Subsingleton φ.range := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isSolvable φ.range ‹_›
  ext h
  have : (⟨φ h, h, rfl⟩ : φ.range) = 1 := Subsingleton.elim _ _
  exact congrArg Subtype.val this

theorem isEmpty_mulEquiv_quaternionGroup {W H : Subgroup G}
    (hHW : H ≤ Subgroup.normalizer (W : Set G)) (hH : (⁅H, H⁆ : Subgroup G) = H)
    (hW : (⁅W, H⁆ : Subgroup G) = W) (hWne : W ≠ ⊥) :
    IsEmpty (W ≃* QuaternionGroup 2) := by
  refine ⟨fun e => ?_⟩
  haveI : Group.IsPerfect H := Subgroup.isPerfect_iff.mpr hH
  haveI : Group.IsSolvable (MulAut (QuaternionGroup 2)) := by
    simpa using CFSG.ProperTwoGeneratedCore.quaternion_power_two_automorphism_solvable 1
  haveI : Group.IsSolvable (MulAut W) :=
    Group.isSolvable_of_isSolvable_injective (f := (MulAut.congr e).toMonoidHom)
      (MulAut.congr e).injective
  have hφ := eq_one_of_isPerfect_of_isSolvable
    ((Subgroup.normalizerMonoidHom (H := W)).comp (Subgroup.inclusion hHW))
  have hcomm : ∀ h ∈ H, ∀ w ∈ W, h * w = w * h := by
    intro h hh w hw
    have h1 : (Subgroup.normalizerMonoidHom (H := W)) ⟨h, hHW hh⟩ = 1 :=
      DFunLike.congr_fun hφ ⟨h, hh⟩
    have h2 := congrArg (fun f : MulAut W => ((f ⟨w, hw⟩ : W) : G)) h1
    have h3 : h * w * h⁻¹ = w := h2
    calc h * w = h * w * h⁻¹ * h := by group
      _ = w * h := by rw [h3]
  have hbot : (⁅W, H⁆ : Subgroup G) = ⊥ := by
    refine le_antisymm (Subgroup.commutator_le.mpr ?_) bot_le
    intro w hw h hh
    rw [Subgroup.mem_bot, commutatorElement_def, ← hcomm h hh w hw]
    group
  exact hWne (hW.symm.trans hbot)

end CFSG.LocalAnalysis.GLTheoremA.P51
