module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Mathlib.GroupTheory.SubgroupSupCommute
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG

open Subgroup

variable {W : Type*} [Group W] [Finite W]

theorem disjoint_sup_centralizer_of_two_components {A B : Subgroup W} (hA : IsComponent A)
    (hB : IsComponent B) (hne : A ≠ B) (hZA : Subgroup.center A = ⊥)
    (hZB : Subgroup.center B = ⊥) :
    (A ⊔ B) ⊓ Subgroup.centralizer ((A ⊔ B : Subgroup W) : Set W) = ⊥ := by
  have hABcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b := by
    have hcomm : ⁅A, B⁆ = ⊥ := by
      rcases LocalCores.distinct_components_commute hA hB with h | h
      · exact absurd h hne
      · exact h
    have hle : A ≤ Subgroup.centralizer (B : Set W) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (hle ha) b hb).symm
  rw [eq_bot_iff]
  intro x hx
  rcases hx with ⟨hxD, hxcent⟩
  obtain ⟨a, ha, b, hb, hxab⟩ :=
    (Subgroup.mem_sup_iff_of_forall_commute
      (fun a ha b hb => (hABcomm a ha b hb).eq) (z := x)).mp hxD
  subst hxab
  have ha_center : (⟨a, ha⟩ : A) ∈ Subgroup.center A := by
    rw [Subgroup.mem_center_iff]
    intro a'
    apply Subtype.ext
    have hxcomm : (a' : W) * (a * b) = (a * b) * (a' : W) :=
      Subgroup.mem_centralizer_iff.mp hxcent (a' : W) (Subgroup.mem_sup_left a'.2)
    have hbcomm : (a' : W) * b = b * (a' : W) := (hABcomm (a' : W) a'.2 b hb).eq
    exact mul_right_cancel (by
      calc
        ((a' : W) * a) * b = (a' : W) * (a * b) := by group
        _ = (a * b) * (a' : W) := hxcomm
        _ = a * (b * (a' : W)) := by group
        _ = a * ((a' : W) * b) := by rw [hbcomm]
        _ = (a * (a' : W)) * b := by group)
  have hb_center : (⟨b, hb⟩ : B) ∈ Subgroup.center B := by
    rw [Subgroup.mem_center_iff]
    intro b'
    apply Subtype.ext
    have hxcomm : (b' : W) * (a * b) = (a * b) * (b' : W) :=
      Subgroup.mem_centralizer_iff.mp hxcent (b' : W) (Subgroup.mem_sup_right b'.2)
    have hab : (b' : W) * a = a * (b' : W) := (hABcomm a ha (b' : W) b'.2).eq.symm
    exact mul_left_cancel (by
      calc
        a * ((b' : W) * b) = (a * (b' : W)) * b := by group
        _ = ((b' : W) * a) * b := by rw [hab]
        _ = (b' : W) * (a * b) := by group
        _ = (a * b) * (b' : W) := hxcomm
        _ = a * (b * (b' : W)) := by group)
  have haone : a = 1 := by
    have hmem : (⟨a, ha⟩ : A) ∈ (⊥ : Subgroup A) := hZA ▸ ha_center
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
  have hbone : b = 1 := by
    have hmem : (⟨b, hb⟩ : B) ∈ (⊥ : Subgroup B) := hZB ▸ hb_center
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
  exact Subgroup.mem_bot.mpr (by rw [haone, hbone, mul_one])

theorem layer_eq_sup_of_two_components {A B D X : Subgroup W} (hA : IsComponent A)
    (hB : IsComponent B) (hD : D = A ⊔ B) (hDn : D.Normal)
    (hX : X = Subgroup.centralizer (D : Set W)) :
    layer W = A ⊔ B ⊔ (layer X).map X.subtype := by
  subst D
  subst X
  have : (A ⊔ B).Normal := hDn
  have hAle : A ≤ layer W := by
    rw [layer.eq_sSup]
    exact le_sSup hA
  have hBle : B ≤ layer W := by
    rw [layer.eq_sSup]
    exact le_sSup hB
  refine le_antisymm ?_ (sup_le (sup_le hAle hBle) ?_)
  · rw [layer.eq_sSup]
    refine sSup_le ?_
    intro C hC
    by_cases hCA : C = A
    · subst hCA
      exact le_sup_of_le_left le_sup_left
    by_cases hCB : C = B
    · subst hCB
      exact le_sup_of_le_left le_sup_right
    · have hCcentA : C ≤ Subgroup.centralizer (A : Set W) := by
        rcases LocalCores.distinct_components_commute hC hA with h | h
        · exact absurd h hCA
        · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      have hCcentB : C ≤ Subgroup.centralizer (B : Set W) := by
        rcases LocalCores.distinct_components_commute hC hB with h | h
        · exact absurd h hCB
        · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      have hCX : C ≤ Subgroup.centralizer ((A ⊔ B : Subgroup W) : Set W) := by
        rw [Subgroup.le_centralizer_iff]
        exact sup_le ((Subgroup.le_centralizer_iff).mp hCcentA)
          ((Subgroup.le_centralizer_iff).mp hCcentB)
      let X : Subgroup W := Subgroup.centralizer ((A ⊔ B : Subgroup W) : Set W)
      have hCX' : C ≤ X := hCX
      have hcomp : IsComponent (C.subgroupOf X) := LocalCores.component_overgroup hC hCX'
      have hCeq : (C.subgroupOf X).map X.subtype = C :=
        Subgroup.map_subgroupOf_eq_of_le hCX'
      rw [← hCeq]
      exact (Subgroup.map_mono (le_sSup hcomp)).trans le_sup_right
  ·
    let X : Subgroup W := Subgroup.centralizer ((A ⊔ B : Subgroup W) : Set W)
    have hEX : (layer X).map X.subtype ≤ layer W := by
      rw [layer.eq_sSup, layer.eq_sSup]
      rw [Subgroup.map_le_iff_le_comap]
      refine sSup_le ?_
      intro C hC
      rw [← Subgroup.map_le_iff_le_comap]
      refine le_sSup ?_
      refine ⟨LocalCores.isQuasisimple_of_mulEquiv
        (Subgroup.equivMapOfInjective C X.subtype X.subtype_injective) hC.1, ?_⟩
      exact hC.2.trans' (by dsimp [X]; infer_instance : X.Normal).isSubnormal
    exact hEX

theorem fittingSubgroup_eq_map_of_two_components {A B D X : Subgroup W} (hA : IsComponent A)
    (hB : IsComponent B) (hD : D = A ⊔ B) (hDn : D.Normal)
    (hX : X = Subgroup.centralizer (D : Set W)) :
    fittingSubgroup W = (fittingSubgroup X).map X.subtype := by
  subst D
  subst X
  have : (A ⊔ B).Normal := hDn
  let X : Subgroup W := Subgroup.centralizer ((A ⊔ B : Subgroup W) : Set W)
  have hFWX : fittingSubgroup W ≤ X := by
    have hDleLayer : (A ⊔ B : Subgroup W) ≤ layer W := by
      rw [layer.eq_sSup]
      exact sup_le (le_sSup hA) (le_sSup hB)
    have hFcent : fittingSubgroup W ≤ Subgroup.centralizer (layer W : Set W) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (LocalCores.fitting_layer_commute (G := W))
    exact hFcent.trans (Subgroup.centralizer_le (fun x hx => hDleLayer hx))
  have hFXle : (fittingSubgroup X).map X.subtype ≤ fittingSubgroup W := by
    refine le_sSup ?_
    have hnormal : ((fittingSubgroup X).map X.subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal
    have hnil : Group.IsNilpotent ((fittingSubgroup X).map X.subtype) :=
      Group.nilpotent_of_mulEquiv
        (Subgroup.equivMapOfInjective (fittingSubgroup X) X.subtype X.subtype_injective)
    exact ⟨hnormal, hnil⟩
  refine le_antisymm ?_ hFXle
  intro w hw
  have hwX : w ∈ X := hFWX hw
  have hNnormal : ((fittingSubgroup W).subgroupOf X).Normal :=
    (inferInstance : (fittingSubgroup W).Normal).subgroupOf X
  have hNnil : Group.IsNilpotent ((fittingSubgroup W).subgroupOf X) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hFWX).symm
  have hNle : (fittingSubgroup W).subgroupOf X ≤ fittingSubgroup X :=
    (LocalCores.fitting_characteristic (G := X)).2.2 _ hNnormal hNnil
  exact Subgroup.mem_map_of_mem X.subtype
    (hNle (show (⟨w, hwX⟩ : X) ∈ (fittingSubgroup W).subgroupOf X from hw))

theorem generalizedFitting_eq_sup_of_two_components {A B D X : Subgroup W}
    (hA : IsComponent A) (hB : IsComponent B) (hD : D = A ⊔ B) (hDn : D.Normal)
    (hX : X = Subgroup.centralizer (D : Set W)) :
    generalizedFitting W = A ⊔ B ⊔ (generalizedFitting X).map X.subtype := by
  have hL := layer_eq_sup_of_two_components hA hB hD hDn hX
  have hF := fittingSubgroup_eq_map_of_two_components hA hB hD hDn hX
  rw [generalizedFitting.eq_sup, generalizedFitting.eq_sup, hL, hF, Subgroup.map_sup]
  ac_rfl

end CFSG
