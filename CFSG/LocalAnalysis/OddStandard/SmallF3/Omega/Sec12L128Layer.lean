module

public import CFSG.GroupTheory.LocalCores.Layer
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec128_layer_le {Y : Type*} [Group Y] (Z : Subgroup Y) [Z.Normal]
    (hsol : Group.IsSolvable (Y ⧸ Z)) : CFSG.layer Y ≤ Z := by
  refine sSup_le fun K hK => ?_
  have : Group.IsPerfect ↥K := hK.1.1
  let f : ↥K →* Y ⧸ Z := (QuotientGroup.mk' Z).comp K.subtype
  have : Group.IsPerfect ↥f.range := Group.IsPerfect.range f
  have := hsol
  intro x hx
  by_contra hxZ
  have hnt : Nontrivial ↥f.range := by
    refine ⟨⟨⟨f ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩, 1, fun h => hxZ ?_⟩⟩
    have h1 : f ⟨x, hx⟩ = 1 := congrArg Subtype.val h
    exact (QuotientGroup.eq_one_iff x).mp h1
  exact Group.IsPerfect.not_isSolvable ↥f.range inferInstance

theorem sec128_layer_map_le {Y : Type*} [Group Y] (Z : Subgroup Y) (hZ : Z.IsSubnormal) :
    (CFSG.layer ↥Z).map Z.subtype ≤ CFSG.layer Y := by
  refine Subgroup.map_le_iff_le_comap.mpr (sSup_le fun K hK => ?_)
  refine Subgroup.map_le_iff_le_comap.mp (CFSG.LocalCores.component_le_layer ⟨?_, hK.2.trans' hZ⟩)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (K.equivMapOfInjective Z.subtype Z.subtype_injective) hK.1

theorem sec128_A5_noncomm : ∃ a b : ↥(alternatingGroup (Fin 5)), a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hc : IsMulCommutative ↥(alternatingGroup (Fin 5)) := ⟨⟨fun a b => h a b⟩⟩
  rw [alternatingGroup.isMulCommutative_iff_card_le_three] at hc
  simp at hc

theorem sec128_layer_top
    (Z : Type*) [Group Z] (e : Z ≃* (↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)))) :
    CFSG.layer Z = ⊤ := by
  let eP : (∀ _ : Fin 2, ↥(alternatingGroup (Fin 5))) ≃*
      (↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5))) :=
    { piFinTwoEquiv (fun _ => ↥(alternatingGroup (Fin 5))) with map_mul' := fun _ _ => rfl }
  exact CFSG.LocalCores.layer_eq_top_of_mulEquiv_pi (ι := Fin 2)
    (S := fun _ => ↥(alternatingGroup (Fin 5))) (fun _ => sec128_A5_noncomm) (e.trans eP.symm)

theorem sec128_layer_eq {Y : Type} [Group Y] [Finite Y] (Z : Subgroup Y) [Z.Normal]
    (hZ : Nonempty (↥Z ≃* (↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)))))
    (hsol : Group.IsSolvable (Y ⧸ Z)) : CFSG.layer Y = Z := by
  obtain ⟨e⟩ := hZ
  refine le_antisymm (sec128_layer_le Z hsol) ?_
  have h := sec128_layer_map_le Z (Subgroup.Normal.isSubnormal inferInstance)
  rwa [sec128_layer_top ↥Z e, Subgroup.map_top, Subgroup.range_subtype] at h

end CFSG.OddStandard.SmallF3.Omega
