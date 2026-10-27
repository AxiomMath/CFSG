module

public import CFSG.LocalAnalysis.ComponentInitial.DiagonalComponent
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

theorem central_extension_simple_socle_component_quotients {C : Type*} [Group C] [Finite C]
    {Z : Subgroup C} [Z.Normal] (hZ : Z ≤ center C) {A : Subgroup (C ⧸ Z)} (hAn : A.Normal)
    (hAs : IsSimpleGroup A) (hAab : ∃ a b : A, a * b ≠ b * a)
    (hcen : centralizer (A : Set (C ⧸ Z)) = ⊥) {B : Subgroup C} (hB : CFSG.IsComponent B) :
    B.map (QuotientGroup.mk' Z) = A ∧ Nonempty (B ⧸ center B ≃* A) := by
  obtain ⟨hAq, hAZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hAab
  have hBq := assembly_isQuasisimple_of_isComponent hB
  have hBZ : ¬ B ≤ Z := fun h => not_le_centralizer_self_of_isQuasisimple hBq fun x hx =>
    mem_centralizer_iff.2 fun y _ => mem_center_iff.1 (hZ (h hx)) y
  have hπB := component_quotient_image hB hBZ
  have hAcomp : CFSG.IsComponent A := ⟨hAq, hAn.isSubnormal⟩
  have hπBA : B.map (QuotientGroup.mk' Z) = A := by
    rcases CFSG.LocalCores.distinct_components_commute hπB hAcomp with h | h
    · exact h
    · exfalso
      have hle := commutator_eq_bot_iff_le_centralizer.1 h
      rw [hcen, le_bot_iff] at hle
      refine not_le_centralizer_self_of_isQuasisimple
        (assembly_isQuasisimple_of_isComponent hπB) ?_
      rw [hle]
      exact bot_le
  refine ⟨hπBA, ?_⟩
  set f : B →* C ⧸ Z := (QuotientGroup.mk' Z).comp B.subtype with hf
  have hrange : f.range = A := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype, hπBA]
  have hker : f.ker = center B := by
    apply le_antisymm
    · intro x hx
      have hxZ : (x : C) ∈ Z := by
        rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, Subgroup.coe_subtype,
          QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
        exact hx
      exact mem_center_iff.2 fun y => Subtype.ext (mem_center_iff.1 (hZ hxZ) y)
    · intro x hx
      have hfx : f x ∈ A := hrange ▸ ⟨x, rfl⟩
      have hc : (⟨f x, hfx⟩ : A) ∈ center A := by
        refine mem_center_iff.2 fun a => Subtype.ext ?_
        obtain ⟨y, hy⟩ : (a : C ⧸ Z) ∈ f.range := hrange ▸ a.2
        change (a : C ⧸ Z) * f x = f x * a
        rw [← hy, ← map_mul, ← map_mul, (mem_center_iff.1 hx y)]
      rw [hAZ, mem_bot] at hc
      exact MonoidHom.mem_ker.2 (congrArg Subtype.val hc)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange))⟩

end CFSG.LocalAnalysis.ComponentInitial
