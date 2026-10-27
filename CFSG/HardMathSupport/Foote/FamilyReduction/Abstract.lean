module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public section

namespace CFSG.HardMathSupport.Foote.FamilyReduction

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def Comp5 (Q : Type) [Group Q] : Prop :=
  ∃ α : MulAut Q, orderOf α = 2 ∧ ∃ K : Subgroup (fixedSubgroup α),
    IsComponent K ∧ Nonempty (K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))

@[expose] def CompIn5 (Q : Type) [Group Q] : Prop :=
  ∃ (α : MulAut Q) (w : Q), α = MulAut.conj w ∧ orderOf α = 2 ∧
    ∃ K : Subgroup (fixedSubgroup α), IsComponent K ∧
      Nonempty (K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∧
        ∃ hw : w ∈ fixedSubgroup α, (⟨w, hw⟩ : fixedSubgroup α) ∈ K

theorem CompIn5.toComp5 {Q : Type} [Group Q] (h : CompIn5 Q) : Comp5 Q := by
  obtain ⟨α, w, -, hα, K, hK, hKe, -⟩ := h
  exact ⟨α, hα, K, hK, hKe⟩

theorem mem_fixedSubgroup_iff {G : Type*} [Group G] (α : MulAut G) (x : G) :
    x ∈ fixedSubgroup α ↔ α x = x := Iff.rfl

end CFSG.HardMathSupport.Foote.FamilyReduction
