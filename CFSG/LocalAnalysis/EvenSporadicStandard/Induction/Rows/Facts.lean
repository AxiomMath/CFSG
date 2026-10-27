module

public import CFSG.Foundations.SteinbergCADefinitionNodes
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterFusion
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

theorem isQuasisimple_of_perfect_simple_quotient {C Y : Type*} [Group C] [Group Y]
    (hp : Group.IsPerfect C) (e : C ⧸ center C ≃* Y) (hs : IsSimpleGroup Y) :
    CFSG.IsQuasisimple C := by
  have hs' : IsSimpleGroup (C ⧸ center C) := @MulEquiv.isSimpleGroup _ _ _ _ hs e
  have hq : Group.IsPerfect (C ⧸ center C) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center C)) QuotientGroup.mk_surjective
  have hnab : ∃ a b : C ⧸ center C, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have h1 : _root_.commutator (C ⧸ center C) = ⊥ := by
      rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      exact mem_centralizer_iff.2 fun y _ => hcon y x
    have h2 : _root_.commutator (C ⧸ center C) = ⊤ := hq.commutator_eq_top
    have hnt : Nontrivial (C ⧸ center C) := hs'.toNontrivial
    obtain ⟨x, hx⟩ := exists_ne (1 : C ⧸ center C)
    have hxt : x ∈ (⊤ : Subgroup (C ⧸ center C)) := Subgroup.mem_top x
    rw [← h2, h1, Subgroup.mem_bot] at hxt
    exact hx hxt
  exact (CFSG.Foundations.SteinbergCA.quasisimple_iff C).1.2 ⟨hp, hs', hnab⟩

theorem fixSubgroup_conj {Y : Type} [Group Y] (g : Y) :
    fixSubgroup (MulAut.conj g) = centralizer ({g} : Set Y) := by
  ext y
  rw [mem_centralizer_singleton_iff]
  show MulAut.conj g y = y ↔ y * g = g * y
  rw [MulAut.conj_apply]
  constructor
  · intro h
    calc y * g = (g * y * g⁻¹) * g := by rw [h]
      _ = g * y := by group
  · intro h
    calc g * y * g⁻¹ = (y * g) * g⁻¹ := by rw [h]
      _ = y := by group

end CFSG.EvenSporadicStandard.Induction
