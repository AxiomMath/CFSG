module

public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Shape

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup

theorem conj_injective_of_simple {A : Type*} [Group A] [IsSimpleGroup A]
    (hnab : ∃ a b : A, a * b ≠ b * a) : Function.Injective (MulAut.conj : A →* MulAut A) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  rw [MonoidHom.mem_ker] at ha
  rw [mem_bot]
  refine CFSG.EvenSporadicStandard.SolomonRed.eq_one_of_central_of_simple hnab fun b => ?_
  have h1 := congrArg (fun σ : MulAut A => σ b) ha
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc b * a = (a * b * a⁻¹) * a := by rw [h1]
    _ = a * b := by group

theorem nonempty_mulEquiv_range_conj {A : Type*} [Group A] [IsSimpleGroup A]
    (hnab : ∃ a b : A, a * b ≠ b * a) :
    Nonempty (↥(MulAut.conj : A →* MulAut A).range ≃* A) :=
  ⟨(MonoidHom.ofInjective (conj_injective_of_simple hnab)).symm⟩

end CFSG.EvenSporadicStandard.HSStd.InvCent
