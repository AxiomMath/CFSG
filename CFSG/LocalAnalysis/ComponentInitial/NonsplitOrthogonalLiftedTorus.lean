module

public import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalTorusMaps
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.CentralExt.QuaternionCover
public import CFSG.LocalAnalysis.SectionRank.EvenCover.SLTwo

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.NormTail

open QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal OrthogonalTail CFSG.LieType.CentralExt
  CFSG.SectionRank.EvenCover

section Lifts

variable {K F : Type} [Field K] [Field F] [Algebra K F] (T : NormTailData K F) {r : ℕ}

variable (F) in
@[expose] def diagHom : Fˣ →* SpecialLinearGroup (Fin 2) F where
  toFun := diagSL F
  map_one' := Matrix.SpecialLinearGroup.ext _ _ fun a b => by
    fin_cases a <;> fin_cases b <;> simp [coe_diagSL]
  map_mul' s t := Matrix.SpecialLinearGroup.ext _ _ fun a b => by
    change (diagSL F (s * t) : Matrix (Fin 2) (Fin 2) F) a b =
      ((diagSL F s : Matrix (Fin 2) (Fin 2) F) * (diagSL F t : Matrix (Fin 2) (Fin 2) F)) a b
    rw [coe_diagSL, coe_diagSL, coe_diagSL, Matrix.mul_fin_two]
    fin_cases a <;> fin_cases b <;> simp [mul_comm]

theorem diagHom_apply (s : Fˣ) : diagHom F s = diagSL F s :=
  rfl

theorem torusMap_commute (a a' : Fin r → Kˣ) (c c' : Fˣ) :
    Commute (torusMap F a c) (torusMap F a' c') := by
  rw [← torusHom_apply (a, c), ← torusHom_apply (a', c')]
  exact (Commute.all _ _).map _

variable [CharP K 2] {E : Type*} [Group E] (π : E →* G0 T r)

variable [Finite K] [Finite E] {T π}

end Lifts

end CFSG.LocalAnalysis.ComponentInitial.NormTail
