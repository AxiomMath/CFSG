module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailMaxBorel

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

theorem tail_eq_closure_of_borel_le {K : Type*} [Field K] {A : Type*}
    [AddCommGroup A] [Module K A] [FiniteDimensional K A] {r : ℕ} {qA : QuadraticForm K A}
    (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0)
    {M : Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))}
    (hMG : M ≤ orthElementaryGroup (quadTail r qA)) (hBM : tailBorel r qA ≤ M) :
    M = Subgroup.closure ((tailBorel r qA : Set _) ∪
      tailWeylElt r qA a₀ '' {i : Fin r | tailWeylElt r qA a₀ i ∈ M}) :=
  eq_closure_of_tailBorel_le hani ha₀ hMG hBM

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
