module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.BinaryScalarInvariance

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

theorem biadditive_eq_zero_of_smul_invariant {F V A : Type*} [Field F] [Finite F] [CharP F 2]
    [AddCommGroup V] [Module F V] [AddCommGroup A] (hcard : 4 < Nat.card F)
    (β : V → V → A) (hleft : ∀ v v' w, β (v + v') w = β v w + β v' w)
    (hright : ∀ v w w', β v (w + w') = β v w + β v w')
    (hinv : ∀ c : F, c ≠ 0 → ∀ v w, β (c • v) (c • w) = β v w) (v w : V) : β v w = 0 := by
  have h := ShultStronglyClosedTI.binaryScalarInvariantBiadditive_eq_zero hcard
    (fun x y : F => β (x • v) (y • w))
    (fun x x' y => by simp only [add_smul, hleft])
    (fun x y y' => by simp only [add_smul, hright])
    (fun c hc x y => by simp only [mul_smul, hinv c hc]) 1 1
  simpa only [one_smul] using h

end CFSG.ProperTwoGeneratedCore.TheoremC
