module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRankOneLeviMinusComm
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRankOneLeviSL2

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open CFSG.LocalAnalysis.UniquenessCase.UC22

open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

private lemma commHyp_H19 {r : ℕ} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hr : 2 ≤ r) :
    ∀ b₁ ∈ tailBorel r (minusTailForm K b c), ∀ b₂ ∈ tailBorel r (minusTailForm K b c),
      ⁅b₁, b₂⁆ ∈ tailUnipotent r (minusTailForm K b c) :=
  fun _ h₁ _ h₂ => commutator_mem_tailUnipotent_minus hr hirr h₁ h₂

theorem tailRankOneSL2Surjection_minus (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {r : ℕ}
    {i : Fin r} (hi : i.val + 1 < r) {a₀ : Fin 2 → K} (ha₀ : a₀ ≠ 0) {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) :
    TailRankOneSL2Surjection (qA := minusTailForm K b c) (anisotropic_minusTailForm hirr) ha₀
      i :=
  tailRankOneSL2Surjection_holds hi (anisotropic_minusTailForm hirr) ha₀
    (commHyp_H19 hirr (by omega)) hn hK

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
