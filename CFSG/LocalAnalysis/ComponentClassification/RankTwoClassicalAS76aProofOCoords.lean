module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix CFSG.Assembly.LowTwoRank

@[expose] def plusOe (k : ℕ) : (Fin k ⊕ Fin k) ⊕ (Fin 2 ⊕ Fin 2) ≃ Fin (k + 2) ⊕ Fin (k + 2) where
  toFun
    | .inl (.inl i) => .inl (Fin.castAdd 2 i)
    | .inl (.inr i) => .inr (Fin.castAdd 2 i)
    | .inr (.inl t) => .inl (Fin.natAdd k t)
    | .inr (.inr t) => .inr (Fin.natAdd k t)
  invFun
    | .inl i => Fin.addCases (fun i => .inl (.inl i)) (fun t => .inr (.inl t)) i
    | .inr i => Fin.addCases (fun i => .inl (.inr i)) (fun t => .inr (.inr t)) i
  left_inv := by rintro ((i | i) | (t | t)) <;> simp
  right_inv := by
    rintro (i | i) <;> induction i using Fin.addCases <;> simp

@[expose] def minusOe (j : ℕ) :
    (Fin j ⊕ Fin j ⊕ Fin 2) ⊕ (Fin 2 ⊕ Fin 2) ≃ Fin (j + 2) ⊕ Fin (j + 2) ⊕ Fin 2 where
  toFun
    | .inl (.inl i) => .inl (Fin.castAdd 2 i)
    | .inl (.inr (.inl i)) => .inr (.inl (Fin.castAdd 2 i))
    | .inl (.inr (.inr t)) => .inr (.inr t)
    | .inr (.inl t) => .inl (Fin.natAdd j t)
    | .inr (.inr t) => .inr (.inl (Fin.natAdd j t))
  invFun
    | .inl i => Fin.addCases (fun i => .inl (.inl i)) (fun t => .inr (.inl t)) i
    | .inr (.inl i) => Fin.addCases (fun i => .inl (.inr (.inl i))) (fun t => .inr (.inr t)) i
    | .inr (.inr t) => .inl (.inr (.inr t))
  left_inv := by rintro ((i | i | t) | (t | t)) <;> simp
  right_inv := by
    rintro (i | i | t)
    · induction i using Fin.addCases <;> simp
    · induction i using Fin.addCases <;> simp
    · simp

variable {K : Type} [Field K]

theorem statedQuadPlus_plusOe (k : ℕ) (v : Fin (k + 2) ⊕ Fin (k + 2) → K) :
    StatedQuadPlus (k + 2) K v = StatedQuadPlus k K (fun a => v (plusOe k (.inl a))) +
      StatedQuadPlus 2 K (fun b => v (plusOe k (.inr b))) := by
  simp only [StatedQuadPlus, Fin.sum_univ_add]
  rfl

theorem statedQuadMinus_minusOe (j : ℕ) (b c : K) (v : Fin (j + 2) ⊕ Fin (j + 2) ⊕ Fin 2 → K) :
    StatedQuadMinus (j + 3) K b c v =
      StatedQuadMinus (j + 1) K b c (fun a => v (minusOe j (.inl a))) +
        StatedQuadPlus 2 K (fun b => v (minusOe j (.inr b))) := by
  have h1 : StatedQuadMinus (j + 3) K b c v = (∑ i : Fin (j + 2), v (.inl i) * v (.inr (.inl i))) +
      v (.inr (.inr 0)) ^ 2 + b * v (.inr (.inr 0)) * v (.inr (.inr 1)) +
        c * v (.inr (.inr 1)) ^ 2 := rfl
  have h2 : StatedQuadMinus (j + 1) K b c (fun a => v (minusOe j (.inl a))) =
      (∑ i : Fin j, v (.inl (Fin.castAdd 2 i)) * v (.inr (.inl (Fin.castAdd 2 i)))) +
        v (.inr (.inr 0)) ^ 2 + b * v (.inr (.inr 0)) * v (.inr (.inr 1)) +
          c * v (.inr (.inr 1)) ^ 2 := rfl
  have h3 : StatedQuadPlus 2 K (fun b => v (minusOe j (.inr b))) =
      ∑ t : Fin 2, v (.inl (Fin.natAdd j t)) * v (.inr (.inl (Fin.natAdd j t))) := rfl
  rw [h1, h2, h3, Fin.sum_univ_add]
  ring

end CFSG.ComponentClassification.RankTwoClassical
