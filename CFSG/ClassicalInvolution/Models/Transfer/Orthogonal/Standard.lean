module

public import CFSG.ClassicalInvolution.Models.Transfer.Orthogonal.Center
public import CFSG.ClassicalGroups.Orthogonal.Simple

public section

namespace CFSG.ClassicalInvolution.Models.Transfer

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

variable {K : Type} [Field K] {n : ℕ}

theorem centerScalar_quadOdd (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) : CenterScalar (quadOdd n K) := by
  obtain ⟨hQ, T, hT, hTQ⟩ := regular_quadOdd (K := K) h2 hn
  exact centerScalar_of_totallySingular hQ hT.ge hTQ

theorem four_lt_finrank_quadOdd (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    4 < Module.finrank K (Fin n ⊕ Fin n ⊕ Unit → K) := by
  obtain ⟨hQ, T, hT, hTQ⟩ := regular_quadOdd (K := K) h2 hn
  exact four_lt_finrank_of_totallySingular hQ hT.ge hTQ

theorem centerScalar_quadPlus (hn : 3 ≤ n) : CenterScalar (quadPlus n K) := by
  obtain ⟨hQ, T, hT, hTQ⟩ := regular_quadPlus (K := K) hn
  exact centerScalar_of_totallySingular hQ hT.ge hTQ

theorem four_lt_finrank_quadPlus (hn : 3 ≤ n) :
    4 < Module.finrank K (Fin n ⊕ Fin n → K) := by
  obtain ⟨hQ, T, hT, hTQ⟩ := regular_quadPlus (K := K) hn
  exact four_lt_finrank_of_totallySingular hQ hT.ge hTQ

theorem centerScalar_quadMinus [Finite K] {b c : K} (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : CenterScalar (quadMinus n K b c) := by
  obtain ⟨hQ, T, hT, hTQ⟩ := regular_quadMinus hn hirr
  exact centerScalar_of_totallySingular hQ hT.ge hTQ

theorem four_lt_finrank_quadMinus [Finite K] {b c : K} (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    4 < Module.finrank K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) := by
  obtain ⟨hQ, T, hT, hTQ⟩ := regular_quadMinus hn hirr
  exact four_lt_finrank_of_totallySingular hQ hT.ge hTQ

end CFSG.ClassicalInvolution.Models.Transfer
