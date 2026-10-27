module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74FDefs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.LieType.Universal.Spin

@[expose] def A1 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Odd (Nat.card K) →
    ∃ i : spinGroup (quadOdd 3 K), i * i = 1 ∧ (∀ j ∈ spinJ₁ K, i * j = j * i) ∧
      i * tSeven K * i⁻¹ = spinZ K * tSeven K

@[expose] def A2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Odd (Nat.card K) →
    centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) ⊓
      centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))) ≤ spinE K

@[expose] def A3 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Odd (Nat.card K) →
    (∀ y ∈ spinJ₁ K, y ≠ 1 → y ^ ringChar K = 1 →
      ∃ g ∈ centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))), g * y * g⁻¹ = qThree K) ∧
    (∀ y : spinGroup (quadOdd 3 K), (y ∈ spinJ₂ K ∨ y ∈ spinJ₃ K) → y ≠ 1 →
      y ^ ringChar K = 1 → ∃ g : spinGroup (quadOdd 3 K), g * y * g⁻¹ = qOne K) ∧
    (∀ y ∈ spinJ₁ K, y ≠ 1 → y ^ ringChar K = 1 →
      ∃ g ∈ spinJ₁ K, ∃ c : K, c ≠ 0 ∧ g * y * g⁻¹ = shortSeven K (upperSL2 c)) ∧
    (∀ y ∈ spinJ₂ K, y ≠ 1 → y ^ ringChar K = 1 →
      ∃ g ∈ spinJ₂ K, ∃ c : K, c ≠ 0 ∧
        g * y * g⁻¹ = (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true true (upperSL2 c))

@[expose] def A4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Odd (Nat.card K) →
    (∀ x ∈ spinJ₂ K, x * x = 1 → x = 1 ∨ x = tSeven K) ∧
    ∀ P : Subgroup (spinGroup (quadOdd 3 K)), P ≤ spinJ₂ K → IsPGroup 2 P →
      ¬ 2 ∣ P.relIndex (spinJ₂ K) →
      (∃ a ∈ P, ∃ b ∈ P, a * a = tSeven K ∧ b * b = tSeven K ∧ a * b ≠ b * a) ∧
      ∀ x ∈ spinJ₂ K, (∀ y ∈ P, x * y = y * x) → x = 1 ∨ x = tSeven K

end CFSG.ComponentClassification.HarrisLit.T1.S74
