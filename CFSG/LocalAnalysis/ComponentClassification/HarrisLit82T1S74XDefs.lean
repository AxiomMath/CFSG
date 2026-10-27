module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74FDefs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.LieType.Universal.Spin

structure SylowFacts (K : Type) [Field K] (i : spinGroup (quadOdd 3 K))
    (S₀ B : Subgroup (spinGroup (quadOdd 3 K))) : Prop where
  isPGroup : IsPGroup 2 S₀
  le_centralizer : S₀ ≤ centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K)))
  not_dvd : ¬ 2 ∣ S₀.relIndex (centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))))
  B_le : B ≤ S₀
  relIndex_B : B.relIndex S₀ = 2
  i_mem : i ∈ S₀
  t_mem : tSeven K ∈ B
  z_mem : spinZ K ∈ B
  commute_t : ∀ x ∈ B, tSeven K * x = x * tSeven K
  center : ∀ x ∈ S₀, (∀ y ∈ S₀, x * y = y * x) → x = 1 ∨ x = spinZ K
  involutions_B : ∀ x ∈ B, x * x = 1 →
    x = 1 ∨ x = spinZ K ∨ x = tSeven K ∨ x = spinZ K * tSeven K
  sqrt : ({x | x ∈ B ∧ x * x = spinZ K} : Set (spinGroup (quadOdd 3 K))).ncard ≠
    ({x | x ∈ B ∧ x * x = spinZ K * tSeven K} : Set (spinGroup (quadOdd 3 K))).ncard
  conj_i : ∀ w ∈ S₀, w ∉ B → w * w = 1 → ∃ s ∈ S₀, s * i * s⁻¹ = w
  commutator_le : ⁅S₀, S₀⁆ ≤ B
  derived_i : ∃ D : Subgroup (spinGroup (quadOdd 3 K)),
    D ≤ S₀ ⊓ centralizer ({i} : Set (spinGroup (quadOdd 3 K))) ∧ spinZ K ∈ ⁅D, D⁆
  card_i : Nat.card ↥(S₀ ⊓ centralizer ({i} : Set (spinGroup (quadOdd 3 K)))) ≠ Nat.card B

structure IBarFacts (K : Type) [Field K] [Finite K] (p : ℕ) (i : spinGroup (quadOdd 3 K)) :
    Prop where
  mul_self : i * i = 1
  commute_J₁ : ∀ j ∈ spinJ₁ K, i * j = j * i
  conj_t : i * tSeven K * i⁻¹ = spinZ K * tSeven K
  card_M : 2 * Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) ≤
    Nat.card ↥(centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))) ⊓
      normalizer (fourT K : Set (spinGroup (quadOdd 3 K))) ⊓
        centralizer ({i} : Set (spinGroup (quadOdd 3 K))))
  conj_M : ∀ w ∈ centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))) ⊓
      normalizer (fourT K : Set (spinGroup (quadOdd 3 K))), w * w = 1 →
    w * tSeven K ≠ tSeven K * w → ∃ m ∈ centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))) ⊓
      normalizer (fourT K : Set (spinGroup (quadOdd 3 K))), m * i * m⁻¹ = w
  shape : ∀ l : spinGroup (quadOdd 3 K), l * tSeven K * l⁻¹ = i →
    ∃ a ∈ spinJ₂ K, ∃ b ∈ spinJ₃ K, a ≠ 1 ∧ b ≠ 1 ∧ a ^ p = 1 ∧ b ^ p = 1 ∧
      l⁻¹ * qThree K * l = a * b
  sylow : ∃ S₀ B : Subgroup (spinGroup (quadOdd 3 K)), SylowFacts K i S₀ B

structure SpinFacts (K : Type) [Field K] [Finite K] (p : ℕ) : Prop where
  qThree_pow : qThree K ^ p = 1
  qThree_ne_one : qThree K ≠ 1
  card_centralizer_tSeven_qThree :
    Nat.card ↥(centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) ⊓
      centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K)))) ≤
      Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) ^ 2
  conj_qOne : ∀ y : spinGroup (quadOdd 3 K), (y ∈ spinJ₂ K ∨ y ∈ spinJ₃ K) → y ≠ 1 →
    y ^ p = 1 → ∃ g : spinGroup (quadOdd 3 K), g * y * g⁻¹ = qOne K
  conj_qThree : ∀ y ∈ spinJ₁ K, y ≠ 1 → y ^ p = 1 →
    ∃ g ∈ centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))), g * y * g⁻¹ = qThree K
  card_centralizer_mul : ∀ a ∈ spinJ₁ K, ∀ b : spinGroup (quadOdd 3 K),
    (b ∈ spinJ₂ K ∨ b ∈ spinJ₃ K) → a ≠ 1 → b ≠ 1 → a ^ p = 1 → b ^ p = 1 →
    Nat.card ↥(centralizer ({a * b} : Set (spinGroup (quadOdd 3 K)))) ≤
      4 * Nat.card K ^ 7 * (Nat.card K ^ 2 - 1)
  iBar : ∃ i : spinGroup (quadOdd 3 K), IBarFacts K p i

@[expose] def SpinFactsAll : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → Nat.card K = p ^ f →
    5 ≤ p ^ f → SpinFacts K p

end CFSG.ComponentClassification.HarrisLit.T1.S74
