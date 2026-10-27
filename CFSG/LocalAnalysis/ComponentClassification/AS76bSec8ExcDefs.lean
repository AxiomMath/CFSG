module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.Foundations.Basic

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.Exc

open Subgroup CFSG.ComponentClassification.AS76b

variable {C : Type*} [Group C]

abbrev cent (x : C) : Subgroup C := centralizer {x}

@[expose] def zx (x : C) : Subgroup C where
  carrier := {w | w ∈ cent x ∧ (∀ c ∈ cent x, w * c = c * w) ∧ w * w = 1}
  mul_mem' := by
    rintro a b ⟨ha, hac, ha2⟩ ⟨hb, hbc, hb2⟩
    refine ⟨mul_mem ha hb, fun c hc => ?_, ?_⟩
    · rw [mul_assoc, hbc c hc, ← mul_assoc, hac c hc, mul_assoc]
    · calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hac b hb]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
  one_mem' := ⟨one_mem _, fun c _ => by rw [one_mul, mul_one], mul_one 1⟩
  inv_mem' := by
    rintro a ⟨ha, hac, ha2⟩
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    rw [hai]
    exact ⟨ha, hac, ha2⟩

structure CentreData (x : C) (Z : Subgroup C) : Prop where
  mem : x ∈ Z
  ne_one : x ≠ 1
  elem : CFSG.Open.IsElemAbelian 2 Z
  le_cent : Z ≤ cent x
  commute : ∀ z ∈ Z, ∀ c ∈ cent x, z * c = c * z
  centre_inv : ∀ w ∈ cent x, (∀ c ∈ cent x, w * c = c * w) → w * w = 1 → w ∈ Z

@[expose] def ResidualMem (x : C) : Prop :=
  x ∈ admResidual (oUpperTwo (cent x) ⊔ ⁅cent x, cent x⁆)

@[expose] def SplitData (x : C) (Z : Subgroup C) : Prop :=
  ∃ D : Subgroup C, ⁅D, D⁆ = D ∧ D ≤ cent x ∧ ∀ c ∈ cent x, ∃ z ∈ Z, z⁻¹ * c ∈ D

@[expose] def CharTwo (x : C) : Prop :=
  CFSG.IsCharacteristicP 2 ↥(cent x)

structure Regular (Z : Subgroup C) (y : C) : Prop where
  y_mem : y ∈ normalizer (Z : Set C)
  odd : Odd (orderOf y)
  trans : ∀ j ∈ Z, j ≠ 1 → ∀ j' ∈ Z, j' ≠ 1 →
    ∃ a ∈ normalizer (Z : Set C), a * j * a⁻¹ = j'
  free : ∀ a ∈ normalizer (Z : Set C), ∀ j ∈ Z, j ≠ 1 → a * j * a⁻¹ = j →
    a ∈ centralizer (Z : Set C)
  cyclic : ∀ a ∈ normalizer (Z : Set C), ∃ k : ℕ, (y ^ k)⁻¹ * a ∈ centralizer (Z : Set C)

@[expose] def SylowData (x : C) (Z : Subgroup C) : Prop :=
  ∀ w ∈ cent x, (∀ b : C, b * x * b⁻¹ ∈ cent x → w ∈ cent (b * x * b⁻¹)) →
    (∃ k : ℕ, w ^ 2 ^ k = 1) → w ∈ Z

structure ClassData (q : ℕ) (x : C) (Z : Subgroup C) : Prop where
  centre : CentreData x Z
  card : Nat.card Z = q
  charTwo : CharTwo x
  residual : ResidualMem x ∨ SplitData x Z

structure FusionData (Z : Subgroup C) (a : C) : Prop where
  commute : ∀ z ∈ Z, ∀ z' ∈ Z, z * (a * z' * a⁻¹) = a * z' * a⁻¹ * z
  inf_eq : ∀ z ∈ Z, ∀ z' ∈ Z, z = a * z' * a⁻¹ → z = 1

@[expose] def OtherClass (Z : Subgroup C) (a : C) (P : Set C) : Prop :=
  ∀ z ∈ Z, z ≠ 1 → ∀ z' ∈ Z, z' ≠ 1 → z * (a * z' * a⁻¹) ∈ P

structure LeviData (Z D Q H L : Subgroup C) : Prop where
  D_perfect : ⁅D, D⁆ = D
  D_le : D ≤ centralizer (Z : Set C)
  Q_le : Q ≤ D
  Q_ne_bot : Q ≠ ⊥
  odd_Q : Odd (Nat.card Q)
  Q_le_H : Q ≤ H
  H_comm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a
  H_le : H ≤ normalizer (L : Set C)
  L_le : L ≤ centralizer (Q : Set C)
  cent_eq : ∀ c ∈ centralizer (Q : Set C), ∃ h ∈ H, h⁻¹ * c ∈ L
  quasisimple : CFSG.Open.IsQuasisimple ↥L
  odd_center : Odd (Nat.card (center ↥L))
  Z_le : Z ≤ L

@[expose] def AutFix (Q L : Subgroup C) : Prop :=
  ∀ α : MulAut C, (∃ k : ℕ, α ^ 2 ^ k = 1) → (∀ y ∈ Q, α y = y) → (∀ y ∈ L, α y = y) → α = 1

@[expose] def D0Data (x : C) (Z : Subgroup C) : Prop :=
  ∀ S : Subgroup C, S ≤ cent x → Odd (Nat.card S) →
    ∃ D₀ : Subgroup C, ⁅D₀, D₀⁆ = D₀ ∧ D₀ ≤ centralizer (S : Set C) ∧ Z ≤ D₀ ∧
      ∀ W : Subgroup C, W ≤ Z → W ≠ ⊥ → ¬ D₀ ≤ normalizer (W : Set C)

@[expose] def ClassesCover (reps : List C) : Prop :=
  ∀ x : C, x * x = 1 → x ≠ 1 → ∃ y ∈ reps, IsConj y x

end CFSG.ComponentClassification.RankTwoExceptional.Exc
