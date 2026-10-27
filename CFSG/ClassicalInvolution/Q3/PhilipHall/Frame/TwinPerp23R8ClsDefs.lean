module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AZ8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


section ClsDefs

@[expose] def P23E8AZ8M (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → SecAE R u 5 → SecAE R e 6 →
      ∀ y ∈ rLayer (Om R) u, y * t = t * y → IsPGroup 3 (Subgroup.zpowers y) →
        (∀ o ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)), y * e * y⁻¹ ≠ o * e * o⁻¹) →
          ∀ m ∈ Subgroup.centralizer ({t} : Set Y),
            (∀ l ∈ tightCore R ⊔ K', m * l * m⁻¹ * l⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y))) →
              ∃ i : ℕ, i < 3 ∧ ∃ o ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)),
                m * e * m⁻¹ = o * (y ^ i * e * (y ^ i)⁻¹) * o⁻¹

@[expose] def P23E8AZ8Out (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → SecAE R u 5 → SecAE R e 6 →
      ∀ c ∈ Subgroup.centralizer ({t} : Set Y), ∃ m ∈ Subgroup.centralizer ({t} : Set Y),
        (∀ l ∈ tightCore R ⊔ K', m * l * m⁻¹ * l⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y))) ∧
          ∃ o ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)), c * e * c⁻¹ = o * (m * e * m⁻¹) * o⁻¹

variable {n : ℕ} in
theorem p23E8AZ8Cls_of_parts (hM : P23E8AZ8M n) (hO : P23E8AZ8Out n) : P23E8AZ8Cls n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hA5 hA6 y hyY hyt hy3 hmove c hc'
  obtain ⟨m, hmC, hmM, o, ho, hco⟩ := hO hcit hP Y R S t K' W u e g hc hno hA5 hA6 c hc'
  obtain ⟨i, hi, o', ho', hmo⟩ :=
    hM hcit hP Y R S t K' W u e g hc hno hA5 hA6 y hyY hyt hy3 hmove m hmC hmM
  refine ⟨i, hi, o * o', Subgroup.mul_mem _ ho ho', ?_⟩
  rw [hco, hmo]
  group

end ClsDefs

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
