module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Defs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section ABar

variable {Y : Type} [Group Y] [Finite Y]

@[expose] def p23ABar (t u e : Y) :
    Subgroup (↥(Subgroup.centralizer ({t} : Set Y)) ⧸
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y))) :=
  Subgroup.closure {q | ∃ x : ↥(Subgroup.centralizer ({t} : Set Y)),
    (∃ c ∈ Subgroup.centralizer ({t} : Set Y), (x : Y) = c * (u * e) * c⁻¹) ∧
      q = (x : ↥(Subgroup.centralizer ({t} : Set Y)) ⧸
        classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)))}

theorem comm_of_mem_p23ABar {t u e : Y}
    (hab : ∀ a ∈ p23ABar t u e, ∀ b ∈ p23ABar t u e, a * b = b * a) {A : Subgroup Y}
    (hAC : A ≤ Subgroup.centralizer ({t} : Set Y)) (hA2 : IsPGroup 2 A)
    (hAB : ∀ (a : Y) (ha : a ∈ A), ((⟨a, hAC ha⟩ : ↥(Subgroup.centralizer ({t} : Set Y))) :
      ↥(Subgroup.centralizer ({t} : Set Y)) ⧸
        classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y))) ∈ p23ABar t u e) :
    ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
  intro a ha b hb
  set C := Subgroup.centralizer ({t} : Set Y)
  set a' : ↥C := ⟨a, hAC ha⟩
  set b' : ↥C := ⟨b, hAC hb⟩
  have h := hab _ (hAB a ha) _ (hAB b hb)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h
  have hw : (a * b)⁻¹ * (b * a) ∈ Asc77.oddCoreOf C := ⟨_, h, rfl⟩
  have hwA : (a * b)⁻¹ * (b * a) ∈ A := A.mul_mem (A.inv_mem (A.mul_mem ha hb)) (A.mul_mem hb ha)
  have h1 : (a * b)⁻¹ * (b * a) = 1 :=
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard C) hw
      (hA2.to_le (Subgroup.zpowers_le.mpr hwA))
  calc a * b = (a * b) * ((a * b)⁻¹ * (b * a)) := by rw [h1, mul_one]
    _ = b * a := by group

end ABar

section E7

variable {n : ℕ}

@[expose] def P23E7AE6 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → ECase1 R W e → SecAE R e 6 → False

@[expose] def P23E7ZC (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → ECase1 R W e →
      u * e ∈ zStarOf (rLayer (Om R) u) →
        u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y))

@[expose] def P23E7Elem (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → ECase1 R W e →
      u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y)) →
        ∀ a ∈ p23ABar t u e, ∀ b ∈ p23ABar t u e, a * b = b * a

@[expose] def P23E7Strong (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → ECase1 R W e →
      u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y)) →
        ∃ (T : Sylow 2 Y) (A : Subgroup Y) (hAC : A ≤ Subgroup.centralizer ({t} : Set Y)),
          A ≤ (T : Subgroup Y) ∧ u * e ∈ A ∧ IsPGroup 2 A ∧
          (∀ (a : Y) (ha : a ∈ A), ((⟨a, hAC ha⟩ : ↥(Subgroup.centralizer ({t} : Set Y))) :
            ↥(Subgroup.centralizer ({t} : Set Y)) ⧸
              classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y))) ∈
                p23ABar t u e) ∧
          ∀ a ∈ A, ∀ x : Y, x⁻¹ * a * x ∈ (T : Subgroup Y) → x⁻¹ * a * x ∈ A

end E7

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
