module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AZData
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ClsMMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


section ClsOut

@[expose] def P23MOrb {Y : Type} [Group Y] (R K' : Subgroup Y) (t e f : Y) : Prop :=
  ∃ m ∈ Subgroup.centralizer ({t} : Set Y),
    (∀ l ∈ tightCore R ⊔ K', m * l * m⁻¹ * l⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y))) ∧
      ∃ o ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)), f = o * (m * e * m⁻¹) * o⁻¹

@[expose] def P23E8OBig (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → SecAE R u 5 → SecAE R e 6 →
      ∀ Z : Subgroup Y, P23ZData t u e Z → ∀ f ∈ p23Orb Z t e, ¬ P23MOrb R K' t e f →
        32 ≤ Nat.card Z

@[expose] def P23E8ON7 (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → SecAE R u 5 → SecAE R e 6 →
      ∀ Z : Subgroup Y, P23ZData t u e Z → (aSub R Z e).relIndex Z ≤ 4

@[expose] def P23E8OL7 (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → SecAE R u 5 → SecAE R e 6 →
      ∀ Z : Subgroup Y, P23ZData t u e Z → ∀ f ∈ p23Orb Z t e, aSub R Z e ⊓ aSub R Z f ≠ ⊥ →
        P23MOrb R K' t e f

variable {n : ℕ}

theorem p23E8AZ8Out_of_parts (hB : P23E8OBig n) (h7 : P23E8ON7 n) (hL : P23E8OL7 n) :
    P23E8AZ8Out n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hA5 hA6 c hc'
  obtain ⟨Z, hZd⟩ := p23_zdata_of_ae5 hcit hP hc hno hA5 hA6
  obtain ⟨o, ho, m, hm, rfl⟩ := hZd.frattini c hc'
  have hf : m * e * m⁻¹ ∈ p23Orb Z t e := ⟨m, hm, rfl⟩
  suffices h : P23MOrb R K' t e (m * e * m⁻¹) by
    obtain ⟨m', hm'C, hm'M, o', ho', heq⟩ := h
    refine ⟨m', hm'C, hm'M, o * o', Subgroup.mul_mem _ ho ho', ?_⟩
    rw [show o * m * e * (o * m)⁻¹ = o * (m * e * m⁻¹) * o⁻¹ by group, heq]
    group
  by_contra hno'
  have h32 := hB hcit hP Y R S t K' W u e g hc hno hA5 hA6 Z hZd _ hf hno'
  have ha4 := h7 hcit hP Y R S t K' W u e g hc hno hA5 hA6 Z hZd
  have haf : (aSub R Z (m * e * m⁻¹)).relIndex Z = (aSub R Z e).relIndex Z := hZd.relIndex_aSub hf
  have hB16 : (aSub R Z e ⊓ aSub R Z (m * e * m⁻¹)).relIndex Z ≤ 16 := by
    have := (Subgroup.relIndex_inf_le : (aSub R Z e ⊓ aSub R Z (m * e * m⁻¹)).relIndex Z ≤
      (aSub R Z e).relIndex Z * (aSub R Z (m * e * m⁻¹)).relIndex Z)
    rw [haf] at this
    nlinarith
  have hne : aSub R Z e ⊓ aSub R Z (m * e * m⁻¹) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.relIndex_bot_left] at hB16
    omega
  exact hno' (hL hcit hP Y R S t K' W u e g hc hno hA5 hA6 Z hZd _ hf hne)

theorem p23E8AZ8Cls_of_out (hB : P23E8OBig n) (h7 : P23E8ON7 n) (hL : P23E8OL7 n) : P23E8AZ8Cls n :=
  p23E8AZ8Cls_of_parts ClsM.p23E8AZ8M_proved (p23E8AZ8Out_of_parts hB h7 hL)

end ClsOut

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
