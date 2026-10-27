module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Assembly8
public import CFSG.HardMathSupport.Lang.D4Three.Assembly
public import CFSG.HardMathSupport.Lang.D4Three.CharThree
public import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Bridge
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4Final

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open TauCeti

theorem d4Bridge_holds : CFSG.HardMathSupport.Lang.D4Three.D4Bridge :=
  fun q hv F _ _ hF =>
    CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_adjointQuotient_D4_equiv F q hv hF

theorem d4FixedBound_holds : CFSG.HardMathSupport.Lang.D4Three.D4FixedBound := by
  intro F _ _ α hα3 hα
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hpr, hn⟩ := FiniteField.card F (ringChar F)
  have : Fact (ringChar F).Prime := ⟨hpr⟩
  have hK : Nat.card F = ringChar F ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hn]
  by_cases h3 : ringChar F = 3
  · have : CharP F 3 := by rw [← h3]; exact ringChar.charP F
    exact CFSG.HardMathSupport.Lang.D4Three.twentySeven_dvd_fixedSubgroup_D4_char3 α hα3 hα
  · exact CFSG.HardMathSupport.Lang.E6Descent.twentySeven_dvd_fixedSubgroup_adjointD4
      (ℓ := ringChar F) n.pos F hK
      (fun h => h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpr).1 h).symm) α hα3 hα

theorem e27LieOuterAutAt_D4_proved :
    E27LieOuterAutAt (fun i => ∃ q, i = .D 4 q) :=
  CFSG.HardMathSupport.Lang.D4Three.e27LieOuterAutAt_D4_of_bridge d4Bridge_holds
    d4FixedBound_holds

theorem e27LieOuterAut_proved : CFSG.HardMathSupport.Foote.E27.E27LieOuterAut :=
  e27LieOuterAut_of_D4 e27LieOuterAutAt_D4_proved

end CFSG.HardMathSupport.Malle.E27Lie
