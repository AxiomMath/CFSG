module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemL
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLFam

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


section SecV

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y} {Z V : Subgroup Y}

theorem om_facts (hc : P23Cfg n Y R S t K' W u e g) :
    HypOmegaGen (Om R) ∧ (∀ M ∈ Om R, AEmpty (Om R) M) ∧
      (∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M)) ∧
      (∀ M ∈ Om R, ∀ P : Subgroup Y, IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup 2)) := by
  have hC := CoreData.of_S hc.std.perp.core
  exact ⟨hC.hyp, hC.aEmpty_all,
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup),
    members_sylow_q8 hc.std.perp⟩

theorem p23SecFamV_pSpan (R V : Subgroup Y) : TC.Thin.pSpan (p23SecFamV R V) = ⊤ :=
  sylFamA_gen

theorem p23SecFamV_hypOmegaGen (hc : P23Cfg n Y R S t K' W u e g) (hZ : P23ZData t u e Z)
    (hVZ : V ≤ Z) (hL1 : SecCoresTwoGroup (Om R) V) : HypOmegaGen (p23SecFamV R V) :=
  sylFamA_hypOmegaGen (om_facts hc).1 hL1

theorem p23SecFamV_aEmpty (hc : P23Cfg n Y R S t K' W u e g) (hZ : P23ZData t u e Z)
    (hVZ : V ≤ Z) (hL1 : SecCoresTwoGroup (Om R) V) :
    ∀ L ∈ p23SecFamV R V, AEmpty (p23SecFamV R V) L :=
  sylFamA_aEmpty (om_facts hc).1 (om_facts hc).2.1 ((P23ZData.isPGroup hZ).to_le hVZ)
    (om_facts hc).2.2.1 hL1

theorem p23SecFamV_isPGroup (hL1 : SecCoresTwoGroup (Om R) V) :
    ∀ L ∈ p23SecFamV R V, IsPGroup 2 ↥L :=
  sylFamA_isPGroup hL1

theorem p23SecFamV_q8 (hc : P23Cfg n Y R S t K' W u e g) (hL1 : SecCoresTwoGroup (Om R) V) :
    ∀ L ∈ p23SecFamV R V, Nonempty (↥L ≃* QuaternionGroup 2) :=
  sylFamA_q8 (om_facts hc).2.2.2 hL1

theorem p23SecFamV_card (hc : P23Cfg n Y R S t K' W u e g) (hL1 : SecCoresTwoGroup (Om R) V) :
    ∀ L ∈ p23SecFamV R V, Nat.card ↥L = 2 ^ 3 :=
  sylFamA_card (om_facts hc).2.2.2 hL1

end SecV

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
