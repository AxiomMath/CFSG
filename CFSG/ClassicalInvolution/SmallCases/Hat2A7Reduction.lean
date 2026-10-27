module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7StepQuasisimple
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.SmallCases.SingleComponent
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7StepSplit

public section

namespace CFSG.ClassicalInvolution.Hat2A7

open CFSG.Open CFSG.ClassicalInvolution.Generic

theorem isQuasisimple_of_inClass2A7 {Y : Type} [Group Y] [Finite Y]
    (hO : classicalInvolutionOddCore Y = ⊥) {Λ : Set (Subgroup Y)} (hΛ : InClass2A7 Λ)
    (hconn : NonCommConnected Λ) : CFSG.Open.IsQuasisimple Y :=
  isQuasisimple_of_members l2PrimeBalance hO hΛ.nonempty hΛ.generated
    (fun L hL => by
      obtain ⟨z, hz⟩ := hΛ.classical L hL
      refine ⟨z, hz.orderOf_eq_two, hz.mem, hz.perfect.commutator_eq_top, ?_, hz.witness.1⟩
      have h1 := hz.subnormal
      rwa [top_inf_eq] at h1) hconn

theorem a7SystemMod_of_corefree (hcore : CoreStep2A7) {Y : Type} [Group Y] [Finite Y]
    (hBelow : CITBelow2A7 (Nat.card Y)) (hO : classicalInvolutionOddCore Y = ⊥)
    {Λ : Set (Subgroup Y)} (hΛ : InClass2A7 Λ) : A7SystemMod Λ := by
  by_cases hconn : NonCommConnected Λ
  · exact a7SystemMod_of_quasisimple hcore hBelow hO hΛ (isQuasisimple_of_inClass2A7 hO hΛ hconn)
  · exact a7SystemMod_of_a7System_corefree hO (a7System_of_not_connected hBelow hO hΛ hconn)

theorem citStep2A7_of_coreStep (hcore : CoreStep2A7) (n : ℕ) : CITStep2A7 n := by
  intro hBelow Y _ _ hY Λ hΛ
  have hBelow' : CITBelow2A7 (Nat.card Y) := by rw [hY]; exact hBelow
  by_cases hO : classicalInvolutionOddCore Y = ⊥
  · exact a7SystemMod_of_corefree hcore hBelow' hO hΛ
  · exact a7SystemMod_of_oddQuotient hBelow' hO hΛ

theorem stepReduction2A7 : StepReduction2A7 := fun hcore n => citStep2A7_of_coreStep hcore n

theorem citInductive2A7_of_coreStep (hcore : CoreStep2A7) : CITInductive2A7 :=
  citInductive2A7_of_step (citStep2A7_of_coreStep hcore)

theorem cit2A7_of_remaining_inputs (h : GoldschmidtMilestone) (TW : TwinExclusion)
    (LOC : LocalOddCentralStep2A7) : CIT2A7 :=
  cit2A7_of_milestone h TW LOC stepReduction2A7

end CFSG.ClassicalInvolution.Hat2A7
