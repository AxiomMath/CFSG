module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7NInduction
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7NTightD
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7LocalB

public section

namespace CFSG.ClassicalInvolution.Hat2A7N

open CFSG.Open CFSG.ClassicalInvolution.Hat2A7

theorem false_of_classical2A7N {F : Type} [Group F] [Finite F] [IsSimpleGroup F]
    (hnab : ∃ a b : F, a * b ≠ b * a) (GS : GoldschmidtStronglyClosedExponent)
    (TW : TwinExclusion) {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z)
    (htight : Subgroup.centralizer ({z} : Set F) ≤ Subgroup.normalizer (K : Set F) →
      TightIH K z ∧ TightP1 K)
    (htwin : ¬ Subgroup.centralizer ({z} : Set F) ≤ Subgroup.normalizer (K : Set F) →
      ClassicalCommuteBelow F ∧ ClassicalQuasisimple F) : False := by
  by_cases ht : Subgroup.centralizer ({z} : Set F) ≤ Subgroup.normalizer (K : Set F)
  · exact TightSettingN.false_of_goldschmidt hnab GS
      ⟨⟨hK, ht⟩, center_trivial_of_simple hnab, (htight ht).1, (htight ht).2⟩
  · obtain ⟨IH, P1⟩ := htwin ht
    exact TW F hnab IH P1 K z hK ht

theorem coreStep2A7_of_inputsN (GS : GoldschmidtStronglyClosedExponent) (TW : TwinExclusion)
    (LOCN : LocalOddCentralStep2A7N) : CoreStep2A7 := by
  intro G _ _ _ hnab K z hK hB
  obtain ⟨hT, hNT⟩ := LOCN G hnab K z hK hB
  have hZ := center_trivial_of_simple hnab
  exact false_of_classical2A7N hnab GS TW hK
    (fun ht => ⟨tightIH_of_localOddCentral hB hZ (hT ht),
      tightP1_of_localOddCentral hZ hK (hT ht)⟩)
    (fun ht => ⟨classicalCommuteBelow_of_induction hB (hNT ht),
      classicalQuasisimple_of_localOddCentral hZ (hNT ht)⟩)

theorem localOddCentralStep2A7N_of_B (h : A7BStep) : LocalOddCentralStep2A7N :=
  localOddCentralStep2A7N_of_full (localOddCentralStep2A7_of_B h)

theorem cit2A7_of_remaining_inputsN (h : GoldschmidtMilestone) (TW : TwinExclusion)
    (LOCN : LocalOddCentralStep2A7N) : CIT2A7 :=
  cit2A7_of_inductive (citInductive2A7_of_coreStep
    (coreStep2A7_of_inputsN (goldschmidtStronglyClosedExponent_of_milestone h) TW LOCN))

end CFSG.ClassicalInvolution.Hat2A7N
