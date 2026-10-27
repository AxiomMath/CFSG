module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SecondLayerFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalG3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Core22
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SecondLayerA

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {L S A B Aa : Subgroup G} {z b : G}

omit [Finite G] in
theorem ThLocalIn3.transvCent (W3 : ThLocalIn3 L S A B Aa) : TransvCent L A B Aa :=
  fun g hg hn hB hH K hK hKc => by
    obtain ⟨H, hHA, hHc, hHg⟩ := hH
    refine W3.transv g hg hn hB ⟨H, hHA, hHc, fun a ha => ?_⟩ K hK fun x hx => ?_
    · have h := hHg a ha
      calc g * a = (g * a * g⁻¹) * g := by group
        _ = a * g := by rw [h]
    · have h := hKc x hx
      calc g * x = (g * x * g⁻¹) * g := by group
        _ = x * g := by rw [h]

theorem SylowFacts.of_localIn3 (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (W3 : ThLocalIn3 L S A B Aa) : SylowFacts L S B Aa :=
  SylowFacts.of_transvCent W W2 W3.transvCent W3.center_quotient

@[expose] def ThCycContra3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L R : Subgroup G) (t : G),
    ThCyc G L R t → ThLocalData3 ↥L → False

theorem thCycContra3_of_secondLayer (h : ThSecondLayer) : ThCycContra3 := by
  intro G _ _ L R t H D3
  obtain ⟨S, A, B, z, Aa, b, W, W2, W3⟩ := D3.exists_localIn3
  have hF := SylowFacts.of_localIn3 W W2 W3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := (H.isPGroup_S_sup_Bp W).exists_le_sylow
  have hSt : S ⊔ zpowers t ≤ P :=
    (sup_le_sup_left (zpowers_le.2 (H.t_mem_Bp W W2)) S).trans hP
  exact h G L R t S A B Aa z b H W W2 hF P P.isPGroup' hP
    (H.not_sylow_le_normalizer W W2 hF P P.isPGroup' (Sylow.not_dvd_index P) hSt)

section Certified


theorem thCore_of_cycContra3 (h : ThCycContra3) (hTh : ThLocalData3 (Carrier .Th)) : ThCore := by
  intro G _ _ hs hn F t hF ht hC hnc
  obtain ⟨e⟩ := hF
  have hD : ThData ↥F := ThData.of_mulEquiv e thData_th
  exact h G F (zpowers t) t (thCyc_of_core hs hn hD ht hC hnc) (ThLocalData3.of_mulEquiv e hTh)

theorem th_not_standard_of_secondLayerA (h : ThSecondLayerA) (hTh : ThLocalData3 (Carrier .Th))
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hstd : StdHyp G L) :
    ¬ IsSporadic L .Th :=
  th_not_standard_of_core
    (thCore_of_cycContra3 (thCycContra3_of_secondLayer (thSecondLayer_of_A h)) hTh) hstd

end Certified

end CFSG.EvenSporadicStandard.ThStd
