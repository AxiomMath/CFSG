module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf47W
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf45M12
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43L3E8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf42U3Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf49G23Row
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm3QuotRows
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.Defs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Core CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ComponentClassification.AS76b

section Rows

@[expose] def FrameCaseITGN : Prop :=
  ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], Thm3A.Thm3RBelowG (Nat.card T) →
    (∃ a b : T, a * b ≠ b * a) → CIT3Below (Nat.card T) →
    TL4.TightBelowRPlus 3 (Nat.card T) →
    ∀ (R : Subgroup T) (t : T), FrameTightDatum R t →
      ∀ (J : Subgroup T) (zK zJ : T), AViol (CoreAssembly.conjClass R) R J zK zJ →
        aStar (CoreAssembly.conjClass R) R ≠ CoreAssembly.conjClass R → False

@[expose] def FrameCaseIITGN : Prop :=
  ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], Thm3A.Thm3RBelowG (Nat.card T) →
    (∃ a b : T, a * b ≠ b * a) → CIT3Below (Nat.card T) →
    TL4.TightBelowRPlus 3 (Nat.card T) →
    ∀ (R : Subgroup T) (t : T), FrameTightDatum R t →
      ∀ (J : Subgroup T) (zK zJ a g : T),
        AViol (CoreAssembly.conjClass R) R J zK zJ →
        a ∈ pairNormalizers R J zK zJ → a * zJ * a⁻¹ = zK → conjSub a J ≠ R →
        conjSub g R = conjSub a J → g * zK * g⁻¹ = zK →
        aStar (CoreAssembly.conjClass R) R = CoreAssembly.conjClass R → False

theorem frameCaseITG_of_N (h : FrameCaseITGN) : FrameCaseITG :=
  fun T _ _ _ hT hnab hB hP _ R t hD J zK zJ hv hne => h T hT hnab hB hP R t hD J zK zJ hv hne

theorem frameRowsTG_of_thm3 {T : Type} [Group T] [Finite T]
    {R : Subgroup T} {t : T} {J : Subgroup T} {zK zJ : T}
    (hT : Thm3A.Thm3RBelowG (Nat.card T)) (hh : FrameCaseIHyps T R t J zK zJ)
    {H : Subgroup T} (hH : omegaGen (aStar (CoreAssembly.conjClass R) R) = H) :
    Thm3A.Thm3RowsG (restrictFamily (CoreAssembly.conjClass R) H) (⊤ : Subgroup ↥H) := by
  have hΩg : HypOmegaGen (CoreAssembly.conjClass R) := hh.datum.hyp
  have hK : R ∈ CoreAssembly.conjClass R := CoreAssembly.mem_conjClass_self R
  have htrans : ∀ M ∈ CoreAssembly.conjClass R, ∃ g : T, conjSub g R = M := by
    intro M hM
    obtain ⟨g, rfl⟩ := hM
    exact ⟨g, rfl⟩
  have hKS : R ∈ aStar (CoreAssembly.conjClass R) R := Relation.ReflTransGen.refl
  have hJS : J ∈ aStar (CoreAssembly.conjClass R) R :=
    Relation.ReflTransGen.single ⟨hh.viol.mem, Or.inl ⟨zK, zJ, hh.viol⟩⟩
  have hKH : R ≤ H := hH ▸ le_omegaGen hKS
  have hJH : J ≤ H := hH ▸ le_omegaGen hJS
  have hHtop : H ≠ ⊤ := fun h =>
    hh.ne (aStar_eq_of_omegaGen_eq_top hΩg.conjInvariant hK htrans (hH.trans h))
  have hlt : Nat.card ↥H < Nat.card T :=
    lt_of_le_of_ne (Subgroup.card_le_card_group H)
      (fun h => hHtop ((Subgroup.card_eq_iff_eq_top H).mp h))
  have hΔ : TypeRHyp (restrictFamily (CoreAssembly.conjClass R) H) :=
    (typeRHyp_of_datum hh.datum).restrict H
  have hKΔ : R.subgroupOf H ∈ restrictFamily (CoreAssembly.conjClass R) H :=
    subgroupOf_mem_restrictFamily hK hKH
  have hnA : ¬ AEmpty (restrictFamily (CoreAssembly.conjClass R) H) (R.subgroupOf H) :=
    not_aEmpty_iff.mpr ⟨J.subgroupOf H, _, _, aViol_restrict_gen hΩg hKH hJH hh.viol⟩
  have hrows := (Thm3Quot.thm3RowsG_omegaGen_aStar_of_quot
    (Thm3A.thm3RGroupQuotG_of_belowG hT hlt) hΔ hKΔ hnA).1
  rwa [omegaGen_aStar_restrict hΩg hH] at hrows

theorem frameCaseI_false_of_rows (h4 : Asc75Theorem4) (hG : FrameC201G23Sec)
    (hU : FrameC201U3FalseF) (hM : FrameC201M12FalseB) (hL : FrameC201L3E8FalseB)
    (hW : FrameC201WFalseB) {T : Type} [Group T] [Finite T] [CaseIAmbient T]
    (hT : Thm3A.Thm3RBelowG (Nat.card T)) {R : Subgroup T} {t : T} {J : Subgroup T}
    {zK zJ : T} (hh : FrameCaseIHyps T R t J zK zJ) : False := by
  obtain ⟨H, hH⟩ : ∃ H, omegaGen (aStar (CoreAssembly.conjClass R) R) = H := ⟨_, rfl⟩
  rcases frameRowsTG_of_thm3 hT hh hH with h | h | h | h | h
  · exact frame_false_of_g2Section h4 hh hH (hG T R t J zK zJ hh H hH h)
  · exact hU T R t J zK zJ hh H hH h
  · exact hM T hT R t J zK zJ hh H hH h
  · exact hL T hT R t J zK zJ hh H hH h
  · exact hW T hT R t J zK zJ hh H hH h

end Rows

theorem frameCaseITF_holds_explicit :
    ∀ (T : Type) [Group T] [Finite T], Thm3Step.FStarSimple T → classicalInvolutionOddCore T = ⊥ →
      Thm3A.Thm3RBelowG (Nat.card T) → (∃ a b : T, a * b ≠ b * a) → CIT3Below (Nat.card T) →
      TL4.TightBelowRPlus 3 (Nat.card T) →
      ∀ (R : Subgroup T) (t : T), FrameTightDatum R t →
        ∀ (J : Subgroup T) (zK zJ : T), AViol (CoreAssembly.conjClass R) R J zK zJ →
          aStar (CoreAssembly.conjClass R) R ≠ CoreAssembly.conjClass R → False := by
  intro T _ _ hF hO hT hnab hB hP R t hD J zK zJ hv hne
  haveI : CaseIAmbient T := ⟨hF.1, hF.2, hO⟩
  exact frameCaseI_false_of_rows CFSG.ComponentClassification.RankTwoFoundation.asc75Theorem4
    frameC201G23Sec_proved frameC201U3FalseF_proved frameC201M12False_of_certs
    frameC201L3E8False_of_certs frameC201WFalse_of_certs hT ⟨hnab, hB, hP, hD, hv, hne⟩

theorem frameCaseITGN_proved :
    FrameCaseITGN := by
  intro T _ _ _ hT hnab hB hP R t hD J zK zJ hv hne
  have h := CaseIAmbient.of_simple hnab hD.unique.sq hD.unique.ne_one
  exact frameCaseITF_holds_explicit T ⟨h.fstar_simple, h.fstar_nonabelian⟩ h.oddCore_eq_bot hT
    hnab hB hP R t hD J zK zJ hv hne

theorem frameCaseITG_proved :
    FrameCaseITG :=
  frameCaseITG_of_N frameCaseITGN_proved

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
