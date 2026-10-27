module

public import CFSG.CGT.M24S.Local
public import CFSG.CGT.M24S.CoreTrivial
public import CFSG.CGT.M24S.NSMain
public import CFSG.Holt.H78.Theorem1
public import CFSG.CGT.M24S.Type4
public import CFSG.CGT.M24R.Final
public import CFSG.CGT.T75P.Inputs
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.CGT.M24S

open CFSG.Open CFSG.CGT.Timmesfeld75

@[expose] def CaseLInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ T H : Subgroup G, T ≤ H → IsWC T → NaturalSL T H 4 1 → Odd H.index → ¬ HasType4 T →
      StatedClassicalModel G .PSL 5 2 1

theorem m24SylowInput_of_caseL_of_holt
    (hHolt : CFSG.Holt.H78.HoltTheorem1) (hCL : CaseLInput) : CFSG.CGT.T75P.M24SylowInput := by
  intro G _ _ _ hna T H hTH hT hN hodd
  by_cases h4 : HasType4 T
  · obtain ⟨x, g, hxN, hxT, hxg, hcx⟩ := h4
    have h : Hyp T H := ⟨hTH, hT, hN, hodd⟩
    have hL := h.localFacts
    have hC : Subgroup.centralizer (T : Set G) = T := centralizer_eq_self hna hHolt h hL
    exact Or.inr (CFSG.CGT.M24R.isSporadic_m24_of_type4_of_holt hHolt h hL hC
      (hasComplement_of_hyp hHolt h hL hC) hxN hxT hxg hcx)
  · exact Or.inl (hCL G hna T H hTH hT hN hodd h4)

theorem m24SylowInput_of_caseL
    (hCL : CaseLInput) : CFSG.CGT.T75P.M24SylowInput :=
  m24SylowInput_of_caseL_of_holt CFSG.Holt.H78.holtTheorem1 hCL

end CFSG.CGT.M24S
