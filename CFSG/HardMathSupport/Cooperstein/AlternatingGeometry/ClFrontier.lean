module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClTwoFinal
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClLam4Final
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightTenSFourFalse
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.Statement
public import CFSG.HardMathSupport.RichardWeiss.Proving.ShortFinal

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open scoped commutatorElement


theorem eightTenNodeColourFour_of_E0 (hE0 : E0Statement) (hE0n : E0NotYStatement) :
    EightTenNodeColourFour :=
  eightTenNodeColourFour_of_two_lam4
    (eightTenNodeColourFourTwo_of_move eightTenNodeColourFourTwoMove)
    (eightTenNodeColourFourLam4_of hE0 hE0n
      (eightTenNodeColourFourLam4Small_of_move eightTenNodeColourFourLam4SmallMove))

theorem eightTenResidualOutcomes_of_E0 (hE0 : E0Statement) (hE0n : E0NotYStatement) :
    EightTenResidualOutcomes :=
  eightTenResidualOutcomes_of_three Coordinator.eightTenNodeSFour (eightTenNodeFourOrbit_of_E0 hE0 hE0n)
    (eightTenNodeColourFour_of_E0 hE0 hE0n)

theorem e0Statement_proved : E0Statement :=
  fun _ _ _ _ _ _ hA hL hSL _ hN _ hNS hθS _hEO hJ _ hΔ₀ _ hPc hPsq hPfix hPtrans _ hωω hωΔ hωfree
      hθ hY =>
    CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.false_of_E0_HY hA hL hSL hN hNS hθS hΔ₀
      hPc hPsq hPfix hPtrans hωω hωΔ hωfree hθ hJ hY

theorem eightTenResidualOutcomes_of_E0n (hE0n : E0NotYStatement) : EightTenResidualOutcomes :=
  eightTenResidualOutcomes_of_E0 e0Statement_proved hE0n

theorem e0NotYStatement_of_nonshort (h : E0NonShortNotYStatement) : E0NotYStatement := by
  intro G _ _ X S L hA hL hSL N hN θ hNS hθS hEO hJ Δ₀ hΔ₀ P hPc hPsq hPfix hPtrans ω hωω hωΔ
    hωfree hθ hY
  by_cases hshort : ⁅pCoreOf 2 (L ⊔ S), L⁆ ≤ blockV S L
  · exact CFSG.HardMathSupport.RichardWeiss.Proving.false_of_E0_short hA hL hSL hN hNS hθS
      ⟨hΔ₀, hPsq, hPfix, hPc, hPtrans, hωω, hωΔ, hωfree⟩ hθ hshort
  · exact h G X S L hA hL hSL N hN θ hNS hθS hEO hJ Δ₀ hΔ₀ P hPc hPsq hPfix hPtrans ω hωω hωΔ
      hωfree hθ hY hshort

theorem eightTenResidualOutcomes_of_E0_nonshort (h : E0NonShortNotYStatement) :
    EightTenResidualOutcomes :=
  eightTenResidualOutcomes_of_E0n (e0NotYStatement_of_nonshort h)

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
