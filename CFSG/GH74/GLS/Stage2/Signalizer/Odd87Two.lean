module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoCov
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoTransport
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoVac
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L34Idx
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

theorem cell87_FTwo
    (h85e : Prop85e) (h85g : Prop85g) (hL34 : L34Aut) (hInv : InvSec) : Cell87 FTwo := by
  have hMin : MinIndexL34 := minIndexL34
  have hVac : TwoAutVac := twoAutVac
  intro h41a h41b G _ _ z k S hctx H₀ H₁ _ hz p X hsig hyp hFK
  classical
  have hd := CellData.of_ctx hctx hsig hyp
  rcases hFK with h | h | h | h | h
  ·
    have hZ : center ↥(layer (Sec H₀ H₁)) = ⊥ := center_eq_bot_psl2_even hd.quasi (Or.inl rfl) h
    have eq0 : (↥(layer (Sec H₀ H₁)) ⧸ center ↥(layer (Sec H₀ H₁))) ≃* ↥(layer (Sec H₀ H₁)) :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    have hL := Transport.lieModel_of_mulEquiv eq0 h
    exact (hVac _ (Or.inl hL) _ p _ (autCfg_of_cellData hd hZ)).elim
  ·
    have hZ : center ↥(layer (Sec H₀ H₁)) = ⊥ := center_eq_bot_psl2_even hd.quasi (Or.inr rfl) h
    have eq0 : (↥(layer (Sec H₀ H₁)) ⧸ center ↥(layer (Sec H₀ H₁))) ≃* ↥(layer (Sec H₀ H₁)) :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    have hL := Transport.lieModel_of_mulEquiv eq0 h
    exact (hVac _ (Or.inr (Or.inl hL)) _ p _ (autCfg_of_cellData hd hZ)).elim
  ·
    by_cases hZ : center ↥(layer (Sec H₀ H₁)) = ⊥
    · have eq0 : (↥(layer (Sec H₀ H₁)) ⧸ center ↥(layer (Sec H₀ H₁))) ≃* ↥(layer (Sec H₀ H₁)) :=
        (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
      have hL := Transport.lieModel_of_mulEquiv eq0 h
      obtain ⟨hPGL, hc3, hcent, hL2, hCJ⟩ := ftwo_L34_transport hd hZ hL hL34
      have hk := h85g h41a h41b G z k S hctx H₀ H₁ hz p X hsig hyp h hZ hL2
      exact Or.inr (Or.inr (Or.inr ⟨hk, hPGL, hL, hc3, hcent, hL2, hCJ⟩))
    · exact (not_kindFactorAll_l34 hMin k h (layerBar_kindFactor hInv hctx hsig hyp hZ)).elim
  ·
    exact (h85e h41a h41b G z k S hctx H₀ H₁ hz p X hsig hyp h).elim
  ·
    by_cases hZ : center ↥(layer (Sec H₀ H₁)) = ⊥
    · have eq0 : (↥(layer (Sec H₀ H₁)) ⧸ center ↥(layer (Sec H₀ H₁))) ≃* ↥(layer (Sec H₀ H₁)) :=
        (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
      have hL := Transport.lieModel_of_mulEquiv eq0 h
      exact (hVac _ (Or.inr (Or.inr hL)) _ p _ (autCfg_of_cellData hd hZ)).elim
    · exact (not_kindFactorAll_sz8 k h (layerBar_kindFactor hInv hctx hsig hyp hZ)).elim

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
