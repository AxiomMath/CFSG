module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtC137Cases
public import CFSG.Quasithin.H13.GoldschmidtC137U33Red

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def C137CaseU33R_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (X T V L P M : Subgroup G),
    CharTwo X → SQTKGroup ↥X → IsSylowTwoOf T X → (∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) →
    L ∈ cComp X → CharTwo L → LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 →
    T ≤ P → P ≤ M → M < X → (∀ H : Subgroup G, M ≤ H → H ≤ X → H = M ∨ H = X) → P = M →
    IsTwoReducedIn X V → ⁅V, L⁆ = V → V ≠ ⊥ → Concl X T V L P

theorem c137CaseU33_of_R_F4 (h : C137CaseU33R_F4) : C137CaseU33_F4 := by
  intro G _ _ X T V L P M hC hSQ hT hprod hL hL2 hlie hTP hPM hMX hmax hPeq hred hVL
  obtain ⟨hredU, hUU, hCeq⟩ := u33_reduce hred hT hprod hL hlie hVL
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hn : X ≤ normalizer (L : Set G) := C124.le_normalizer_of_prod hT hprod hL
  have hLN : L ≤ normalizer (V : Set G) := hLX.trans hred.2.1
  have hUV : ⁅V, L⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLN
  have hPX : P ≤ X := (hPM.trans hMX.le)
  have hc := h G X T ⁅V, L⁆ L P M hC hSQ hT hprod hL hL2 hlie hTP hPM hMX hmax hPeq hredU hUU hVL
  exact concl_of_U hred hn hPX hCeq hredU.2.2.1 hUV hredU.2.1 hlie hc

end CFSG.Quasithin.H13.U3.GC137
