module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtC137Cases
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtC137H6Two
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtC137S6Case
public import CFSG.Quasithin.H13.GoldschmidtC137H6CaseI

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

theorem c137CaseS6HatM_of_F4 (hC124 : ∀ (G : Type) [Group G] [Finite G], C124StatementSQTK (G := G))
    (hC132 : CFSG.Quasithin.ASInputs.AS_C_1_32_F4) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (X T V L P M : Subgroup G),
      CharTwo X → SQTKGroup ↥X → IsSylowTwoOf T X → (∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) →
      L ∈ cComp X → CharTwo L → A6.IsHatA6 L →
      ¬ autOn T V ≤ autOn L V →
      T ≤ P → P ≤ M → M < X → (∀ H : Subgroup G, M ≤ H → H ≤ X → H = M ∨ H = X) →
      (P = M ∨ (A6.IsHatA6 L ∧ P.relIndex M = 3 ∧ ¬ oTwoUpper P ≤ A6.o2Z L)) →
      ∀ hred : IsTwoReducedIn X V, ⁅V, L⁆ ≠ ⊥ →
        (∃ k, (k = B3.Mod.ut0 ∨ k = B3.Mod.u0) ∧ Nonempty (KModel k (autI hred.2.2.1 L))) →
        Concl X T V L P := by
  intro G _ _ X T V L P M hX hSQ hT hprod hL hL2 hhat hnin hTP hPM hMX hmax hPeq hred hVL hmod
  have h : H6Ctx X T V L P :=
    ⟨hX, hSQ, hT, hprod, hL, hL2, hhat, hnin, hTP, lt_of_le_of_lt hPM hMX, hred, hVL, hmod⟩
  by_cases hDP : A6.o2Z L ≤ P
  · exact concl_caseI (hC124 G) h hDP
  · rcases hPeq with rfl | ⟨-, h3, -⟩
    · exact absurd (by
        have := h.D_le_of_maximal hTP hMX hmax
        rwa [h.D_eq_o2Z] at this) hDP
    · exact concl_caseII_F4 (hC124 G) hC132 h hPM hMX hmax h3 hDP

theorem c137CaseS6Hat_of_F4 (hC124 : ∀ (G : Type) [Group G] [Finite G], C124StatementSQTK (G := G))
    (hC132 : CFSG.Quasithin.ASInputs.AS_C_1_32_F4) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (X T V L P M : Subgroup G),
      CharTwo X → SQTKGroup ↥X → IsSylowTwoOf T X → (∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) →
      L ∈ cComp X → CharTwo L → A6.IsHatA6 L →
      ¬ autOn T V ≤ autOn L V → (∃ _ : IsMulCommutative ↥V,
        AlternatingNatural (V := ↥V) (autOn L V) ⊤ ⊥ 6) →
      T ≤ P → P ≤ M → M < X → (∀ H : Subgroup G, M ≤ H → H ≤ X → H = M ∨ H = X) →
      (P = M ∨ (A6.IsHatA6 L ∧ P.relIndex M = 3 ∧ ¬ oTwoUpper P ≤ A6.o2Z L)) →
      IsTwoReducedIn X V → ⁅V, L⁆ ≠ ⊥ → Concl X T V L P := by
  intro G _ _ X T V L P M hX hSQ hT hprod hL hL2 hhat hnin hnat hTP hPM hMX hmax hPeq hred hVL
  exact c137CaseS6HatM_of_F4 hC124 hC132 G X T V L P M hX hSQ hT hprod hL hL2 hhat hnin hTP hPM hMX
    hmax hPeq hred hVL (model_of_natural hred.2.2.1 hnat)

theorem c137CaseS6M_of_F4 (hC124 : ∀ (G : Type) [Group G] [Finite G], C124StatementSQTK (G := G))
    (hC132 : CFSG.Quasithin.ASInputs.AS_C_1_32_F4) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (X T V L P M : Subgroup G),
      CharTwo X → SQTKGroup ↥X → IsSylowTwoOf T X → (∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) →
      L ∈ cComp X → CharTwo L →
      (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) ∨ A6.IsHatA6 L) →
      ¬ autOn T V ≤ autOn L V →
      T ≤ P → P ≤ M → M < X → (∀ H : Subgroup G, M ≤ H → H ≤ X → H = M ∨ H = X) →
      (P = M ∨ (A6.IsHatA6 L ∧ P.relIndex M = 3 ∧ ¬ oTwoUpper P ≤ A6.o2Z L)) →
      ∀ hred : IsTwoReducedIn X V, ⁅V, L⁆ ≠ ⊥ →
        (∃ k, (k = B3.Mod.ut0 ∨ k = B3.Mod.u0) ∧ Nonempty (KModel k (autI hred.2.2.1 L))) →
        Concl X T V L P := by
  intro G _ _ X T V L P M hX hSQ hT hprod hL hL2 htype hnin hTP hPM hMX hmax hPeq hred hVL hmod
  rcases htype with ha | hh
  · exact c137CaseS6A6M_of_F4 hC124 hC132 G X T V L P M hX hSQ hT hprod hL hL2 ha hnin hTP hPM hMX
      hmax (hPeq.resolve_right fun h' => not_hatA6_of_a6 ha h'.1) hred hVL hmod
  · exact c137CaseS6HatM_of_F4 hC124 hC132 G X T V L P M hX hSQ hT hprod hL hL2 hh hnin hTP hPM hMX
      hmax hPeq hred hVL hmod

theorem c137CaseS6_of_F4 (hC124 : ∀ (G : Type) [Group G] [Finite G], C124StatementSQTK (G := G))
    (hC132 : CFSG.Quasithin.ASInputs.AS_C_1_32_F4) : C137CaseS6_F4 := by
  intro G _ _ X T V L P M hX hSQ hT hprod hL hL2 htype hnin hnat hTP hPM hMX hmax hPeq hred hVL
  rcases htype with ha | hh
  · exact c137CaseS6A6_of_F4 hC124 hC132 G X T V L P M hX hSQ hT hprod hL hL2 ha hnin hnat hTP hPM
      hMX hmax (hPeq.resolve_right fun h' => not_hatA6_of_a6 ha h'.1) hred hVL
  · exact c137CaseS6Hat_of_F4 hC124 hC132 G X T V L P M hX hSQ hT hprod hL hL2 hh hnin hnat hTP hPM
      hMX hmax hPeq hred hVL

end CFSG.Quasithin.H13.U3.GC137
