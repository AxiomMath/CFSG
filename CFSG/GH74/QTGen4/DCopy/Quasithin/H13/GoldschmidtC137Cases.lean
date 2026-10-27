module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtC137Stmt
public import CFSG.Quasithin.H13.GoldschmidtC137Inner

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

@[expose] def C137CaseL32_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (X T V L P M : Subgroup G),
    CharTwo X → SQTKGroup ↥X → IsSylowTwoOf T X → (∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) →
    L ∈ cComp X → CharTwo L → LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 →
    T ≤ P → P ≤ M → M < X → (∀ H : Subgroup G, M ≤ H → H ≤ X → H = M ∨ H = X) → P = M →
    IsTwoReducedIn X V → ⁅V, L⁆ ≠ ⊥ → Nat.card ↥⁅V, L⁆ = 8 →
    (∃ u ∈ ⁅V, L⁆, u ≠ 1 ∧ P = X ⊓ centralizer ({u} : Set G)) → Concl X T V L P

@[expose] def C137CaseU33_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (X T V L P M : Subgroup G),
    CharTwo X → SQTKGroup ↥X → IsSylowTwoOf T X → (∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) →
    L ∈ cComp X → CharTwo L → LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 →
    T ≤ P → P ≤ M → M < X → (∀ H : Subgroup G, M ≤ H → H ≤ X → H = M ∨ H = X) → P = M →
    IsTwoReducedIn X V → ⁅V, L⁆ ≠ ⊥ → Concl X T V L P

@[expose] def C137CaseS6_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (X T V L P M : Subgroup G),
    CharTwo X → SQTKGroup ↥X → IsSylowTwoOf T X → (∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) →
    L ∈ cComp X → CharTwo L →
    (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) ∨ A6.IsHatA6 L) →
    ¬ autOn T V ≤ autOn L V → (∃ _ : IsMulCommutative ↥V,
      AlternatingNatural (V := ↥V) (autOn L V) ⊤ ⊥ 6) →
    T ≤ P → P ≤ M → M < X → (∀ H : Subgroup G, M ≤ H → H ≤ X → H = M ∨ H = X) →
    (P = M ∨ (A6.IsHatA6 L ∧ P.relIndex M = 3 ∧ ¬ oTwoUpper P ≤ A6.o2Z L)) →
    IsTwoReducedIn X V → ⁅V, L⁆ ≠ ⊥ → Concl X T V L P

theorem c137StatementFiveSQTK_of_cases_F4
    (hC124 : ∀ (G : Type) [Group G] [Finite G], C124StatementSQTK (G := G))
    (hL32 : C137CaseL32_F4) (hU33 : C137CaseU33_F4) (hS6 : C137CaseS6_F4) : C137StatementFiveSQTK_F4 := by
  intro G _ _ X T V L P M hX hSQ hT hprod hL hL2 htype hdyn hTP hPM hMX hmax hPeq hred hVL hLie
  have hPX : P ≤ X := hPM.trans hMX.le
  rcases htype with hl | ha | hh | hu
  · have hP : P = M := hPeq.resolve_right fun h => not_hatA6_of_psl32 hl h.1
    obtain ⟨h8, hu⟩ := hLie hl
    exact hL32 G X T V L P M hX hSQ hT hprod hL hL2 hl hTP hPM hMX hmax hP hred hVL h8 hu
  · by_cases hin : autOn T V ≤ autOn L V
    · exact concl_of_c124_inner (hC124 G) hX hSQ hT hprod hL hL2 (Or.inl ha) hin hTP hPX hred hVL
    · have hnat := (hdyn.resolve_left (not_psu33_of_a6 ha)).resolve_left hin
      exact hS6 G X T V L P M hX hSQ hT hprod hL hL2 (Or.inl ha) hin hnat hTP hPM hMX hmax hPeq
        hred hVL
  · by_cases hin : autOn T V ≤ autOn L V
    · exact concl_of_c124_inner (hC124 G) hX hSQ hT hprod hL hL2 (Or.inr hh) hin hTP hPX hred hVL
    · have hnat := (hdyn.resolve_left (not_psu33_of_hatA6 hh)).resolve_left hin
      exact hS6 G X T V L P M hX hSQ hT hprod hL hL2 (Or.inr hh) hin hnat hTP hPM hMX hmax hPeq
        hred hVL
  · have hP : P = M := hPeq.resolve_right fun h => not_hatA6_of_psu33 hu h.1
    exact hU33 G X T V L P M hX hSQ hT hprod hL hL2 hu hTP hPM hMX hmax hP hred hVL

end CFSG.Quasithin.H13.U3.GC137
