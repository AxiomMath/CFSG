module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3C137

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

@[expose] def C137StatementFive_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (X T V L P M : Subgroup G),
    CharTwo X → IsSylowTwoOf T X → (∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) →
    L ∈ cComp X → CharTwo L →
    (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 ∨
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) ∨ A6.IsHatA6 L ∨
      LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) →
    (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 ∨ autOn T V ≤ autOn L V ∨
      ∃ _ : IsMulCommutative ↥V, AlternatingNatural (V := ↥V) (autOn L V) ⊤ ⊥ 6) →
    T ≤ P → P ≤ M → M < X → (∀ H : Subgroup G, M ≤ H → H ≤ X → H = M ∨ H = X) →
    (P = M ∨ (A6.IsHatA6 L ∧ P.relIndex M = 3 ∧ ¬ oTwoUpper P ≤ A6.o2Z L)) →
    IsTwoReducedIn X V → ⁅V, L⁆ ≠ ⊥ →
    (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 →
      Nat.card ↥⁅V, L⁆ = 8 ∧ ∃ u ∈ ⁅V, L⁆, u ≠ 1 ∧ P = X ⊓ centralizer ({u} : Set G)) →
    CharNormal (baum (pCoreOf 2 P)) X ∨
      ((LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 → IsLnBlock L 3) ∧
        (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) → H13.IsA6Block L) ∧
        (A6.IsHatA6 L → H13.IsHatA6Block L) ∧
        (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 → H13.IsG2Block L)) ∨
      (Nat.card ↥(autOn X V) = 12096 ∧ ∃ l : Subgroup G, V ⊓ centralizer (L : Set G) ≤ l ∧
        l ≤ V ∧ Nat.card ↥l = 4 * Nat.card ↥(V ⊓ centralizer (L : Set G)) ∧
        P ≤ normalizer (l : Set G)) ∨
      ((Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) ∨ A6.IsHatA6 L) ∧
        (∃ l : Subgroup G, V ⊓ centralizer (L : Set G) ≤ l ∧ l ≤ V ∧
          Nat.card ↥l = 4 * Nat.card ↥(V ⊓ centralizer (L : Set G)) ∧
          P ≤ normalizer (l : Set G)) ∧
        (A6.IsHatA6 L → ¬ oTwoUpper (A6.o2Z L) ≤ P) ∧
        ∃ A : Subgroup G, IsMaxElemAbelian T A ∧ 2 < Nat.card ↥(autOn A V))

theorem c137Statement_of_five_F4 (h : C137StatementFive_F4) : C137Statement_F4 := by
  intro G _ _ X T V L P M hX hT hXLT hL hL2 htype hdyn hTP hPM hMX hmax hPeq hred hVL hL32
  rcases h G X T V L P M hX hT hXLT hL hL2 htype (hdyn.elim Or.inl fun h' => Or.inr (Or.inl h'))
      hTP hPM hMX hmax hPeq hred hVL hL32 with h1 | h2 | h4 | h5
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h4))
  · exact Or.inr (Or.inr (Or.inr h5.1))

end CFSG.Quasithin.H13.U3
