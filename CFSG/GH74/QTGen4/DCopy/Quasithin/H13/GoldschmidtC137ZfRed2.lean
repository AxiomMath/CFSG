module

public import CFSG.Quasithin.H13.GoldschmidtC137ZfRed2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtC137ZfStmt

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem c137CaseS6Z_of_M_F4
    (Mdl : ∀ {G : Type} [Group G] [Finite G] (U : Subgroup G), Subgroup G →
      IsElemAbelian 2 U → Prop)
    (hM : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (X T V L P M : Subgroup G),
      CharTwo X → SQTKGroup ↥X → IsSylowTwoOf T X → (∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) →
      L ∈ cComp X → CharTwo L →
      (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) ∨ A6.IsHatA6 L) →
      ¬ autOn T V ≤ autOn L V → T ≤ P → P ≤ M → M < X →
      (∀ H : Subgroup G, M ≤ H → H ≤ X → H = M ∨ H = X) →
      (P = M ∨ (A6.IsHatA6 L ∧ P.relIndex M = 3 ∧ ¬ oTwoUpper P ≤ A6.o2Z L)) →
      ∀ hred : IsTwoReducedIn X V, ⁅V, L⁆ ≠ ⊥ → Mdl V L hred.2.2.1 → Concl X T V L P)
    (hmodZ : ∀ {G : Type} [Group G] [Finite G] {V L U : Subgroup G}, IsElemAbelian 2 V →
      ∀ hU : IsElemAbelian 2 U, L ≤ normalizer (V : Set G) → L ≤ normalizer (U : Set G) →
      ⁅V, L⁆ = U → ⁅U, L⁆ = U →
      (∃ _ : IsMulCommutative ↥V, AlternatingNatural (V := ↥V) (autOn L V) ⊤
        ((centralizer (L : Set G)).subgroupOf V) 6) → Mdl U L hU) :
    C137CaseS6Z_F4 := by
  intro G _ _ X T V L P M hX hSQ hT hprod hL hL2 htype hnin hnat hTP hPM hMX hmax hPeq hred hVL
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hn : X ≤ normalizer (L : Set G) := C124.le_normalizer_of_prod hT hprod hL
  have hXN : X ≤ normalizer (V : Set G) := hred.2.1
  have hLN : L ≤ normalizer (V : Set G) := hLX.trans hXN
  have hPX : P ≤ X := hPM.trans hMX.le
  have hUV : ⁅V, L⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLN
  obtain ⟨hredU, hUU, hCeq⟩ := zf_reduce hred hT hprod hL htype hVL hnat
  have hninU : ¬ autOn T ⁅V, L⁆ ≤ autOn L ⁅V, L⁆ :=
    zf_not_autOn_le_of_centralizer_eq hXN hredU.2.1 hT.1 hLX hCeq hnin
  have hUL : ⁅⁅V, L⁆, L⁆ ≠ ⊥ := by rw [hUU]; exact hVL
  have hmod : Mdl ⁅V, L⁆ L hredU.2.2.1 :=
    hmodZ hred.2.2.1 hredU.2.2.1 hLN (hLX.trans hredU.2.1) rfl hUU hnat
  exact zf_concl_of_U hred hT hn hPX hCeq hredU.2.2.1 hUV hredU.2.1
    (hM G X T ⁅V, L⁆ L P M hX hSQ hT hprod hL hL2 htype hninU hTP hPM hMX hmax hPeq hredU hUL
      hmod)

end CFSG.Quasithin.H13.U3.GC137
