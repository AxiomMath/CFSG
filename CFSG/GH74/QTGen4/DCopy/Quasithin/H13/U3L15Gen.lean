module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2
public import CFSG.Quasithin.H13.U3L15Core

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem core15_of_F4 [CFSG.GH74.QTGen4.Finite4 G] (h1332 : Stmt13_3_2_F4) {T L V V₂ X : Subgroup G} (hH : QTH13 G T L)
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V) (hzv : V ⊓ centralizer (L : Set G) = ⊥)
    (hV2 : A6.IsV2 T V V₂) (hq1 : ¬ pCoreOf 2 (A6.g1 T V) ≤ centralizer (V₂ : Set G))
    (hXL : X ≤ L) (hXN : X ≤ normalizer (V₂ : Set G)) (hXT : T ≤ normalizer (X : Set G))
    (hXres : oTwoRes X = X) (hXact : ∃ x ∈ X, x ^ 3 = 1 ∧ x ∉ centralizer (V₂ : Set G))
    (hXker : IsPGroup 2 ↥(X ⊓ centralizer (V₂ : Set G))) (hXZ : ¬ X ≤ A6.o2Z L)
    (hgen : ∀ V₃ : Subgroup G, V₂ ≤ V₃ → V₃ ≤ V → T ≤ normalizer (V₃ : Set G) →
      Nat.card V₃ = 8 → autOn (X ⊔ L ⊓ normalizer (V₃ : Set G)) V = autOn L V) :
    Core15 G T L V V₂ X := by
  obtain ⟨-, ⟨hTL, -⟩, ⟨-, hVall⟩, -⟩ := h1332 G T L hH L hH.faithful
  obtain ⟨-, hTV, hfsu, -, -⟩ := hVall V hV
  exact ⟨hH, hV, hzv, hV2, hTL, hTV, hfsu.quasisimple, hq1, hXL, hXN, hXT, hXres, hXact, hXker,
    hXZ, hgen⟩

end CFSG.Quasithin.H13.U3
