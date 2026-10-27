module

public import CFSG.Quasithin.H13.A7EscapeLocal
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Statements

public section

namespace CFSG.Quasithin.H13.A7

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Blueprint

variable {G : Type} [Group G]

theorem A7_escape_oTwoUpper_local_F4 (h1227 : Stmt12_2_7_F4) [CFSG.GH74.QTGen4.Finite4 G] (T : Sylow 2 G)
    {L V H : Subgroup G} (hyp : Hyp1223 G T L V)
    (hCZ : centralizer (quasithinOmegaOneCenter (T : Subgroup G) : Set G) ≤
      normalizer (L : Set G))
    (hH : IsHStar (T : Subgroup G) (normalizer (L : Set G)) H) (hHs : ¬ Group.IsSolvable H)
    (hsolv : ∀ X : Subgroup G, (T : Subgroup G) ≤ X → Group.IsSolvable X →
      X ≤ normalizer (L : Set G)) :
    LieModel (↥(oTwoUpper H) ⧸ CFSG.pCore 2 ↥(oTwoUpper H)) .PSL 2 2 2 ∧
      quasithinIsMaximalLocal (T : Subgroup G) (oTwoUpper H) ∧
      quasithinIsFaithfulLocal (T : Subgroup G) (oTwoUpper H) ∧
      IsA5ModuleSum (oTwoUpper H) ⁅VZ (T : Subgroup G) H, oTwoUpper H⁆ ∧
      IsPrimeReduced 2 ((VZ (T : Subgroup G) H).subgroupOf H) ∧
      (T : Subgroup G) ⊓ centralizer (VZ (T : Subgroup G) H : Set G) = pCoreOf 2 H := by
  obtain ⟨⟨hred, hCT, -, -⟩, h2⟩ := h1227 G T L V H hyp hCZ hH
  obtain ⟨hLie, Y, hKY, hYmax, hYf, hcase⟩ := h2 hHs
  rcases hcase with ⟨hYK, hA5⟩ | ⟨hA7, -, hTY, -⟩
  · rw [hYK] at hYmax hYf
    exact ⟨hLie, hYmax, hYf, hA5, hred, hCT⟩
  · exfalso
    have hYM : Y ≤ normalizer (L : Set G) :=
      le_of_alternating_seven_central_quotient T hTY hA7 hsolv
    apply hH.2.1
    rw [← eq_oTwoUpper_sup_sylow T hH.1.1]
    exact sup_le (hKY.trans hYM) hyp.normalizes

end CFSG.Quasithin.H13.A7
