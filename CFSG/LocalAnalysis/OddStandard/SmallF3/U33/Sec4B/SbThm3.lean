module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AStmt2C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbThm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbX17b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbX18b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbS18f

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

@[expose] def Lemma418CaseAStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}
    (hG : Sec4Glob G) (hc : Ctx18 t L S x₁ x₂ lam rho tau om 𝒮)
    (hcard : Nat.card (ctxCY t tau x₁ x₂ rho) = 2 ^ 8), False

theorem lemma4_18_of_caseA (hA : Lemma418CaseAStmt) : Lemma4_18Stmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau om hG hc 𝒮 h𝒮 hU hK
  have hc18 : Ctx18 t L S x₁ x₂ lam rho tau om 𝒮 := ⟨⟨hc, h𝒮, hU⟩, hK⟩
  rcases S4B.l18_card_C hc18 with h8 | h10
  · exact (hA hG hc18 h8).elim
  · exact (S4B.l18_false_caseB hG ⟨hc18, h10⟩).elim


theorem harris1981_bound_reduced18 (h41 : Lemma4_1Stmt) (h41c : CtxOfLemma4_1Stmt)
    (h411 : Lemma4_11Stmt) (h411c : Ctx11OfTMStmt) (h412 : Lemma4_12Stmt)
    (h413 : Lemma4_13Stmt) (h413c : Ctx13ExistsStmt) (h418A : Lemma418CaseAStmt)
    (hI : Sec4Inputs) (hB : Sec4BInputs) : FritzII.Harris1981Bound :=
  harris1981_bound h41 h41c lemma4_3_holds h411 h411c h412 h413 h413c lemma4_17
      (lemma4_18_of_caseA h418A) hI hB

end CFSG.OddStandard.SmallF3.HarrisU33
