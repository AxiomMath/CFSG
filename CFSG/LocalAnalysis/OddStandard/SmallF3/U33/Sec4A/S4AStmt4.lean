module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AStmt1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AStmt2B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AStmt3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AInputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL48A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL49B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL49D
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL410F

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem lemma4_8 (hc : Ctx4 t L S x₁ x₂ lam rho tau) : Lemma4_8Concl t x₁ x₂ rho tau :=
  have h43 : twoCore t = zpowers t := hc.l43
  have h44 : tau ^ 2 = 1 := hc.l44.1
  ⟨⟨fun hg => S4A.exists_adjust_of_conj hc.toCtx h43 h44 (Or.inl rfl) hg,
    fun ⟨g, _, hg, _⟩ => ⟨g, hg⟩⟩,
   ⟨fun hg => S4A.exists_adjust_of_conj hc.toCtx h43 h44 (Or.inr rfl) hg,
    fun ⟨g, _, hg, _⟩ => ⟨g, hg⟩⟩⟩

theorem lemma4_9 (hI : Sec4Inputs) (hG : Sec4Glob G) (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    Lemma4_9Concl t S x₁ x₂ tau := by
  have h43 : twoCore t = zpowers t := hc.l43
  have h44 : tau ^ 2 = 1 := hc.l44.1
  have h2 : 2 ∣ S.index := hc.l42
  have hS1 : ∀ 𝒮 : Sylow 2 G, S < (𝒮 : Subgroup G) →
      ctxS1 S (𝒮 : Subgroup G) ≤ ctxM t tau x₁ x₂ := by
    intro 𝒮 h𝒮
    obtain ⟨E, hE𝒮, hEn, hEe, hEc⟩ := hI.exists_normal_e8 hG hc.hyp 𝒮
    exact S4A.ctxS1_le_ctxM_of hc.toCtx h43 h44 h2 hG.dvd 𝒮 h𝒮 hE𝒮 hEn hEe hEc
  exact ⟨hS1, S4A.tM_cases_of hc.toCtx h43 h44 h2 hS1⟩

theorem lemma4_10 (hI : Sec4Inputs) (hG : Sec4Glob G) (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    Lemma4_10Concl t x₁ x₂ tau :=
  S4A.lemma4_10_of hc.toCtx hc.l43 hc.l44.1 hc.l42 hG.dvd
    (fun 𝒮 => hI.exists_normal_e8 hG hc.hyp 𝒮) (lemma4_9 hI hG hc)

theorem ctx10_of_ctx4 (hI : Sec4Inputs) (hG : Sec4Glob G) (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    Ctx10 t L S x₁ x₂ lam rho tau :=
  { toCtx4 := hc
    l45 := lemma4_5 hc
    l46 := lemma4_6 hc
    l47 := lemma4_7 hc
    l48 := lemma4_8 hc
    l49 := lemma4_9 hI hG hc
    l410 := lemma4_10 hI hG hc }

theorem lemma4_1_to_10 (h41 : Lemma4_1Stmt) (h41c : CtxOfLemma4_1Stmt) (h43 : Lemma4_3Stmt)
    (hI : Sec4Inputs) (hG : Sec4Glob G) (h0 : Ctx0 t L S x₁ x₂ lam rho) :
    ∃ tau : G, Ctx10 t L S x₁ x₂ lam rho tau := by
  obtain ⟨tau, hc⟩ := exists_ctx h41 h41c hI hG h0
  exact ⟨tau, ctx10_of_ctx4 hI hG (ctx4_of_ctx h43 hI hG hc)⟩

end CFSG.OddStandard.SmallF3.HarrisU33
