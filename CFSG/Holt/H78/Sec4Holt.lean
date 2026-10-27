module

public import CFSG.Holt.H78.Sec4Main
public import CFSG.Holt.H78.Sec4Prop46A
import CFSG.Holt.H78.Sec4Prop43
import CFSG.Holt.H78.Sec4Prop46
import CFSG.Holt.H78.Sec4Prop49S4e
import CFSG.Holt.H78.Sec4Prop49S5h
import CFSG.Holt.H78.Sec4Prop49S7b
import CFSG.Holt.H78.Sec4SEFacts
import CFSG.Holt.H78.Induction

public section

namespace CFSG.Holt.H78

@[expose] def HoltCaseAStepA7Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Fintype Ω] [DecidableEq Ω]
    [MulAction G Ω] [FaithfulSMul G Ω], Sec4Setting G Ω →
      ∀ (α : Ω) (v : G) (P : Subgroup (typeLSection G Ω v)),
        Prop46Setup G Ω α v P → CaseAStepA7 G Ω α v P

theorem holtSection4Statement_of_caseAStepA7
    (hD : HoltCaseAStepA7Statement) :
    HoltSection4Statement :=
  have hP43 : ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Fintype Ω] [DecidableEq Ω]
      [MulAction G Ω] [FaithfulSMul G Ω], Sec4Setting G Ω →
        ∀ {α β : Ω}, α ≠ β → IsEmpty (AltConfig G Ω α β) :=
    fun _ _ _ _ _ _ _ _ hS _ _ hαβ => hS.isEmpty_altConfig hαβ
  have hP46 : ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Fintype Ω] [DecidableEq Ω]
      [MulAction G Ω] [FaithfulSMul G Ω], Sec4Setting G Ω →
        ∀ {α : Ω} {v : G}, IsTypeL G Ω α v → CFSG.pPrimeCore 2 (typeLSection G Ω v) = ⊥ :=
    fun G _ _ Ω _ _ _ _ hS _ _ hv =>
      hS.pPrimeCore_typeLSection_eq_bot_of (fun _ _ hab => hS.isEmpty_altConfig hab)
        (hD G Ω hS) hv
  holtSection4Statement_of_section4Hyps hP43 hP46
    (fun G _ _ Ω _ _ _ _ hS =>
      hS.p49Step94_of (hP43 G Ω hS) (hP46 G Ω hS) seFieldFixBound seChainUnitary)
    (fun _ _ _ _ _ _ _ _ hS => hS.p49Step95)
    (fun _ _ _ _ _ _ _ _ hS => hS.p49Step97b)

theorem holtTheorem1_of_caseAStepA7
    (hD : HoltCaseAStepA7Statement) :
    HoltTheorem1 :=
  holtTheorem1_of_section4 (holtSection4Statement_of_caseAStepA7 hD)

end CFSG.Holt.H78
