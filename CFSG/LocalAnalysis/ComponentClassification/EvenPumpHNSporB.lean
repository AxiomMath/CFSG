module

public import CFSG.LocalAnalysis.ComponentClassification.BMCaseOddCoreB
public import CFSG.Monster.B.CTIB.ComponentsSeventeen
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpHNComps
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafSpor

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf

theorem not_isHNType_of_properFixedComponent_B
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* NativeSporadic.Carrier .B) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) : ¬ IsHNType (P ⧸ Open.fusionZStar P) :=
  not_isHNType_of_comps hna
    (fun σ hσ => oddCore_fixedSubgroup_eq_bot_of_mulAut hna
      (mulAut_oddCore_eq_bot_of_sporadicOddCoreFree BMCase.sporadicOddCoreFree_B hna e) hσ)
    (fun t ht K hK => by
      obtain ⟨-, hiso, -⟩ :=
        Monster.B.CTIB.involution_local_components_simple_quotient_divisible_by_seventeen ⟨e⟩ t ht
          K hK
      rcases hiso with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
      · show Nat.card _ ≠ _
        rw [Nat.card_congr φ.toEquiv, LieType.Chevalley.C2E6Std.card_stdGroup]
        decide
      · obtain ⟨ψ⟩ := Monster.B.E6.StdF4Radical.nonempty_groupJ_mulEquiv_F4
        show Nat.card _ ≠ _
        rw [Nat.card_congr φ.toEquiv, ← Nat.card_congr ψ.toEquiv,
          Monster.B.E6.FieldInvF4.card_groupJ]
        decide)
    (fun α _ hα => outer_compNotHN_of_forall_inner (s := .B)
      (BMCase.inner_of_mulEquiv_pinnedB NativeSporadic.B ⟨MulEquiv.refl NativeSporadic.B⟩) e α hα)
    h

end CFSG.ComponentClassification.EvenPump
