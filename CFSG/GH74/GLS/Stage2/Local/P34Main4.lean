module

public import CFSG.GH74.GLS.Stage2.Local.P34Step3
public import CFSG.GH74.GLS.Stage2.Local.P34S5W2
public import CFSG.GH74.GLS.Stage2.Local.P34S6
public import CFSG.GH74.GLS.Stage2.Local.P34Sp4Odd
public import CFSG.GH74.GLS.Stage2.Local.P34NS12Main

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.IVK.Proofs2

theorem leaf_prop34_final''
    {Ctx : ∀ (G : Type) [Group G] [Finite G], G → Kind → Subgroup G → Prop}
    (hto : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G),
      Stage2Ctx G z k S → Ctx G z k S)
    (h93 : IVK93) (hm12 : Prop34M12)
    (hOne : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
      ∀ H : Subgroup G, H ≠ ⊤ → Cen z ≤ H → C0 z k S H → barIn H (LC z) ≤ generalizedFitting (HBar H) →
        ¬ (∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v))
    (hSch : GHSchreier) (hrank : RankThree) (h27 : Leaf_Prop27W Ctx)
    (hK : Ivk93KindM12) (hM : P34NS.M12Facts) :
    Leaf_Prop34 := by
  intro G _ _ z k S hctx H hCH hne
  by_cases hV : pCore 2 (HBar H) = ⊥
  · have h2 := hasTwoInvolutionClasses hctx hne hCH
    obtain ⟨hs, hnab, hPerf⟩ := step23_of hSch hrank G z k S hctx H hne hCH hV h2
    rcases h93 G z k S hctx H hne hCH hV hs hnab hPerf h2 with hC0 | hFUS
    · obtain ⟨hcoatom, hLle, hFm⟩ := step6_of sp4Facts G z k S hctx H hne hCH hPerf hC0
      have hC0' := hC0
      obtain ⟨ε, q, L₁, L₂, hk, hL4, hq3, hpsp, hnS, hO2⟩ := hC0
      have hq4 : q % 4 = (if ε then 3 else 1) := by
        rcases hL4.fusion with ⟨-, hone⟩ | ⟨h2', -⟩
        · exact (hOne G z k S hctx H hne hCH hC0' hLle hone).elim
        · exact h2'
      exact Or.inr (Or.inr ⟨ε, q, L₁, L₂, hk, hL4, hq4, hq3, hpsp, hcoatom, hLle, hnS, hO2, hFm⟩)
    · exact (step5H_of_w hto h27 hSch (nsm12H_of hK hM) G z k S hctx H hne hCH hV hs hnab hPerf h2
        hFUS).elim
  · refine Or.inl ?_
    by_cases hk : k = Kind.m12
    · subst hk
      exact hm12 G z S hctx H hne hCH hV
    · exact stepOne hctx hk hCH hV

end CFSG.GH74.GLS.Stage2.Local.P34
