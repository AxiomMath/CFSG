module

public import CFSG.GH74.GLS.Stage1.Thm6.Prod.M12Final

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Prod

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm6.M12Facts
  CFSG.GH74.GLS.Stage1.Thm6.Sec13 CFSG.GH74.GLS.Stage1.Thm6.Sec14 CFSG.GH74.GLS.Stage2.Local

@[expose] def Lemma14_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Stage12.Std G →
    ∀ (x : G) (T V S : Subgroup G) (a b y : G), Out13 G x T V S a b y →
      ∀ i j : Fin 4, ¬ (i.val % 2 = 0 ∧ j.val % 2 = 0) →
        IsConj (a ^ 2 * b ^ 2) (nu a b y x (i, j, 0, 1))

@[expose] def Lemma14_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Stage12.Std G →
    ∀ (x : G) (T V S : Subgroup G) (a b y : G), Out13 G x T V S a b y →
      ∀ u : G, orderOf u = 2 → ¬ IsConj (a ^ 2 * b ^ 2) u → M12NonCentral u

variable {G : Type} [Group G] [Finite G] {S T V : Subgroup G} {a b y x : G}

theorem stage2Ctx_m12_of_out13 (h91 : IVK_9_1) (h144 : Lemma14_4) (h145 : Lemma14_5)
    (hStd : Stage12.Std G) (h3 : pRank 2 G = 3) (o : Out13 G x T V S a b y) :
    Stage2Ctx G (a ^ 2 * b ^ 2) Stage12.Kind.m12 S := by
  have h := o.data
  obtain ⟨S', a', b', y', x', hb⟩ := exists_barImg h91 hStd.kps o
  refine ⟨hStd, isCentralInvolution_z o, ?_,
    Stage1Data.m12 (stage1M12_of_barImg o hb (h144 G hStd x T V S a b y o)), ⟨?_, ?_, ?_⟩, fun _ => h3⟩
  · exact (CFSG.ABGLocalTools.isSylowOf_iff).2 (sylow2In_centralizer_z h o.sylow)
  · intro s _ K hK
    exact (not_isPCompIn_of_solvable _ hb.solvable K hK).elim
  · intro _ u hu hnc
    exact h145 G hStd x T V S a b y o u hu hnc
  · intro ε _ _ _ _ hk
    cases hk

end CFSG.GH74.GLS.Stage1.Thm6.Prod
