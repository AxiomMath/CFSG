module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightInduction

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3.FourEight

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers
open scoped MatrixGroups Pointwise

variable {X : Type} [Group X] [Finite X]

structure ElemCtx (G T S Q H : Subgroup X) (g y : X) : Prop where
  elem : Elem47 G T S Q H g y
  index_le : T.relIndex (S ⊓ H) ≤ Nat.card T
  oddCore_eq_bot : CFSG.oddCore G = ⊥
  ih : Theorem48Below (Nat.card (G ⊔ T : Subgroup X))
  not_normal : ¬ G ≤ Subgroup.normalizer (relativeWeakClosure G T S : Set X)

namespace ElemCtx

variable {G T S Q H : Subgroup X} {g y : X}

theorem sylowFrame (c : ElemCtx G T S Q H g y) : SylowFrame G T S := c.elem.hyp45.sylowFrame

theorem hyp43 (c : ElemCtx G T S Q H g y) : Hyp43 G T Q H := c.elem.hyp45.hyp43

theorem frame (c : ElemCtx G T S Q H g y) : Frame G T := c.sylowFrame.toFrame

theorem pRank_lt (c : ElemCtx G T S Q H g y) : 1 < pRank 2 T := c.elem.pRank_lt

theorem weakClosure_eq (c : ElemCtx G T S Q H g y) :
    relativeWeakClosure G T S = rightConjugate T y ⊔ (T ⊔ rightConjugate T g) :=
  c.elem.weakClosure_eq

theorem not_le_pCoreOf (c : ElemCtx G T S Q H g y) : ¬ T ≤ pCoreOf 2 (G ⊔ T) :=
  fun hT => c.not_normal (le_normalizer_of_le_pCoreOf c.sylowFrame hT)

theorem not_isMulCommutative (c : ElemCtx G T S Q H g y) :
    ¬ IsMulCommutative (relativeWeakClosure G T S) := by
  intro hab
  have hbot : ⁅relativeWeakClosure G T S, relativeWeakClosure G T S⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr hab)
  rw [c.weakClosure_eq, c.elem.commutator_eq] at hbot
  exact c.elem.hyp45.W_inf_G_ne_bot hbot

theorem not_isMulCommutative_of_le (c : ElemCtx G T S Q H g y) {S₁ : Subgroup X}
    (hW : relativeWeakClosure G T S ≤ S₁) : ¬ IsMulCommutative S₁ :=
  fun hab => c.not_isMulCommutative (isMulCommutative_of_le hW hab)

theorem commutator_eq (c : ElemCtx G T S Q H g y) : ⁅T, G⁆ = G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hF := c.frame
  have h := c.sylowFrame
  set L := ⁅T, G⁆ with hLdef
  have hLG : L ≤ G := by
    rw [hLdef, Subgroup.commutator_comm]
    exact hF.commutator_le
  have hLN : G ⊔ T ≤ Subgroup.normalizer (L : Set X) := sup_le_normalizer_commutator hF
  have hK : conjugateClosure G T = L ⊔ T := by rw [conjugateClosure_eq, sup_comm]
  have hKN : G ⊔ T ≤ Subgroup.normalizer ((L ⊔ T : Subgroup X) : Set X) :=
    hK ▸ sup_le_normalizer_conjugateClosure hF
  have hWK : relativeWeakClosure G T S ≤ L ⊔ T := by
    rw [relativeWeakClosure_le_iff]
    intro x hx _
    rw [← hK]
    unfold conjugateClosure
    exact le_iSup (fun c : G => rightConjugate T c) ⟨x, hx⟩
  have hWS : relativeWeakClosure G T S ≤ S ⊓ (L ⊔ T) :=
    le_inf (relative_weak_closure_le _ _ _) hWK
  rcases conclusion_of_normal c.ih h c.hyp43 c.index_le c.oddCore_eq_bot c.pRank_lt hLG hLN
      hne with hN | hpsl
  ·
    set W₁ := relativeWeakClosure L T (S ⊓ (L ⊔ T)) with hW₁def
    have hTW₁ : T ≤ W₁ := subgroup_le_relative_weak_closure _ _ _ (le_inf h.le le_sup_right)
    have hW₁S : W₁ ≤ S ⊓ (L ⊔ T) := relative_weak_closure_le _ _ _
    have hW₁N : L ⊔ T ≤ Subgroup.normalizer (W₁ : Set X) :=
      sup_le hN (hTW₁.trans Subgroup.le_normalizer)
    have hle := le_pCoreOf_of_normal (sup_le (hLG.trans le_sup_left) le_sup_right) hKN
      (hW₁S.trans inf_le_right) hW₁N (h.sylow.isPGroup.to_le (hW₁S.trans inf_le_left))
    exact c.not_le_pCoreOf (hTW₁.trans hle)
  · exact c.not_isMulCommutative_of_le hWS
      (isMulCommutative_of_psl_case (h.restrict hLG hLN).toFrame (h.restrict hLG hLN).sylow hpsl)

end ElemCtx

end CFSG.ComponentClassification.AschbacherTheorem3.FourEight
