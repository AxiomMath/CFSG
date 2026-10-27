module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9Statements

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Sec9NoE1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G)
    (t₀ : G) (E1 : Subgroup G), Sec9E1 G t L S z g B t₀ E1 → False

theorem asc82Sec9_false (h91 : Asc82Lemma91) (hF : Asc82Fink9E1) (hN : Asc82Sec9NoE1) :
    ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G)
      (t₀ : G), Sec9Ctx G t L S z g B t₀ → False := by
  intro G _ _ t L S z g B t₀ hctx
  obtain ⟨B', t₀', hch⟩ := h91 G t L S z g B t₀ hctx
  obtain ⟨E1, hE1⟩ := hF G t L S z g B' t₀' hch
  exact hN G t L S z g B' t₀' E1 hE1

end CFSG.OddStandard.SmallF3.Omega
