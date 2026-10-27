module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Quasithin CFSG.Blueprint CFSG.QuasithinUnique.Setup.Family

@[expose] def M22TightProp : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
    ∀ L E : Subgroup (MulAut W), CFSG.IsQuasisimple ↥L → IsIrrOn L →
      Nonempty (CQ L ≃* NativeSporadic.Carrier .M22) →
      E ≤ Subgroup.normalizer (L : Set (MulAut W)) → E ≠ ⊥ → IsElemAbelian2 E → IsQuadratic E →
      ¬ E ≤ L → Nat.card E = 2 ^ 5 → (fixV E).index = 2 ^ 5 → False

@[expose] def M24TightProp : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
    ∀ L E : Subgroup (MulAut W), CFSG.IsQuasisimple ↥L → IsIrrOn L →
      Nonempty (CQ L ≃* NativeSporadic.Carrier .M24) →
      E ≤ Subgroup.normalizer (L : Set (MulAut W)) → E ≠ ⊥ → IsElemAbelian2 E → IsQuadratic E →
      Nat.card E = 2 ^ 6 → (fixV E).index = 2 ^ 6 → False

theorem sporadicExclusion_M22_of
    (h : M22TightProp) : SporadicExclusion .M22 := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hE hEne hEel hquad
  rcases m22_weight_lt_or_tight hW hq hirr e hE hEne hEel with h1 | ⟨h1, h2, h3⟩
  · exact h1
  · exact (h W hW L E hq hirr ⟨e⟩ hE hEne hEel hquad h1 h2 h3).elim

theorem sporadicExclusion_M24_of
    (h : M24TightProp) : SporadicExclusion .M24 := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hE hEne hEel hquad
  rcases m24_weight_lt_or_tight hW hq hirr e hE hEne hEel with h1 | ⟨h2, h3⟩
  · exact h1
  · exact (h W hW L E hq hirr ⟨e⟩ hE hEne hEel hquad h2 h3).elim

end CFSG.QuasithinUnique.Setup.X1
