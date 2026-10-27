module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.LowDimSection.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

@[expose] noncomputable def normalizerQuotCenterHom {X : Type*} [Group X] (C : Subgroup X) :
    ↥(Subgroup.normalizer (C : Set X)) →* MulAut (↥C ⧸ Subgroup.center ↥C) :=
  (FiveTransitive.CharacteristicAutomorphism.quotient (Subgroup.center ↥C)).comp
    C.normalizerMonoidHom

@[expose] def KFactLowDimPPrimeGen : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (p : ℕ), p.Prime → q ≠ 2 → p ≠ 2 → q ≠ p →
    ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], ¬ IsMulCommutative S →
    IsLowDimSimpleSection q S →
    ∀ E : Subgroup (MulAut S), CFSG.Open.IsElemAbelian p E → Nat.card E = p ^ 2 →
    ¬ (p = 3 ∧ Nonempty (S ≃* alternatingGroup (Fin 6))) →
    Subgroup.closure {x : S | ¬ p ∣ orderOf x ∧ ∃ α ∈ E, α ≠ 1 ∧ α x = x} = ⊤

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
