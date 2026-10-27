module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineTwelveOneSigmaStrongDefs
public import CFSG.LieType.SteinbergBRMulEquivCores

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.LocalAnalysis.RankThreeUC

@[expose] def NineTwelveOneSigmaThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q H F : Subgroup G),
    O1217.Setting1417 G M Q H F 3 →
    ∀ L : Subgroup G, AGL81C.IsPComponentIn 3 L H → ¬ L ≤ M →
      AGL81C.IsTwoPrimeComponentIn L H ∨
        Nonempty (↥L ⧸ CFSG.solvableRadical ↥L ≃* alternatingGroup (Fin 6))

theorem O1217.Setting1417.nineTwelveOne (h2 : NineTwelveOneSigmaStrong)
    (h3 : NineTwelveOneSigmaThree) {G : Type} [Group G] [Finite G] {M Q H F : Subgroup G}
    {q : ℕ} (s : O1217.Setting1417 G M Q H F q) {L : Subgroup G}
    (hL : AGL81C.IsPComponentIn q L H) (hLM : ¬ L ≤ M) :
    AGL81C.IsTwoPrimeComponentIn L H ∨
      (q = 3 ∧ Nonempty (↥L ⧸ CFSG.solvableRadical ↥L ≃* alternatingGroup (Fin 6))) := by
  by_cases hq3 : q = 3
  · subst hq3
    rcases h3 G M Q H F s L hL hLM with h | h
    · exact Or.inl h
    · exact Or.inr ⟨rfl, h⟩
  · exact Or.inl (h2 G M Q H F q s hq3 L hL hLM)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
