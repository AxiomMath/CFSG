module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.LieCross

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] def IsG2EightIndex : TauCeti.LieTypeIndex → Prop
  | .G2 q => IsTwoPow q 3
  | _ => False

@[expose] def Bal207Corr : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (p : ℕ) (K B : Subgroup X),
    p.Prime → p ≠ 2 → CFSG.Open.IsComponentOf K ⊤ → IsSCp p ⊤ B →
      B ≤ Subgroup.normalizer (K : Set X) → ∀ d : TauCeti.ValidLieTypeIndex, Bal207Index p d.1 →
        Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie d).Group) →
        (IsG2EightIndex d.1 → CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (K : Set X)) + 3 ≤
          CFSG.Open.pRank p B) →
        IsStronglyBalancedIn p B K

theorem Bal207Corr.of_index (h : Bal207Corr) {X : Type} [Group X] [Finite X]
    (hX : CFSG.Open.IsKGroup X) {p : ℕ} {K B : Subgroup X} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : CFSG.Open.IsComponentOf K ⊤) (hB : IsSCp p ⊤ B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) {P : TauCeti.LieTypeIndex → Prop}
    (hP : ∀ d, P d → Bal207Index p d ∧ ¬ IsG2EightIndex d) (hL : IsLieQuot ↥K P) :
    IsStronglyBalancedIn p B K := by
  obtain ⟨d, hd, he⟩ := hL
  exact h X hX p K B hp hp2 hK hB hBN d (hP _ hd).1 he fun hg => ((hP _ hd).2 hg).elim

theorem not_isG2EightIndex_of_d2Exc {p : ℕ} {d : TauCeti.LieTypeIndex}
    (h : CFSG.AGLEmbeddingD2.IsD2SeitzException p d) : ¬ IsG2EightIndex d := by
  rcases h with ⟨-, ⟨q, -, -, rfl⟩ | ⟨q, -, -, rfl⟩ | ⟨q, -, -, rfl⟩ | ⟨q, -, -, rfl | rfl⟩ | rfl⟩ |
    ⟨-, rfl | rfl⟩ <;> exact fun h => h

end CFSG.HardMathSupport.Dickson.Bal207

end
