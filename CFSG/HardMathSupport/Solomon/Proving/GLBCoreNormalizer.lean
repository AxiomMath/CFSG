module

public import CFSG.Open.GeneratedCore

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_glbCore {p k : ℕ} {P Q : Subgroup G} (hQP : Q ≤ P) (hk : k ≤ pRank p Q) :
    Subgroup.normalizer (Q : Set G) ≤ GLBCore p k P :=
  le_sSup ⟨Q, hQP, hk, rfl⟩

theorem GLBCore_mono {p k : ℕ} {P P' : Subgroup G} (hPP' : P ≤ P') :
    GLBCore p k P ≤ GLBCore p k P' := by
  unfold GLBCore
  apply sSup_le_sSup
  rintro N ⟨Q, hQP, hk, hN⟩
  exact ⟨Q, hQP.trans hPP', hk, hN⟩

theorem GLBCore_le_of_forall {p k : ℕ} {P M : Subgroup G}
    (h : ∀ Q : Subgroup G, Q ≤ P → k ≤ pRank p Q → Subgroup.normalizer (Q : Set G) ≤ M) :
    GLBCore p k P ≤ M := by
  unfold GLBCore
  refine sSup_le ?_
  rintro N ⟨Q, hQP, hk, rfl⟩
  exact h Q hQP hk

end CFSG.HardMathSupport.Solomon.Proving
