module

public import CFSG.LocalAnalysis.AGLEmbedding.Statements
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

structure D2Global (G : Type) [Group G] [Finite G] : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  kProper : IsKProper G
  charTwo : IsCharTwoType G
  rank : 4 ≤ evenRank G
  deltaOne : GLBDeltaOne G
  deltaTwo : GLBDeltaTwo G

@[expose] def D1For (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ GLBBetaFour G, ∀ (P : Sylow p G) (M : Subgroup G), GLBIsMaxTwoLocal M →
    GLBWeakCore p (P : Subgroup G) ≤ M → ∀ H : Subgroup G, IsTwoLocal H →
      3 ≤ pRank p (H ⊓ M) → H ≤ M

variable {G : Type} [Group G] [Finite G]

theorem D2Global.preuniqueness (h : D2Global G) : GLBPreuniqueness G := by
  intro q hq
  refine (weakCoreLocal_iff_of_betaFour hq).mpr fun P => ?_
  obtain ⟨H, hH, hcore⟩ := h.deltaOne q hq P
  exact ⟨H, hH, (weakCore_le_fullCore q (P : Subgroup G)).trans hcore⟩

theorem D2Global.toD1Global (h : D2Global G) : CFSG.AGLEmbedding.D1Global G :=
  ⟨h.simple, h.nonab, h.kProper, h.charTwo, h.rank, h.preuniqueness⟩

section Cores

variable {G : Type*} [Group G] [Finite G]

theorem glbCore_mono (p k : ℕ) {P R : Subgroup G} (hPR : P ≤ R) :
    GLBCore p k P ≤ GLBCore p k R :=
  (fullCore_le_iff p k P _).mpr fun Q hQP hrank => le_sSup ⟨Q, hQP.trans hPR, hrank, rfl⟩

theorem glbCore_anti (p : ℕ) {k l : ℕ} (hkl : k ≤ l) (P : Subgroup G) :
    GLBCore p l P ≤ GLBCore p k P :=
  (fullCore_le_iff p l P _).mpr fun Q hQP hrank => le_sSup ⟨Q, hQP, hkl.trans hrank, rfl⟩

theorem normalizer_le_glbCore (p k : ℕ) {P Q : Subgroup G} (hQP : Q ≤ P) (hrank : k ≤ pRank p Q) :
    Subgroup.normalizer (Q : Set G) ≤ GLBCore p k P :=
  le_sSup ⟨Q, hQP, hrank, rfl⟩

end Cores

end CFSG.AGLEmbeddingD2
