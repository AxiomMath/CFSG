module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291N1Y
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.CensusRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291

open CFSG CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt)

@[expose] def UniE9 : Prop :=
  ∀ (n q : ℕ) (K : Type) [Field K] [Finite K], Nat.card K = q ^ 2 → 4 ≤ n →
    2 ≤ Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU n q K)))

theorem ne_zero_of_not_comm {S : Type} [Group S] (n : ℕ) {K : Type} [Field K]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
    (e : S ≃* StatedProj H) (hS : ∃ a b : S, a * b ≠ b * a) : n ≠ 0 := by
  rintro rfl
  obtain ⟨a, b, hab⟩ := hS
  apply hab
  have : Subsingleton (StatedProj H) := by
    have : Subsingleton (Matrix.GeneralLinearGroup (Fin 0) K) := by
      haveI : Subsingleton (Matrix (Fin 0) (Fin 0) K) := inferInstance
      infer_instance
    haveI : Subsingleton ↥H := inferInstance
    infer_instance
  exact e.injective (Subsingleton.elim _ _)

theorem linUniE9_of_uniE9 (hU : UniE9) {p : ℕ} (hp5 : 5 ≤ p) : LinUniE9 p := by
  intro S _ _ h hS
  rcases h with ⟨n, K, _, _, hpn, -, ⟨e⟩⟩ | ⟨n, q, K, _, _, hK, hpn, -, ⟨e⟩⟩
  · have hn0 := ne_zero_of_not_comm n _ e hS
    have hn : 4 ≤ n := by
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn
      omega
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    exact CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.psl_two_le_pRank_three hn
  · have hn0 := ne_zero_of_not_comm n _ e hS
    have hn : 4 ≤ n := by
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn
      omega
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    exact hU n q K hK hn

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291
