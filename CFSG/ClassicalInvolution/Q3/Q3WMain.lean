module

public import CFSG.ClassicalInvolution.Q3.Q3WChain
public import CFSG.ClassicalInvolution.WeakCT.Amalgam

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

theorem weakCT3_recognition_of_pairs {n : ℕ} (hn : 3 ≤ n) {X : Type} [Group X]
    {U : Fin n → Subgroup X}
    (hcomm : ∀ i j : Fin n, (i : ℕ) + 1 < j → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j : Fin n, (j : ℕ) = i + 1 → ∃ W, LinearBlockStandardPair F3 W (U i) (U j))
    (hgen : ⨆ i, U i = ⊤) :
    ∃ ψ : SL(n + 1, F3) →* X, Function.Surjective ψ ∧
      ψ.ker ≤ Subgroup.center SL(n + 1, F3) ∧ CFSG.IsQuasisimple X ∧
      CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X)
        CFSG.Assembly.LowTwoRank.StatedLieTag.PSL (n + 1) 3 1 := by
  obtain ⟨F, hF⟩ := exists_ctFamily_of_pairs3 (by omega) hcomm hpair
  have hgen' : ⨆ i, (F.ι i).range = ⊤ := by
    simp only [fun i => (hF i).1]
    exact hgen
  have hnt : ∃ i, ∃ A, F.ι i A ≠ 1 := by
    refine ⟨⟨0, by omega⟩, xp 1, fun h => xp_one_ne_one ?_⟩
    exact (hF ⟨0, by omega⟩).2 (h.trans (map_one _).symm)
  obtain ⟨ψ, -, hsurj, hker, hqs, -, hmodel⟩ :=
    exists_recognition hn Nat.prime_three le_rfl (by simp) F hgen' hnt
  exact ⟨ψ, hsurj, hker, hqs, hmodel⟩

theorem weakCT3_recognition {n : ℕ} (hn : 3 ≤ n) {X : Type} [Group X]
    {U : Fin n → Subgroup X} {W : Fin n → Fin n → Subgroup X} (hW : WeakCTSystem F3 n U W) :
    ∃ ψ : SL(n + 1, F3) →* X, Function.Surjective ψ ∧
      ψ.ker ≤ Subgroup.center SL(n + 1, F3) ∧ CFSG.IsQuasisimple X ∧
      CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X)
        CFSG.Assembly.LowTwoRank.StatedLieTag.PSL (n + 1) 3 1 :=
  weakCT3_recognition_of_pairs hn hW.comm (fun i j hj => ⟨_, hW.pair i j hj⟩) hW.gen

end CFSG.ClassicalInvolution.Q3.Q3W
