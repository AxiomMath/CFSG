module

public import CFSG.ClassicalInvolution.WeakCT.Coherent
public import CFSG.ClassicalInvolution.WeakCT.Amalgam

public section

namespace CFSG.ClassicalInvolution.WeakCT

open scoped MatrixGroups

theorem weakCT_recognition_of_pairs (K : Type) [Field K] [Finite K] (p f : ℕ) (hp : p.Prime)
    (hK : Nat.card K = p ^ f) (hq : 4 ≤ p ^ f) {n : ℕ} (hn : 3 ≤ n) {X : Type} [Group X]
    {U : Fin n → Subgroup X}
    (hcomm : ∀ i j : Fin n, (i : ℕ) + 1 < j → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j : Fin n, (j : ℕ) = i + 1 → ∃ W, LinearBlockStandardPair K W (U i) (U j))
    (hgen : ⨆ i, U i = ⊤) :
    ∃ ψ : SL(n + 1, K) →* X, Function.Surjective ψ ∧
      ψ.ker ≤ Subgroup.center SL(n + 1, K) ∧ CFSG.IsQuasisimple X ∧
      CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X)
        CFSG.Assembly.LowTwoRank.StatedLieTag.PSL (n + 1) p f := by
  have hK4 : 4 ≤ Nat.card K := hK ▸ hq
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  obtain ⟨F, hF⟩ := exists_ctFamily_of_pairs hK4 (by omega) hcomm hpair
  have hgen' : ⨆ i, (F.ι i).range = ⊤ := by
    simp only [fun i => (hF i).1]
    exact hgen
  have hnt : ∃ i, ∃ A, F.ι i A ≠ 1 := by
    obtain ⟨s, hs⟩ := exists_unit_ne_one (by omega : 3 ≤ Nat.card K)
    refine ⟨⟨0, by omega⟩, torusHom K s, fun h => hs ?_⟩
    apply torusHom_injective
    rw [map_one]
    exact (hF ⟨0, by omega⟩).2 (h.trans (map_one _).symm)
  obtain ⟨ψ, -, hsurj, hker, hqs, -, hmodel⟩ := exists_recognition hn hp hf hK F hgen' hnt
  exact ⟨ψ, hsurj, hker, hqs, hmodel⟩

theorem weakCT_recognition (K : Type) [Field K] [Finite K] (p f : ℕ) (hp : p.Prime)
    (hK : Nat.card K = p ^ f) (hq : 4 ≤ p ^ f) {n : ℕ} (hn : 3 ≤ n) {X : Type} [Group X]
    {U : Fin n → Subgroup X} {W : Fin n → Fin n → Subgroup X} (hW : WeakCTSystem K n U W) :
    ∃ ψ : SL(n + 1, K) →* X, Function.Surjective ψ ∧
      ψ.ker ≤ Subgroup.center SL(n + 1, K) ∧ CFSG.IsQuasisimple X ∧
      CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X)
        CFSG.Assembly.LowTwoRank.StatedLieTag.PSL (n + 1) p f :=
  weakCT_recognition_of_pairs K p f hp hK hq hn hW.comm (fun i j hj => ⟨_, hW.pair i j hj⟩)
    hW.gen

theorem weakCTRecognition :
    ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → Nat.card K = p ^ f → 4 ≤ p ^ f →
      ∀ {n : ℕ}, 3 ≤ n →
      ∀ {X : Type} [Group X] {U : Fin n → Subgroup X} {W : Fin n → Fin n → Subgroup X},
        WeakCTSystem K n U W →
        ∃ ψ : SL(n + 1, K) →* X, Function.Surjective ψ ∧
          ψ.ker ≤ Subgroup.center SL(n + 1, K) ∧ CFSG.IsQuasisimple X ∧
          CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X)
            CFSG.Assembly.LowTwoRank.StatedLieTag.PSL (n + 1) p f :=
  fun K _ _ p f hp hK hq _ hn _ _ _ _ hW =>
  weakCT_recognition K p f hp hK hq hn hW

end CFSG.ClassicalInvolution.WeakCT
