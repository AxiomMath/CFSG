module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2OmJoint
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinOPlane

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open QuadraticMap

theorem l2_om_frame {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    (hd : 10 ≤ Module.finrank K V) {x : Fin 4 → V ≃ₗ[K] V}
    (hxO : ∀ i, x i ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hx2 : ∀ i, x i * x i = 1)
    (hxc : ∀ i j, x i * x j = x j * x i) :
    ∃ w : Fin 8 → V, (∀ j, Q (w j) ≠ 0) ∧ (∀ j k, j ≠ k → polar Q (w j) (w k) = 0) ∧
      ∀ i j, ∃ s : K, x i (w j) = s • w j := by
  classical
  have main : ∀ k : ℕ, k ≤ 8 → ∃ w : Fin k → V, (∀ j, Q (w j) ≠ 0) ∧
      (∀ j j', j ≠ j' → polar Q (w j) (w j') = 0) ∧
      ∀ i j, ∃ s : K, x i (w j) = s • w j := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨Fin.elim0, fun j => Fin.elim0 j, fun j => Fin.elim0 j,
        fun i j => Fin.elim0 j⟩
    | succ k ih =>
      intro hk
      obtain ⟨w, hw0, hwo, hwe⟩ := ih (by omega)
      obtain ⟨u, hu, hort⟩ :=
        CFSG.ComponentClassification.HarrisLit.Hin.exists_aniso_orth h2 hQ w hw0 hwo
          (by rw [Fintype.card_fin]; omega)
      obtain ⟨v, hv0, hve, hvort⟩ := l2_om_joint h2 hxO hx2 hxc w hwe hu hort
      refine ⟨Fin.snoc w v, ?_, ?_, ?_⟩
      · intro j
        cases j using Fin.lastCases with
        | cast a => simpa using hw0 a
        | last => simpa using hv0
      · intro j j' hne
        cases j using Fin.lastCases with
        | cast a =>
          cases j' using Fin.lastCases with
          | cast b => simpa using hwo a b (fun h => hne (by rw [h]))
          | last => simpa using hvort a
        | last =>
          cases j' using Fin.lastCases with
          | cast b => rw [Fin.snoc_last, Fin.snoc_castSucc, polar_comm]; exact hvort b
          | last => exact absurd rfl hne
      · intro i j
        cases j using Fin.lastCases with
        | cast a => simpa using hwe i a
        | last => simpa using hve i
  exact main 8 le_rfl

end CFSG.OddStandard.HigherRank.YamadaG23
