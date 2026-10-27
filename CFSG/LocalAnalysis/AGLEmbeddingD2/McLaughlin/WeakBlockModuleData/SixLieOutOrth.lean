module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.OutL5Proof
public import CFSG.RankThree.PartOne.S11d.OutOrthogonal

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs CFSG.RankThree.PartOne.OutStructure
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

theorem subsingleton_ringEquiv_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Subsingleton (K ≃+* K) := by
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  classical
  have h01 : ∀ x : K, x = 0 ∨ x = 1 := by
    intro x
    by_contra hx
    push Not at hx
    have h3 : ({0, 1, x} : Finset K).card = 3 :=
      Finset.card_eq_three.mpr ⟨0, 1, x, zero_ne_one, hx.1.symm, hx.2.symm, rfl⟩
    have := Finset.card_le_univ ({0, 1, x} : Finset K)
    omega
  refine ⟨fun σ τ => RingEquiv.ext fun x => ?_⟩
  rcases h01 x with rfl | rfl <;> simp

theorem autThreePowInner_matrixProjectiveDerived {K : Type} [Field K] [Finite K] [CharP K 2]
    (hsub : Subsingleton (K ≃+* K)) {d : ℕ} (Q : QuadraticForm K (Fin d → K))
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (htop : matrixProjectiveImage Q = ⊤) : AutThreePowInner (matrixProjectiveDerived Q) := by
  have hQ : ∃ v, Q v ≠ 0 := CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  intro ψ k hψ
  have hpow : ψ ^ (3 ^ k) = 1 := by
    apply MulEquiv.ext
    intro x
    rw [mulAut_pow_apply_iterate, hψ]
    rfl
  obtain ⟨g, hg⟩ := (mem_matrixProjectiveImage_iff Q ψ).mp (htop ▸ Subgroup.mem_top ψ)
  have hglin : g ∈ linearSimilarityPairs Q := (mem_linearSimilarityPairs_iff Q g).2
    (Subsingleton.elim _ _)
  have hδ : ψ ∈ orthD Q := (mem_orthD_iff Q ψ).2 ⟨⟨g, hglin⟩, hg⟩
  have hk : ψ ^ (3 ^ k) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) := by
    rw [hpow]; exact one_mem _
  have hin := orthD_D2 Q hQ hnd hT Nat.prime_three (by norm_num) hδ hk
  obtain ⟨a, ha⟩ := hin
  exact ⟨a, fun x => by
    have hx := congrArg (fun φ : MulAut (matrixProjectiveDerived Q) => φ x) ha
    simp only [MulAut.conj_apply] at hx
    exact hx.symm⟩

theorem autThreePowInner_pomegaMinus_two {X : Type} [Group X] {n : ℕ} (hn : 4 ≤ n)
    (h : StatedClassicalModel X .POmegaMinus n 2 1) : AutThreePowInner X := by
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id h
  have : Fintype K := Fintype.ofFinite K
  rw [pow_one] at hK
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus h K (by rw [pow_one, hK]) b c hirr e
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn b c
    hirr
  exact autThreePowInner_of_mulEquiv (coordinateMinusWitnessEquiv K (by omega) b c e)
    (autThreePowInner_matrixProjectiveDerived (subsingleton_ringEquiv_of_card_two hK) _ hnd hT htop)

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
