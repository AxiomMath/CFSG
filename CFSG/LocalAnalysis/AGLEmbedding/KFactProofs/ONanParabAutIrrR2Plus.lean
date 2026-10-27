module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrR2PlusSyl
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrOrth
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrTorus

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.OutStructure

section Core

variable {K : Type} [Field K] [Finite K] [CharP K 2] (n : ℕ)

theorem autScalarTorus_plusStated (hn : 4 ≤ n)
    (hnd : (QuadraticMap.polarBilin (coordinateQuadPlus n K)).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧
      ∀ x ∈ T, coordinateQuadPlus n K x = 0)
    (hE : ∀ α : MulAut (StatedProj (StatedOmega (StatedQuadPlus n K))),
      (∃ e : ℕ, 0 < e ∧ Nat.Coprime e 6 ∧
        α ^ e ∈ inn (StatedProj (StatedOmega (StatedQuadPlus n K)))) →
          MulAut.congr (plusProjReindex n) α ∈ matrixProjectiveImage (coordinateQuadPlus n K)) :
    AutScalarTorus (StatedProj (StatedOmega (StatedQuadPlus n K))) := by
  have hn3 : 3 ≤ n := by omega
  obtain ⟨S₁, hS₁⟩ := plusProjectiveUnipotent_isSylow n K 2 hn3
  have hN : Subgroup.normalizer ((S₁ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K)))) :
      Set (StatedProj (StatedOmega (StatedQuadPlus n K)))) = plusProjectiveBorel n K := by
    rw [hS₁]
    exact plusProjectiveUnipotent_normalizer n K hn3
  refine AutScalarTorus.of_decomp S₁ ?_ ?_
  · intro b hb c hc
    rw [hN] at hb hc
    rw [hS₁]
    exact plus_commutator_mem_unipotent n hn3 hb hc
  · rintro α ⟨e, he, he6, hinn⟩
    have hodd : Odd e :=
      Nat.Coprime.odd_of_right (Nat.Coprime.coprime_dvd_right (by norm_num) he6)
    have hαP := hE α ⟨e, he, he6, hinn⟩
    have hαe : (MulAut.congr (plusProjReindex n) α) ^ e ∈
        inn (matrixProjectiveDerived (coordinateQuadPlus n K)) := by
      rw [← map_pow, ← map_inn_congr (plusProjReindex n)]
      exact ⟨α ^ e, hinn, rfl⟩
    obtain ⟨x, σ, hασ⟩ := exists_conj_mul_plusFieldAut n (by omega) hnd hT hαP hodd hαe
    obtain ⟨j, hj⟩ := exists_pow_two_of_ringEquiv σ
    refine ⟨(plusProjReindex n).symm x, plusStatedAut n σ, 2 ^ j, ?_, fun w => ?_, fun b hb => ?_⟩
    · have hα' : α = MulAut.congr (plusProjReindex n).symm
          (MulAut.congr (plusProjReindex n) α) := by
        ext y
        simp [MulAut.congr_apply]
      rw [hα', hασ, map_mul, congr_conj]
      rfl
    · rw [hS₁]
      exact plusStatedAut_mem_unipotent_iff n hn3 σ w
    · rw [hN] at hb
      rw [hS₁]
      exact plusStatedAut_mul_pow_inv_mem n hn3 σ hj hb

end Core

section Model

theorem inn_le_matrixProjectiveImage {K : Type} [Field K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) :
    inn (matrixProjectiveDerived Q) ≤ matrixProjectiveImage Q :=
  fun δ hδ => by
    obtain ⟨g, rfl⟩ := (mem_orthD_iff Q δ).1 (inner_le_orthD Q hδ)
    exact ⟨g.val, rfl⟩

theorem autScalarTorus_pomegaPlus {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaPlus n 2 f) : AutScalarTorus Y := by
  have hn : 4 ≤ n := h.1.2.2
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  have : Finite (StatedProj (StatedOmega (StatedQuadPlus n K))) := Finite.of_equiv Y e.toEquiv
  refine AutScalarTorus.of_mulEquiv e.symm (autScalarTorus_plusStated n hn hnd hT ?_)
  rintro α ⟨m, hm, hm6, hinn⟩
  have hαm : (MulAut.congr (plusProjReindex n) α) ^ m ∈
      inn (matrixProjectiveDerived (coordinateQuadPlus n K)) := by
    rw [← map_pow, ← map_inn_congr (plusProjReindex n)]
    exact ⟨α ^ m, hinn, rfl⟩
  rcases Nat.eq_or_lt_of_le hn with rfl | hn5
  · exact mem_of_pow_mem_of_index_le_three_of_coprime _ (plus_four_index h K hK e) hm6
      (inn_le_matrixProjectiveImage _ hαm)
  · rw [CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn5]
    exact Subgroup.mem_top _

end Model

end CFSG.AGLEmbedding.ParabAutIrr
