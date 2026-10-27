module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRowBlock
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCoverBasic
public import CFSG.RankThree.PartTwo.Census.OddClassical.LinearComponent

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.ComponentClassification Matrix CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartTwo.Census
open CFSG.OddStandard.SmallF3.HypA2 (TypU)
open scoped MatrixGroups

section Block

variable {K : Type} [Field K] {k m : ℕ}

theorem a2l_coe_blockSL (X : SL(k, K)) :
    ((blockSL K k m X : SL(k + m, K)) : Matrix (Fin (k + m)) (Fin (k + m)) K) =
      diagBlock (X : Matrix (Fin k) (Fin k) K) 1 :=
  rfl

theorem a2l_blockSL_injective : Function.Injective (blockSL K k m) := by
  intro X Y h
  have h' := congrArg (fun A : SL(k + m, K) => (A : Matrix (Fin (k + m)) (Fin (k + m)) K)) h
  simp only [a2l_coe_blockSL] at h'
  exact Subtype.ext (diagBlock_injective h').1

theorem a2l_blockSL_mem_center_iff (hk : 1 ≤ k) (hm : 1 ≤ m) (X : SL(k, K)) :
    blockSL K k m X ∈ center (SL(k + m, K)) ↔ X = 1 := by
  constructor
  · intro hX
    by_contra h1
    have hs := SpecialLinearGroup.scalar_eq_self_of_mem_center hX
      (finSumFinEquiv (Sum.inl ⟨0, hk⟩))
    refine blockGL_ne_scalar_of_ne_one hm (X := SpecialLinearGroup.toGL X) ?_ _ hs.symm
    intro h
    exact h1 (SpecialLinearGroup.toGL_injective (h.trans (map_one _).symm))
  · rintro rfl
    rw [map_one]
    exact Subgroup.one_mem _

theorem a2l_conj_mem_range_blockSL (h2 : (2 : K) ≠ 0) {T : SL(k, K)}
    (hT : (T : Matrix (Fin k) (Fin k) K) = -1) {g : SL(k + m, K)}
    (hg : g * blockSL K k m T = blockSL K k m T * g) (X : SL(k, K)) :
    g * blockSL K k m X * g⁻¹ ∈ (blockSL K k m).range := by
  have hTm : ((blockSL K k m T : SL(k + m, K)) : Matrix (Fin (k + m)) (Fin (k + m)) K) =
      diagBlock (-1) 1 := by
    rw [a2l_coe_blockSL, hT]
  have hcomm : ∀ x : SL(k + m, K), x * blockSL K k m T = blockSL K k m T * x →
      ∃ A D, (x : Matrix (Fin (k + m)) (Fin (k + m)) K) = diagBlock A D := fun x hx =>
    eq_diagBlock_of_comm h2 (by
      have := congrArg Subtype.val hx
      change (x : Matrix (Fin (k + m)) (Fin (k + m)) K) *
          (blockSL K k m T : Matrix (Fin (k + m)) (Fin (k + m)) K) =
        (blockSL K k m T : Matrix (Fin (k + m)) (Fin (k + m)) K) *
          (x : Matrix (Fin (k + m)) (Fin (k + m)) K) at this
      rwa [hTm] at this)
  have hg' : g⁻¹ * blockSL K k m T = blockSL K k m T * g⁻¹ := (Commute.inv_left hg).eq
  obtain ⟨A, D, hAD⟩ := hcomm g hg
  obtain ⟨A', D', hAD'⟩ := hcomm g⁻¹ hg'
  have hone := congrArg Subtype.val (mul_inv_cancel g)
  change (g : Matrix (Fin (k + m)) (Fin (k + m)) K) *
    ((g⁻¹ : SL(k + m, K)) : Matrix (Fin (k + m)) (Fin (k + m)) K) = 1 at hone
  rw [hAD, hAD', diagBlock_mul, ← diagBlock_one] at hone
  obtain ⟨hA, hD⟩ := diagBlock_injective hone
  have hdet : (A * (X : Matrix (Fin k) (Fin k) K) * A').det = 1 := by
    rw [det_mul, det_mul, X.2, mul_one, ← det_mul, hA, det_one]
  refine ⟨⟨A * X * A', hdet⟩, Subtype.ext ?_⟩
  change diagBlock (A * (X : Matrix (Fin k) (Fin k) K) * A') 1 =
    (g : Matrix (Fin (k + m)) (Fin (k + m)) K) * diagBlock (X : Matrix (Fin k) (Fin k) K) 1 *
      ((g⁻¹ : SL(k + m, K)) : Matrix (Fin (k + m)) (Fin (k + m)) K)
  rw [hAD, hAD', diagBlock_mul, diagBlock_mul, Matrix.mul_one, hD]

end Block

theorem a2lDatum_psl_block {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0) {k m : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m) {F : Type} [Field F] [Fintype F] {q₀ : ℕ} (hodd : Odd q₀)
    (h5 : 5 ≤ q₀) (hF : Fintype.card F = q₀) (φ : SL(2, F) →* SL(k, K))
    (hφ : Function.Injective φ) (hφT : (φ (a2lNegOne F) : Matrix (Fin k) (Fin k) K) = -1)
    (hq : CFSG.IsQuasisimple SL(k, K)) (hTU : TypU ↥(blockSL K k m).range) :
    a2lDatum (ProjectiveSpecialLinearGroup (Fin (k + m)) K) := by
  have hφ' : Function.Injective ((blockSL K k m).comp φ) :=
    a2l_blockSL_injective.comp hφ
  have hφ1 : φ (a2lNegOne F) ≠ 1 := by
    intro h1
    have h0 : (φ (a2lNegOne F) : Matrix (Fin k) (Fin k) K) = 1 := by rw [h1]; rfl
    rw [hφT] at h0
    have h00 := congrFun (congrFun h0 ⟨0, hk⟩) ⟨0, hk⟩
    simp only [Matrix.neg_apply, Matrix.one_apply_eq] at h00
    exact h2 (by linear_combination -h00)
  have hcen : ∀ X : SL(k, K), φ (a2lNegOne F) * X = X * φ (a2lNegOne F) := fun X => by
    apply Subtype.ext
    change (φ (a2lNegOne F) : Matrix (Fin k) (Fin k) K) * (X : Matrix (Fin k) (Fin k) K) =
      (X : Matrix (Fin k) (Fin k) K) * (φ (a2lNegOne F) : Matrix (Fin k) (Fin k) K)
    rw [hφT, Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul, Matrix.mul_one]
  refine a2lDatum_of_block_normal (QuotientGroup.mk' (center SL(k + m, K)))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) hodd h5
    (t := blockSL K k m (φ (a2lNegOne F))) ?_ ?_
    (J := (blockSL K k m).range) (N := ((blockSL K k m).comp φ).range)
    (fun x hx => by obtain ⟨y, rfl⟩ := hx; exact ⟨φ y, rfl⟩) ⟨a2lNegOne F, rfl⟩ ?_ ?_ ?_ ?_ ?_
    hTU
  · rw [← map_mul, ← map_mul, ← sq, a2lNegOne_sq, map_one, map_one]
  · rw [Ne, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, a2l_blockSL_mem_center_iff hk hm]
    exact hφ1
  · rintro _ ⟨X, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hcen]
  · rintro g hg _ ⟨X, rfl⟩
    exact a2l_conj_mem_range_blockSL h2 hφT (mem_centralizer_singleton_iff.1 hg) X
  · exact CFSG.IsQuasisimple.of_mulEquiv
      (MonoidHom.ofInjective (a2l_blockSL_injective (K := K) (k := k) (m := m))).symm hq
  · rintro _ ⟨X, rfl⟩ hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      a2l_blockSL_mem_center_iff hk hm] at hx
    rw [hx, map_one]
  · exact ⟨F, inferInstance, inferInstance, hF, ⟨(MonoidHom.ofInjective hφ').symm⟩⟩

theorem a2l_rowPSL_two {X : Type} [Group X] [Finite X] {n f : ℕ} (hn : 3 ≤ n) (hf : 2 ≤ f)
    (hm : LieModel X .PSL n 3 f) : a2lDatum X := by
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hm.statedClassicalModel (by decide)
  haveI := Fintype.ofFinite F
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 + m := ⟨n - 2, by omega⟩
  have hFc : Fintype.card F = 3 ^ f := by rw [← Nat.card_eq_fintype_card, hcard]
  have hodd : Odd (3 ^ f) := Odd.pow (by decide)
  have h9 : 9 ≤ 3 ^ f :=
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h2 : (2 : F) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F (by rw [hcard]; exact hodd)
  obtain ⟨s, -, hs⟩ : ∃ s ⊆ (Finset.univ : Finset F), s.card = 4 :=
    Finset.exists_subset_card_eq (by rw [Finset.card_univ, hFc]; omega)
  have hq : CFSG.IsQuasisimple SL(2, F) := CFSG.RankThree.Classical.isQuasisimple_SL2 ⟨s, hs⟩
  have hN : HarrisLit.IsSLTwoOver (3 ^ f) ↥(blockSL F 2 m).range :=
    ⟨F, inferInstance, inferInstance, hFc,
      ⟨(MonoidHom.ofInjective a2l_blockSL_injective).symm⟩⟩
  have hd := a2lDatum_psl_block h2 (k := 2) (m := m) (by norm_num)
    (by omega) hodd (by omega) hFc (MonoidHom.id SL(2, F)) Function.injective_id rfl hq
    (a2l_typU_of_isSLTwoOver hodd h9 hN)
  exact a2lDatum_of_mulEquiv
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj (2 + m) F).symm).symm hd

end CFSG.OddStandard.SmallF3.HypA2Leaves
