module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRowBlock
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRowScalar
public import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryComponent

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.ComponentClassification CFSG.Assembly.LowTwoRank Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.Census
open CFSG.OddStandard.SmallF3.HypA2 (TypU)

variable {p f : ℕ} {K : Type} [Field K] {k m : ℕ}

theorem a2l_blockGL_mem_unitarySU (h : UnitaryFieldData p f K) {X : GL (Fin k) K}
    (hX : X ∈ unitarySU p f K k) : blockGL K k m X ∈ unitarySU p f K (k + m) := by
  rw [mem_unitarySU_iff h] at hX ⊢
  rw [det_blockGL, coe_blockGL_eq_diagBlock, diagBlock_map, diagBlock_transpose, diagBlock_mul,
    Matrix.map_one _ (map_zero _) (map_one _), transpose_one, Matrix.mul_one, hX.2, diagBlock_one]
  exact ⟨hX.1, rfl⟩

@[expose] noncomputable def a2lUBlock (h : UnitaryFieldData p f K) (k m : ℕ) :
    unitarySU p f K k →* unitarySU p f K (k + m) :=
  ((blockGL K k m).comp (unitarySU p f K k).subtype).codRestrict _
    fun X => a2l_blockGL_mem_unitarySU h X.2

theorem a2l_coe_uBlock (h : UnitaryFieldData p f K) (X : unitarySU p f K k) :
    (((a2lUBlock h k m X : unitarySU p f K (k + m)) : GL (Fin (k + m)) K) :
      Matrix (Fin (k + m)) (Fin (k + m)) K) =
      diagBlock ((X : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) 1 :=
  rfl

theorem a2lUBlock_injective (h : UnitaryFieldData p f K) :
    Function.Injective (a2lUBlock h k m) := by
  intro X Y hXY
  have h' := congrArg (fun g : unitarySU p f K (k + m) => ((g : GL (Fin (k + m)) K) :
    Matrix (Fin (k + m)) (Fin (k + m)) K)) hXY
  simp only [a2l_coe_uBlock] at h'
  exact Subtype.ext (Units.ext (diagBlock_injective h').1)

theorem a2l_conj_mem_range_uBlock (h : UnitaryFieldData p f K) (h2 : (2 : K) ≠ 0)
    {X₀ : unitarySU p f K k} (hX₀ : ((X₀ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) = -1)
    {g : unitarySU p f K (k + m)} (hg : g * a2lUBlock h k m X₀ = a2lUBlock h k m X₀ * g)
    (X : unitarySU p f K k) : g * a2lUBlock h k m X * g⁻¹ ∈ (a2lUBlock h k m).range := by
  have hcomm : ∀ x : unitarySU p f K (k + m), x * a2lUBlock h k m X₀ = a2lUBlock h k m X₀ * x →
      ∃ A D, ((x : GL (Fin (k + m)) K) : Matrix (Fin (k + m)) (Fin (k + m)) K) =
        diagBlock A D := fun x hx =>
    eq_diagBlock_of_comm h2 (by
      have := congrArg (fun y : unitarySU p f K (k + m) => ((y : GL (Fin (k + m)) K) :
        Matrix (Fin (k + m)) (Fin (k + m)) K)) hx
      simpa only [Subgroup.coe_mul, Units.val_mul, a2l_coe_uBlock, hX₀] using this)
  have hg' : g⁻¹ * a2lUBlock h k m X₀ = a2lUBlock h k m X₀ * g⁻¹ := (Commute.inv_left hg).eq
  obtain ⟨A, D, hAD⟩ := hcomm g hg
  obtain ⟨A', D', hAD'⟩ := hcomm g⁻¹ hg'
  have hone : diagBlock (A * A') (D * D') = diagBlock 1 1 := by
    rw [← diagBlock_mul, ← hAD, ← hAD', diagBlock_one, ← Units.val_mul, ← Subgroup.coe_mul,
      mul_inv_cancel, Subgroup.coe_one, Units.val_one]
  have hone' : diagBlock (A' * A) (D' * D) = diagBlock 1 1 := by
    rw [← diagBlock_mul, ← hAD, ← hAD', diagBlock_one, ← Units.val_mul, ← Subgroup.coe_mul,
      inv_mul_cancel, Subgroup.coe_one, Units.val_one]
  obtain ⟨hA, hD⟩ := diagBlock_injective hone
  obtain ⟨hA', -⟩ := diagBlock_injective hone'
  have hunit : ∀ x : unitarySU p f K (k + m), ∀ A D, ((x : GL (Fin (k + m)) K) :
      Matrix (Fin (k + m)) (Fin (k + m)) K) = diagBlock A D → (A.map h.bar)ᵀ * A = 1 := by
    intro x A D hx
    have hx2 := ((mem_unitarySU_iff h).mp x.2).2
    rw [hx, diagBlock_map, diagBlock_transpose, diagBlock_mul, ← diagBlock_one] at hx2
    exact (diagBlock_injective hx2).1
  have hAu := hunit g A D hAD
  have hA'u := hunit g⁻¹ A' D' hAD'
  set Xm := ((X : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)
  obtain ⟨hXdet, hXu⟩ := (mem_unitarySU_iff h).mp X.2
  have hdet : (A * Xm * A').det = 1 := by
    rw [det_mul, det_mul, hXdet, mul_one, ← det_mul, hA, det_one]
  set Y : GL (Fin k) K :=
    GeneralLinearGroup.mkOfDetNeZero (A * Xm * A') (by rw [hdet]; exact one_ne_zero)
  have hYcoe : (Y : Matrix (Fin k) (Fin k) K) = A * Xm * A' := rfl
  have hY : Y ∈ unitarySU p f K k := by
    rw [mem_unitarySU_iff h, hYcoe]
    refine ⟨hdet, ?_⟩
    rw [Matrix.map_mul, Matrix.map_mul, transpose_mul, transpose_mul]
    calc (A'.map h.bar)ᵀ * ((Xm.map h.bar)ᵀ * (A.map h.bar)ᵀ) * (A * Xm * A')
        = (A'.map h.bar)ᵀ * ((Xm.map h.bar)ᵀ * ((A.map h.bar)ᵀ * A) * Xm) * A' := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hAu, Matrix.mul_one, hXu, Matrix.mul_one, hA'u]
  refine ⟨⟨Y, hY⟩, Subtype.ext (Units.ext ?_)⟩
  rw [a2l_coe_uBlock]
  change diagBlock (A * Xm * A') 1 = ((g : GL (Fin (k + m)) K) :
      Matrix (Fin (k + m)) (Fin (k + m)) K) * diagBlock Xm 1 *
    (((g⁻¹ : unitarySU p f K (k + m)) : GL (Fin (k + m)) K) :
      Matrix (Fin (k + m)) (Fin (k + m)) K)
  rw [hAD, hAD', diagBlock_mul, diagBlock_mul, Matrix.mul_one, hD]

theorem a2lDatum_psu_block [Finite K] (h : UnitaryFieldData p f K) (h2 : (2 : K) ≠ 0)
    (hk : 1 ≤ k) (hm : 1 ≤ m) {X₀ : unitarySU p f K k}
    (hX₀ : ((X₀ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) = -1) {q₀ : ℕ} (hodd : Odd q₀)
    (h5 : 5 ≤ q₀) {N : Subgroup (unitarySU p f K (k + m))}
    (hNJ : N ≤ (a2lUBlock h k m).range) (htN : a2lUBlock h k m X₀ ∈ N)
    (hq : CFSG.IsQuasisimple (unitarySU p f K k)) (hN : HarrisLit.IsSLTwoOver q₀ ↥N)
    (hTU : TypU ↥(a2lUBlock h k m).range) :
    a2lDatum (StatedProj (unitarySU p f K (k + m))) := by
  have hX₀sq : X₀ * X₀ = 1 := Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Units.val_mul, hX₀, neg_mul_neg, Matrix.one_mul]; rfl))
  have hcoe : (((a2lUBlock h k m X₀ : unitarySU p f K (k + m)) : GL (Fin (k + m)) K) :
      Matrix (Fin (k + m)) (Fin (k + m)) K) = diagBlock (-1) 1 := by
    rw [a2l_coe_uBlock, hX₀]
  have hentry : ∀ X : unitarySU p f K k, ∀ i : Fin m,
      (((a2lUBlock h k m X : unitarySU p f K (k + m)) : GL (Fin (k + m)) K) :
        Matrix (Fin (k + m)) (Fin (k + m)) K) (finSumFinEquiv (Sum.inr i))
        (finSumFinEquiv (Sum.inr i)) = 1 := fun X i => by
    rw [a2l_coe_uBlock, diagBlock_apply_inr, Matrix.one_apply_eq]
  refine a2lDatum_of_block_normal (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact Open.StatedAPI.statedScalars_subgroupOf_le_center _)
    hodd h5 (by rw [← map_mul, hX₀sq, map_one]) ?_ hNJ htN ?_ ?_ ?_ ?_ hN hTU
  · intro hπ
    refine h2 (a2l_two_eq_zero_of_mk_eq_one hπ (a := finSumFinEquiv (Sum.inl ⟨0, hk⟩))
      (b := finSumFinEquiv (Sum.inr ⟨0, hm⟩)) ?_ (hentry X₀ ⟨0, hm⟩))
    rw [hcoe, diagBlock_apply_inl]
    simp
  · rintro _ ⟨X, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hX₀, Matrix.mul_neg,
      Matrix.neg_mul, Matrix.mul_one, Matrix.one_mul]
  · rintro g hg _ ⟨X, rfl⟩
    exact a2l_conj_mem_range_uBlock h h2 hX₀ (mem_centralizer_singleton_iff.1 hg) X
  · exact CFSG.IsQuasisimple.of_mulEquiv
      (MonoidHom.ofInjective (a2lUBlock_injective (k := k) (m := m) h)).symm hq
  · rintro _ ⟨X, rfl⟩ hx
    exact a2l_eq_one_of_mk_eq_one hx (a := finSumFinEquiv (Sum.inr ⟨0, hm⟩))
      (hentry X ⟨0, hm⟩)

end CFSG.OddStandard.SmallF3.HypA2Leaves
