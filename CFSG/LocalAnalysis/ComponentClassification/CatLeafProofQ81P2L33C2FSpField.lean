module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2FSpComm

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {r : ℕ} {K : Type} [Field K]

theorem formJ_eq (h2 : (2 : K) = 0) : formJ r K = fromBlocks 0 1 1 0 := by
  rw [formJ, neg_one_matrix h2]

theorem formJ_single (j k : Fin r ⊕ Fin r) :
    (formJ r K *ᵥ Pi.single j 1) ⬝ᵥ Pi.single k 1 = formJ r K k j := by
  rw [mulVec_single, dotProduct_single, mul_one]
  simp only [Pi.smul_apply, col_apply, op_smul_eq_smul, smul_eq_mul, one_mul]

theorem fix_formJ_mulVec (φ : K ≃+* K) {u : Fin r ⊕ Fin r → K} (hu : ∀ i, φ (u i) = u i)
    (i : Fin r ⊕ Fin r) : φ ((formJ r K *ᵥ u) i) = (formJ r K *ᵥ u) i := by
  have hJ : ∀ a b, φ (formJ r K a b) = formJ r K a b := fun a b => by
    simpa using congrFun (congrFun (formJ_map (r := r) φ) a) b
  simp only [mulVec, dotProduct, map_sum, map_mul, hJ, hu]

theorem map_vecMulVec_fix (φ : K ≃+* K) {u w : Fin r ⊕ Fin r → K} (hu : ∀ i, φ (u i) = u i)
    (hw : ∀ i, φ (w i) = w i) : (vecMulVec u w).map φ = vecMulVec u w := by
  ext i j
  simp only [Matrix.map_apply, vecMulVec_apply, map_mul, hu, hw]

theorem map_one_add_fix (φ : K ≃+* K) {X : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hX : X.map φ = X) : (1 + X).map φ = 1 + X := by
  rw [Matrix.map_add _ (map_add φ), Matrix.map_one _ (map_zero φ) (map_one φ), hX]

theorem single_fix (φ : K ≃+* K) (j : Fin r ⊕ Fin r) (i : Fin r ⊕ Fin r) :
    φ ((Pi.single j 1 : Fin r ⊕ Fin r → K) i) = (Pi.single j 1 : Fin r ⊕ Fin r → K) i := by
  by_cases h : i = j
  · subst h
    simp
  · simp [h]

theorem hasWit_fieldAut_sp [CharP K 2] (hr : 2 ≤ r) (φ : K ≃+* K) :
    HasWit (fieldAut r K φ) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have : NeZero r := ⟨by omega⟩
  set i0 : Fin r := ⟨0, by omega⟩
  set i1 : Fin r := ⟨1, by omega⟩
  have h01 : i1 ≠ i0 := by simp [i0, i1, Fin.ext_iff]
  set x : Fin r ⊕ Fin r → K := Pi.single (Sum.inl i0) 1 with hx
  set y : Fin r ⊕ Fin r → K := Pi.single (Sum.inr i0) 1 with hy
  set m : Fin r ⊕ Fin r → K := Pi.single (Sum.inl i1) 1 with hm
  have hxf : ∀ i, φ (x i) = x i := single_fix φ _
  have hyf : ∀ i, φ (y i) = y i := single_fix φ _
  have hmf : ∀ i, φ (m i) = m i := single_fix φ _
  have hfix : ∀ g : StatedSp r K, (spMat g).map φ = spMat g →
      fieldAut r K φ (proj r K g) = proj r K g := by
    intro g hg
    rw [fieldAut_proj]
    congr 1
    apply spMat_injective
    exact hg
  refine hasWit_sp_comm (Q := fun M => M.map φ = M) hfix (x := x) (y := y) (m := m) ?_ ?_ ?_
    ?_ ?_ ?_ ?_
  · rw [hx, hy, formJ_single, formJ_eq h2]
    simp
  · rw [hx, hm, formJ_single, formJ_eq h2]
    simp
  · rw [hy, hm, formJ_single, formJ_eq h2]
    simp [h01]
  · rw [hm]
    exact Pi.single_ne_zero_iff.mpr one_ne_zero
  · exact map_one_add_fix φ (map_vecMulVec_fix φ hxf (fix_formJ_mulVec φ hxf))
  · exact map_one_add_fix φ (map_vecMulVec_fix φ hyf (fix_formJ_mulVec φ hyf))
  · refine map_one_add_fix φ ?_
    rw [Matrix.map_add _ (map_add φ), map_vecMulVec_fix φ hmf (fix_formJ_mulVec φ hxf),
      map_vecMulVec_fix φ hxf (fix_formJ_mulVec φ hmf)]

theorem hasWit_field_sp {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hr : 2 ≤ r)
    {v : MulAut (StatedProj (StatedSp r K))} (hv : v * v = 1) (g : StatedSp r K)
    {φ : K ≃+* K} (hφ : φ ≠ 1) (hvg : v = spInner r K g * fieldAut r K φ) : HasWit v := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h, hh⟩ :=
    even_symplectic_quadratic_involution_descent (by omega) hf hK hv g φ
      (by rw [hvg, spInner_apply]) hφ
  rw [hh]
  exact (hasWit_fieldAut_sp hr φ).conj _

end CFSG.ComponentClassification.HarrisLit.L33.C2
