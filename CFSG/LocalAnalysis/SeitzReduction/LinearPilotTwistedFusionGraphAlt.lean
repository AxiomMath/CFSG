module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusionField

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearCover (rootElt rootElt_of_ne coe_rootElt_of_ne
  rootElt_add rootElt_zero rootElt_mul_comm)
open FourGroupEvenCanonical UnitaryHigher
open CFSG.ComponentClassification.UnbalancedCatalog (blockSwapJ_transpose)
open CFSG.ComponentClassification.OutcomeLocal (blockSwapIsometryEquivStatedSp)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ComponentClassification.UnbalancedCatalog
  (even_linear_canonical_graph_symplectic_centralizers)

variable {K : Type} [Field K] {n r : ℕ}

section BlockSwap

theorem blockSwapJ_apply_eq_ite (hr : r + r = n) {p p' : Fin n}
    (hpp : (p' : ℕ) = p + r ∨ (p : ℕ) = p' + r) (u : Fin n) :
    (blockSwapJ n r : Matrix (Fin n) (Fin n) K) u p = if u = p' then 1 else 0 := by
  simp only [blockSwapJ, of_apply, Fin.ext_iff]
  split_ifs with h1 h2 h2
  · rfl
  · exfalso
    omega
  · exfalso
    omega
  · rfl

theorem blockSwapJ_mul_single (hr : r + r = n) {p p' : Fin n}
    (hpp : (p' : ℕ) = p + r ∨ (p : ℕ) = p' + r) (q : Fin n) (c : K) :
    blockSwapJ n r * single p q c = single p' q c := by
  ext u v
  rw [mul_apply, Finset.sum_eq_single p]
  · rw [blockSwapJ_apply_eq_ite hr hpp, single_apply, single_apply]
    by_cases hu : u = p'
    · subst hu
      simp
    · have hu' : ¬p' = u := fun h => hu h.symm
      simp [hu, hu']
  · intro z _ hz
    rw [single_apply_of_row_ne (Ne.symm hz), mul_zero]
  · simp

theorem single_mul_blockSwapJ (hr : r + r = n) {p p' : Fin n}
    (hpp : (p' : ℕ) = p + r ∨ (p : ℕ) = p' + r) (q : Fin n) (c : K) :
    single q p c * blockSwapJ n r = single q p' c := by
  have h := congrArg transpose (blockSwapJ_mul_single (K := K) hr hpp q c)
  rwa [transpose_mul, blockSwapJ_transpose, transpose_single, transpose_single] at h

theorem blockSwapJ_mul_transvection_mul [CharP K 2] (hr : r + r = n) {i i' j j' : Fin n}
    (hi : (i' : ℕ) = i + r ∨ (i : ℕ) = i' + r) (hj : (j' : ℕ) = j + r ∨ (j : ℕ) = j' + r)
    (c : K) :
    blockSwapJ n r * transvection i j c * blockSwapJ n r = transvection i' j' c := by
  rw [transvection, transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    blockSwapJ_mul_self hr, blockSwapJ_mul_single hr hi, single_mul_blockSwapJ hr hj]

theorem transvection_transpose_eq_transvection (i j : Fin n) (c : K) :
    (transvection i j c)ᵀ = transvection j i c := by
  rw [transvection, transvection, transpose_add, transpose_one, transpose_single]

theorem transpose_mul_blockSwapJ_mul_eq [CharP K 2] (hr : r + r = n)
    (x : Matrix (Fin n) (Fin n) K) :
    (blockSwapJ n r * xᵀ * blockSwapJ n r * x)ᵀ * blockSwapJ n r *
        (blockSwapJ n r * xᵀ * blockSwapJ n r * x) =
      blockSwapJ n r * ((blockSwapJ n r * xᵀ * blockSwapJ n r * x) *
        (blockSwapJ n r * xᵀ * blockSwapJ n r * x)) := by
  have hJJ : blockSwapJ n r * blockSwapJ (K := K) n r = 1 := blockSwapJ_mul_self hr
  have hJJ' : ∀ M : Matrix (Fin n) (Fin n) K, blockSwapJ n r * (blockSwapJ n r * M) = M :=
    fun M => by rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  simp only [transpose_mul, transpose_transpose, blockSwapJ_transpose, Matrix.mul_assoc, hJJ',
    hJJ, Matrix.mul_one]

end BlockSwap

theorem perfectTwistedFusionIn_blockSwap [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n) (hr : n = 2 * r) (hfr : 2 ≤ f ∨ 3 ≤ r)
    (C : GL (Fin n) K) (hC : (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r) :
    PerfectTwistedFusionIn (conjAut n K C * dualAut n K) (IsInvolutionClass 2) := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have hrr : r + r = n := by omega
  obtain ⟨hinj, hNinn, -, -, hNC, -, -⟩ :=
    even_linear_canonical_graph_symplectic_centralizers hf hK hn C (Or.inr ⟨r, hr, hC⟩)
  have eN : (matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)).map (conjAut n K) ≃*
      matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K) :=
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, range_subtype])).trans
      (MonoidHom.ofInjective hinj).symm
  let eSp : matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K) ≃* StatedSp r K :=
    (MulEquiv.subgroupCongr (congrArg matrixIsometryGroup hC)).trans
      (blockSwapIsometryEquivStatedSp hrr)
  have := LinearOuter.isPerfect_statedSp_of_card hf hK hfr
  have hperf : Group.IsPerfect
      ((matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)).map (conjAut n K)) :=
    Group.IsPerfect.ofSurjective (f := (eN.trans eSp).symm.toMonoidHom)
      (eN.trans eSp).symm.surjective
  set a : Fin n := ⟨0, by omega⟩ with ha
  set b : Fin n := ⟨1, by omega⟩ with hb
  set a' : Fin n := ⟨r, by omega⟩ with ha'
  set b' : Fin n := ⟨r + 1, by omega⟩ with hb'
  have hab : a ≠ b := by simp [ha, hb, Fin.ext_iff]
  have hb'a' : b' ≠ a' := by simp [ha', hb', Fin.ext_iff]
  have hb'b : b' ≠ b := by simp [hb', hb, Fin.ext_iff]; omega
  have ha'a : a' ≠ a := by simp [ha', ha, Fin.ext_iff]; omega
  have hab' : a ≠ b' := by simp [ha, hb', Fin.ext_iff]
  have hpa : (a' : ℕ) = a + r ∨ (a : ℕ) = a' + r := Or.inl (by simp [ha, ha'])
  have hpb : (b' : ℕ) = b + r ∨ (b : ℕ) = b' + r := Or.inl (by simp [hb, hb', add_comm])
  have hCC : C * C = 1 := Units.ext (by rw [Units.val_mul, hC, blockSwapJ_mul_self hrr,
    Units.val_one])
  have hCinv : ((C⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = blockSwapJ n r := by
    rw [inv_eq_of_mul_eq_one_right hCC, hC]
  set x : SpecialLinearGroup (Fin n) K := rootElt a b 1 with hx
  have hxT : ((x : Matrix (Fin n) (Fin n) K))ᵀ = transvection b a 1 := by
    rw [hx, coe_rootElt_of_ne hab, transvection_transpose_eq_transvection]
  have hJxJ : blockSwapJ n r * (x : Matrix (Fin n) (Fin n) K)ᵀ * blockSwapJ n r =
      transvection b' a' 1 := by
    rw [hxT, blockSwapJ_mul_transvection_mul hrr hpb hpa]
  have hxinv : x⁻¹ = x := by
    rw [hx, ← LinearPilot.rootElt_neg_eq_inv, CharTwo.neg_eq]
  have hαx : (conjAut n K C * dualAut n K) (proj n K x) = proj n K (rootElt b' a' 1) := by
    rw [MulAut.mul_apply, dualAut_proj, conjAut_proj, hxinv]
    congr 1
    apply Subtype.ext
    rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_transpose, hC, hCinv, hJxJ,
      coe_rootElt_of_ne hb'a']
  set y : SpecialLinearGroup (Fin n) K := rootElt b' a' 1 * x with hy
  have hyy : y * y = 1 := by
    have hcomm : rootElt b' a' (1 : K) * x = x * rootElt b' a' 1 :=
      rootElt_mul_comm ha'a hb'b.symm 1 1
    calc y * y = rootElt b' a' 1 * rootElt b' a' 1 * (x * x) := by
          rw [hy, mul_assoc, ← mul_assoc x, ← hcomm]; group
      _ = 1 := by
          rw [← rootElt_add, CharTwo.add_self_eq_zero, rootElt_zero, one_mul, hx, ← rootElt_add,
            CharTwo.add_self_eq_zero, rootElt_zero]
  have hfus : ((conjAut n K C * dualAut n K) (proj n K x))⁻¹ * proj n K x = proj n K y := by
    rw [hαx, ← map_inv, ← map_mul]
    congr 1
    rw [← LinearPilot.rootElt_neg_eq_inv, CharTwo.neg_eq]
  have hymat : (y : Matrix (Fin n) (Fin n) K) =
      blockSwapJ n r * (x : Matrix (Fin n) (Fin n) K)ᵀ * blockSwapJ n r *
        (x : Matrix (Fin n) (Fin n) K) := by
    rw [hy, Matrix.SpecialLinearGroup.coe_mul, hJxJ, coe_rootElt_of_ne hb'a']
  have hyO : SpecialLinearGroup.toGL y ∈ matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K) := by
    rw [mem_matrixIsometryGroup, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hC, hymat,
      transpose_mul_blockSwapJ_mul_eq hrr, ← hymat, ← Matrix.SpecialLinearGroup.coe_mul, hyy,
      Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
  have hcl : IsInvolutionClass 2 (proj n K y) := by
    refine ⟨y, rfl, hyy, ?_⟩
    have hprod : single b' a' (1 : K) * single a b 1 = 0 := by
      simp [ha'a]
    have hsub : (y : Matrix (Fin n) (Fin n) K) - 1 = single b' a' 1 + single a b 1 := by
      rw [hy, Matrix.SpecialLinearGroup.coe_mul, coe_rootElt_of_ne hb'a', hx,
        coe_rootElt_of_ne hab, transvection, transvection, Matrix.add_mul, Matrix.one_mul,
        Matrix.mul_add, Matrix.mul_one, hprod]
      abel
    rw [hsub]
    have hba' : b ≠ a' := by simp [hb, ha', Fin.ext_iff]; omega
    have hcol₁ : (single b' a' (1 : K) + single a b 1).col a' = Pi.single b' 1 := by
      ext i
      by_cases hi : i = b'
      · subst hi
        simp [col_apply, hba']
      · simp [col_apply, hi, Ne.symm hi, hba']
    have hcol₂ : (single b' a' (1 : K) + single a b 1).col b = Pi.single a 1 := by
      ext i
      by_cases hi : i = a
      · subst hi
        simp [col_apply, hab'.symm]
      · simp [col_apply, hi, Ne.symm hi, hba'.symm]
    refine rank_eq_two_of_col_mem (linearIndependent_pi_single_pair hab'.symm) (fun j => ?_)
      hcol₁ hcol₂
    by_cases hj₁ : j = a'
    · rw [hj₁, hcol₁]
      exact Submodule.subset_span (Set.mem_insert _ _)
    · by_cases hj₂ : j = b
      · rw [hj₂, hcol₂]
        exact Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
      · have h0 : (single b' a' (1 : K) + single a b 1).col j = 0 := by
          ext i
          simp [col_apply, Ne.symm hj₁, Ne.symm hj₂]
        rw [h0]
        exact Submodule.zero_mem _
  refine perfectTwistedFusionIn_of_inner (LinearOuter.conj_injective hn) hNinn hNC
    (Subgroup.isPerfect_iff.mp hperf) (proj n K x) ?_ ?_ ?_
  · rw [hfus]
    exact hcl.ne_one two_ne_zero
  · rw [hfus, ← conjAut_toGL]
    exact mem_map_of_mem _ hyO
  · rw [hfus]
    exact hcl

theorem perfectTwistedFusionIn_conjAut_mul_dualAut_of_alt {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n) (hnf : ¬(n = 4 ∧ f = 1)) (A : GL (Fin n) K)
    (hα : (conjAut n K A * dualAut n K) ^ 2 = 1)
    (halt : ∀ v : Fin n → K, v ⬝ᵥ ((A : Matrix (Fin n) (Fin n) K) *ᵥ v) = 0) :
    PerfectTwistedFusionIn (conjAut n K A * dualAut n K) (IsInvolutionClass 2) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨-, ⟨H, C, -, hH, hC⟩, -⟩ :=
    UnitaryHigher.even_linear_pure_graph_involution_normal_forms hf hK hn A hα
  rcases hC with ⟨-, hnalt⟩ | ⟨r, hr, hCJ, -⟩
  · exact absurd halt hnalt
  · refine PerfectTwistedFusionIn.of_conj (ψ := (conjAut n K H)⁻¹)
      (β := conjAut n K C * dualAut n K) ?_ (fun x hx => ?_)
      (perfectTwistedFusionIn_blockSwap hf hK hn hr (by omega) C hCJ)
    · rw [hH]
      group
    · rw [inv_inv]
      exact hx.conjAut H

end CFSG.SeitzReduction.LinearPilot
