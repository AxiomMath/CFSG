module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLNormal
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOrthNormal

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup
open CFSG.ComponentClassification.Burgoyne.PSL (OrthNF exists_frame exists_orth_normal_form
  isCompl_ker_of_sq_one)

variable {K : Type} [Field K] {d : ℕ}

theorem dot_symm {R : Matrix (Fin d) (Fin d) K} (hR : Rᵀ = R) (x y : Fin d → K) :
    y ⬝ᵥ R *ᵥ x = x ⬝ᵥ R *ᵥ y := by
  rw [dotProduct_mulVec, dotProduct_comm, ← vecMul_transpose, hR]

abbrev eigP (A : Matrix (Fin d) (Fin d) K) : Submodule K (Fin d → K) :=
  LinearMap.ker (Matrix.toLin' A - 1)

abbrev eigM (A : Matrix (Fin d) (Fin d) K) : Submodule K (Fin d → K) :=
  LinearMap.ker (Matrix.toLin' A + 1)

theorem mem_eigP {A : Matrix (Fin d) (Fin d) K} {v : Fin d → K} : v ∈ eigP A ↔ A *ᵥ v = v := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
    Matrix.toLin'_apply]

theorem mem_eigM {A : Matrix (Fin d) (Fin d) K} {v : Fin d → K} : v ∈ eigM A ↔ A *ᵥ v = -v := by
  rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, Matrix.toLin'_apply,
    add_eq_zero_iff_eq_neg]

theorem isCompl_eig (h2 : (2 : K) ≠ 0) {A : Matrix (Fin d) (Fin d) K} (hA2 : A * A = 1) :
    IsCompl (eigP A) (eigM A) := by
  refine isCompl_ker_of_sq_one h2 ?_
  rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hA2, Matrix.toLin'_one]
  rfl

theorem finrank_eig_add (h2 : (2 : K) ≠ 0) {A : Matrix (Fin d) (Fin d) K} (hA2 : A * A = 1) :
    Module.finrank K (eigM A) + Module.finrank K (eigP A) = d := by
  rw [add_comm, Submodule.finrank_add_eq_of_isCompl (isCompl_eig h2 hA2), Module.finrank_fin_fun]

theorem orth_eig (h2 : (2 : K) ≠ 0) {R A : Matrix (Fin d) (Fin d) K} (hAR : Aᵀ * R * A = R)
    {x y : Fin d → K} (hx : x ∈ eigP A) (hy : y ∈ eigM A) : x ⬝ᵥ R *ᵥ y = 0 := by
  have e : x ⬝ᵥ (Aᵀ * R * A) *ᵥ y = (A *ᵥ x) ⬝ᵥ R *ᵥ (A *ᵥ y) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  rw [hAR, mem_eigP.1 hx, mem_eigM.1 hy, mulVec_neg, dotProduct_neg] at e
  have : (2 : K) * (x ⬝ᵥ R *ᵥ y) = 0 := by linear_combination e
  exact (mul_eq_zero.1 this).resolve_left h2

theorem nondeg_eig (h2 : (2 : K) ≠ 0) {R : GL (Fin d) K} (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R)
    {A : Matrix (Fin d) (Fin d) K} (hAR : Aᵀ * (R : Matrix (Fin d) (Fin d) K) * A = R)
    (hA2 : A * A = 1) {W : Submodule K (Fin d → K)} (hW : W = eigP A ∨ W = eigM A) :
    ∀ v ∈ W, (∀ u ∈ W, v ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ u = 0) → v = 0 := by
  intro v hv hvW
  have hall : ∀ z, v ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ z = 0 := by
    intro z
    obtain ⟨y, hy, x, hx, rfl⟩ := Submodule.mem_sup.1 ((isCompl_eig h2 hA2).sup_eq_top ▸
      Submodule.mem_top : z ∈ eigP A ⊔ eigM A)
    rw [mulVec_add, dotProduct_add]
    rcases hW with rfl | rfl
    · rw [hvW y hy, orth_eig h2 hAR hv hx, add_zero]
    · rw [hvW x hx, dot_symm hR, orth_eig h2 hAR hy hv, zero_add]
  have hRv : (R : Matrix (Fin d) (Fin d) K) *ᵥ v = 0 := by
    funext i
    have := hall (Pi.single i 1)
    rw [dot_symm hR, single_one_dotProduct] at this
    exact this
  have := congrArg (fun z => ((R⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ z) hRv
  simpa [mulVec_mulVec, ← Units.val_mul] using this

@[expose] def gramMat (R : Matrix (Fin d) (Fin d) K) {W : Submodule K (Fin d → K)} {m : ℕ}
    (u : Module.Basis (Fin m) K W) : Matrix (Fin m) (Fin m) K :=
  Matrix.of fun i j => (u i : Fin d → K) ⬝ᵥ R *ᵥ (u j : Fin d → K)

theorem gramMat_transpose {R : Matrix (Fin d) (Fin d) K} (hR : Rᵀ = R)
    {W : Submodule K (Fin d → K)} {m : ℕ} (u : Module.Basis (Fin m) K W) :
    (gramMat R u)ᵀ = gramMat R u := by
  ext i j
  simp only [transpose_apply, gramMat, of_apply]
  exact dot_symm hR _ _

theorem gramMat_det_ne_zero {R : Matrix (Fin d) (Fin d) K} (hR : Rᵀ = R)
    {W : Submodule K (Fin d → K)} (hW : ∀ v ∈ W, (∀ u ∈ W, v ⬝ᵥ R *ᵥ u = 0) → v = 0)
    {m : ℕ} (u : Module.Basis (Fin m) K W) : (gramMat R u).det ≠ 0 := by
  intro h0
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  set y : W := ∑ j, x j • u j with hy
  have hyv : (y : Fin d → K) = ∑ j, x j • (u j : Fin d → K) := by
    rw [hy, Submodule.coe_sum]
    rfl
  have hyR : ∀ i, (u i : Fin d → K) ⬝ᵥ R *ᵥ (y : Fin d → K) = 0 := by
    intro i
    have e := congrFun hx i
    simp only [mulVec, dotProduct, gramMat, of_apply, Pi.zero_apply] at e
    rw [hyv, mulVec_sum, dotProduct_sum]
    simp only [mulVec_smul, dotProduct_smul, smul_eq_mul]
    rw [← e]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [dotProduct, mulVec]
    ring
  have hy0 : (y : Fin d → K) = 0 := by
    refine hW _ y.2 fun z hz => ?_
    rw [dot_symm hR]
    have hz' : z = ∑ i, (u.repr ⟨z, hz⟩ i) • (u i : Fin d → K) := by
      have := congrArg Subtype.val (u.sum_repr ⟨z, hz⟩)
      rw [Submodule.coe_sum] at this
      exact this.symm
    rw [hz', sum_dotProduct]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [smul_dotProduct, hyR, smul_zero]
  have hli := u.linearIndependent
  rw [Fintype.linearIndependent_iff] at hli
  exact hx0 (funext (hli x (by rw [← hy]; exact Subtype.ext hy0)))

@[expose] def famOf {W : Submodule K (Fin d → K)} {m : ℕ} (u : Module.Basis (Fin m) K W)
    (P : Matrix (Fin m) (Fin m) K) : Fin m → Fin d → K :=
  fun j => ∑ i, P i j • (u i : Fin d → K)

theorem famOf_mem {W : Submodule K (Fin d → K)} {m : ℕ} (u : Module.Basis (Fin m) K W)
    (P : Matrix (Fin m) (Fin m) K) (j : Fin m) : famOf u P j ∈ W :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (u i).2

theorem famOf_gram (R : Matrix (Fin d) (Fin d) K) {W : Submodule K (Fin d → K)} {m : ℕ}
    (u : Module.Basis (Fin m) K W) (P : Matrix (Fin m) (Fin m) K) (j k : Fin m) :
    famOf u P j ⬝ᵥ R *ᵥ famOf u P k = (Pᵀ * gramMat R u * P) j k := by
  simp only [famOf, mulVec_sum, mulVec_smul, dotProduct_sum, sum_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, Matrix.mul_apply, transpose_apply, gramMat, of_apply,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

@[expose] def gramGL {R : Matrix (Fin d) (Fin d) K} (hR : Rᵀ = R)
    {W : Submodule K (Fin d → K)} (hW : ∀ v ∈ W, (∀ u ∈ W, v ⬝ᵥ R *ᵥ u = 0) → v = 0)
    {m : ℕ} (u : Module.Basis (Fin m) K W) : GL (Fin m) K :=
  Matrix.nonsingInvUnit (gramMat R u) (isUnit_iff_ne_zero.2 (gramMat_det_ne_zero hR hW u))

theorem coe_gramGL {R : Matrix (Fin d) (Fin d) K} (hR : Rᵀ = R)
    {W : Submodule K (Fin d → K)} (hW : ∀ v ∈ W, (∀ u ∈ W, v ⬝ᵥ R *ᵥ u = 0) → v = 0)
    {m : ℕ} (u : Module.Basis (Fin m) K W) :
    ((gramGL hR hW u : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = gramMat R u := rfl

end CFSG.ComponentClassification.Burgoyne.O
