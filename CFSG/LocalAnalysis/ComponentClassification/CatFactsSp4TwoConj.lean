module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Classify
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvolutionFusion

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup

variable {K : Type} [Field K]

@[expose] def Rmat (x y : K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks !![x, y + 1; y - 1, -x] !![1 - y, x; x, y + 1] !![-y - 1, x; x, y - 1]
    !![-x, 1 - y; -1 - y, x]

theorem Rmat_symplectic {x y : K} (h : x ^ 2 + y ^ 2 = -1) :
    (Rmat x y)ᵀ * formJ 2 K * Rmat x y = (4 : K) • formJ 2 K := by
  simp only [Rmat, formJ, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_smul]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination 2 * h | linear_combination -2 * h

theorem Rmat_mul_self {x y : K} (h : x ^ 2 + y ^ 2 = -1) :
    Rmat x y * Rmat x y = (-4 : K) • 1 := by
  simp only [Rmat, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp <;>
    first | ring1 | linear_combination 2 * h | linear_combination -2 * h

theorem Rmat_mul_T2 (x y : K) : Rmat x y * kron 1 J₁ = formJ 2 K * Rmat x y := by
  simp only [Rmat, kron, J₁, formJ, fromBlocks_multiply]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp <;> ring1

theorem half_half_four (h2 : (2 : K) ≠ 0) : (2 : K)⁻¹ * (2 : K)⁻¹ * 4 = 1 := by
  field_simp
  norm_num

theorem Rhalf_symplectic (h2 : (2 : K) ≠ 0) {x y : K} (h : x ^ 2 + y ^ 2 = -1) :
    ((2 : K)⁻¹ • Rmat x y)ᵀ * formJ 2 K * ((2 : K)⁻¹ • Rmat x y) = formJ 2 K := by
  rw [transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Rmat_symplectic h, smul_smul, half_half_four h2, one_smul]

@[expose] def Rsp (h2 : (2 : K) ≠ 0) {x y : K} (h : x ^ 2 + y ^ 2 = -1) : StatedSp 2 K :=
  toSp ((2 : K)⁻¹ • Rmat x y) (Rhalf_symplectic h2 h)

theorem Rsp_mul_self (h2 : (2 : K) ≠ 0) {x y : K} (h : x ^ 2 + y ^ 2 = -1) :
    proj 2 K (Rsp h2 h * Rsp h2 h) = 1 := by
  rw [← MonoidHom.mem_ker, ker_proj, mem_spScalars_iff]
  right
  rw [Subgroup.coe_mul, Units.val_mul, Rsp, coe_toSp, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Rmat_mul_self h, smul_smul]
  rw [show (2 : K)⁻¹ * (2 : K)⁻¹ * -4 = -1 by linear_combination -half_half_four h2, neg_one_smul]

@[expose] def J₁SL : Matrix.SpecialLinearGroup (Fin 2) K := ⟨J₁, by simp [J₁, det_fin_two]⟩

theorem diagSL_J₁SL : (((diagSL K J₁SL : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = formJ 2 K := by
  rw [coe_diagSL, formJ_eq_kron]
  rfl

variable (K) in
@[expose] def w0 : StatedProj (StatedSp 2 K) := proj 2 K (diagSL K J₁SL)

theorem w0_mem_Lsub : w0 K ∈ Lsub K := ⟨_, ⟨J₁SL, rfl⟩, rfl⟩

theorem orderOf_w0 : orderOf (w0 K) = 2 := by
  apply orderOf_eq_prime
  · rw [w0, pow_two, ← map_mul, ← map_mul, ← MonoidHom.mem_ker, ker_proj, mem_spScalars_iff]
    right
    change ((diagSL K (J₁SL * J₁SL) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K).val = -1
    rw [coe_diagSL, Matrix.SpecialLinearGroup.coe_mul]
    change kron (J₁ * J₁) 1 = -1
    have hJJ : (J₁ : Matrix (Fin 2) (Fin 2) K) * J₁ = -1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [J₁]
    rw [hJJ, kron_neg_one_one]
  · intro h
    rw [w0, ← MonoidHom.mem_ker, ker_proj, mem_spScalars_iff, diagSL_J₁SL] at h
    rcases h with h | h
    · have := congrFun (congrFun h (Sum.inl 0)) (Sum.inl 0)
      simp [formJ] at this
    · have := congrFun (congrFun h (Sum.inl 0)) (Sum.inl 0)
      simp [formJ] at this

theorem isInvolution_of_orderOf {G : Type*} [Group G] {x : G} (h : orderOf x = 2) :
    BenderSuzuki.PFAppendixIII.IsInvolution x := by
  refine ⟨fun h1 => ?_, by rw [← h, pow_orderOf_eq_one]⟩
  rw [h1, orderOf_one] at h
  norm_num at h

theorem exists_conj_w0 [Finite K] (hpp : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K))
    {w : StatedProj (StatedSp 2 K)} (hw : w ∈ Lsub K) (hord : orderOf w = 2) :
    ∃ l ∈ Lsub K, l * w0 K * l⁻¹ = w := by
  set x := (LEquiv K).symm ⟨w0 K, w0_mem_Lsub⟩
  set y := (LEquiv K).symm ⟨w, hw⟩
  have hx : BenderSuzuki.PFAppendixIII.IsInvolution x := by
    apply isInvolution_of_orderOf
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, orderOf_w0]
  have hy : BenderSuzuki.PFAppendixIII.IsInvolution y := by
    apply isInvolution_of_orderOf
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hord]
  obtain ⟨g, hg⟩ :=
    CFSG.GorensteinWalter.psl2_involutions_conjugate_of_odd_prime_power K hpp x y hx hy
  refine ⟨(LEquiv K g : StatedProj (StatedSp 2 K)), (LEquiv K g).2, ?_⟩
  have h1 := congrArg (fun z => ((LEquiv K z : Lsub K) : StatedProj (StatedSp 2 K))) hg
  simpa [x, y] using h1

theorem exists_involution_conj_u2 [Finite K] (hodd : Odd (Nat.card K))
    (hpp : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K))
    {w : StatedProj (StatedSp 2 K)} (hw : w ∈ Lsub K) (hord : orderOf w = 2) :
    ∃ r : StatedProj (StatedSp 2 K), r * r = 1 ∧ r⁻¹ * u2 K * r = w := by
  have h2 := two_ne_zero_of_odd_card hodd
  obtain ⟨x, y, hxy⟩ := exists_sq_add_sq_eq h2 (-1)
  set R := Rsp h2 hxy with hR
  set r₀ := (proj 2 K R)⁻¹ with hr₀def
  have hr₀ : r₀ * r₀ = 1 := by
    rw [hr₀def, ← _root_.mul_inv_rev, ← map_mul, Rsp_mul_self, inv_one]
  have hRT : R * T2 K = diagSL K J₁SL * R := sp_ext (by
    simp only [Subgroup.coe_mul, Units.val_mul, coe_T2, diagSL_J₁SL, hR, Rsp, coe_toSp,
      Matrix.smul_mul, Matrix.mul_smul, Rmat_mul_T2])
  have hconj : r₀⁻¹ * u2 K * r₀ = w0 K := by
    rw [hr₀def, inv_inv, u2, w0, ← map_inv, ← map_mul, ← map_mul, hRT, mul_inv_cancel_right]
  obtain ⟨l, hl, hlw⟩ := exists_conj_w0 hpp hw hord
  have hlu : l⁻¹ * u2 K * l = u2 K := by
    have := mem_centralizer_singleton_iff.mp (Lsub_le_centralizer hl)
    rw [mul_assoc, ← this, inv_mul_cancel_left]
  refine ⟨l * r₀ * l⁻¹, ?_, ?_⟩
  · calc l * r₀ * l⁻¹ * (l * r₀ * l⁻¹) = l * (r₀ * r₀) * l⁻¹ := by group
      _ = 1 := by rw [hr₀, mul_one, mul_inv_cancel]
  · calc (l * r₀ * l⁻¹)⁻¹ * u2 K * (l * r₀ * l⁻¹) = l * (r₀⁻¹ * (l⁻¹ * u2 K * l) * r₀) * l⁻¹ := by
          group
      _ = w := by rw [hlu, hconj, hlw]

end CFSG.ComponentClassification.CatFactsSp4
