module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.G2VecAction
public import CFSG.LieType.Chevalley.LangRootRankOne

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  RootOps
open scoped commutatorElement

section Generation

variable
  {K : Type} [Field K]

theorem M_val : (((uSL (1 : K) * vSL (-1) * uSL 2 : SL2 K)) : Matrix (Fin 2) (Fin 2) K) =
    !![0, 1; -1, -1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  show !![1, 1; 0, 1] * !![1, 0; -1, 1] * !![(1 : K), 2; 0, 1] = _
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_two]; try ring)

theorem M_cube : (uSL (1 : K) * vSL (-1) * uSL 2) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, M_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

theorem weylElt_one_eq (i : Fin Tag.G2.rank) :
    weylElt .G2 K i 1 = xUnit .G2 K i 1 * yUnit .G2 K i (-1) * xUnit .G2 K i 1 := by
  refine Units.ext ?_
  simp only [Units.val_mul]
  show xOp .G2 K i ((1 : Kˣ) : K) * yOp .G2 K i (-(((1 : Kˣ)⁻¹ : Kˣ) : K)) *
    xOp .G2 K i ((1 : Kˣ) : K) = _
  simp [xUnit, yUnit]

@[expose] def zr (K : Type) [Field K] : ModGL .G2 K := weylElt .G2 K iR 1 * xUnit .G2 K iR 1

theorem gR_eq : gR = Pi.single iR 1 := by funext j; fin_cases j <;> rfl

theorem xUnit_iR (c : K) : xUnit .G2 K iR c = pinnedX .G2 K gR c := by
  rw [gR_eq, pinnedX_single]

theorem zr_eq_rho : zr K = simpleRootSL2 .G2 K iR (uSL 1 * vSL (-1) * uSL 2) := by
  rw [map_mul, map_mul, simpleRootSL2_uSL, simpleRootSL2_vSL, simpleRootSL2_uSL]
  unfold zr
  rw [weylElt_one_eq, mul_assoc, ← xUnit_add, show (1 : K) + 1 = 2 from one_add_one_eq_two]

theorem zr_pow_three : zr K ^ 3 = 1 := by
  rw [zr_eq_rho, ← map_pow, M_cube, map_one]

theorem zr_normalizes : ∀ q ∈ Qg K, zr K * q * (zr K)⁻¹ ∈ Qg K := by
  intro q hq
  have h1 := Xr_normalizes (1 : K) q hq
  have h2 := nR_normalizes _ h1
  have e : zr K * q * (zr K)⁻¹ = weylElt .G2 K iR 1 *
      (pinnedX .G2 K gR 1 * q * (pinnedX .G2 K gR 1)⁻¹) * (weylElt .G2 K iR 1)⁻¹ := by
    unfold zr; rw [xUnit_iR]; group
  rw [e]; exact h2

theorem zr_Z_fixed : ∀ z ∈ Zg K, zr K * z * (zr K)⁻¹ = z := by
  intro z hz
  obtain ⟨c, rfl⟩ := mem_Zg.1 hz
  have e : zr K * pinnedX .G2 K gC c * (zr K)⁻¹ = weylElt .G2 K iR 1 *
      (pinnedX .G2 K gR 1 * pinnedX .G2 K gC c * (pinnedX .G2 K gR 1)⁻¹) *
        (weylElt .G2 K iR 1)⁻¹ := by
    unfold zr; rw [xUnit_iR]; group
  rw [e, conj_eq_of_mul_comm (commute_r_c 1 c).eq, nR_c]

theorem Z_no_three_torsion (h3 : (3 : K) ≠ 0) :
    ∀ z ∈ Zg K, z ^ 3 = 1 → z = 1 := by
  intro z hz hz3
  obtain ⟨c, rfl⟩ := mem_Zg.1 hz
  have : pinnedX .G2 K gC (3 * c) = pinnedX .G2 K gC 0 := by
    rw [pinnedX_zero .G2 K gC, ← hz3, pow_succ, pow_two, ← pinnedX_add .G2 K gC, ← pinnedX_add .G2 K gC]
    congr 1; ring
  have h := pinnedX_injective .G2 K gC this
  have : c = 0 := by
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h h3
    · exact h
  rw [this, pinnedX_zero .G2 K gC]

theorem Qg_le_adjointGroup : Qg K ≤ adjointGroup .G2 K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨γ, -, c, rfl⟩
  exact pinnedX_mem_adjointGroup _ _

theorem clsT_inv {g : ModGL .G2 K} (hg : g ∈ Qg K) : clsT g⁻¹ = -clsT g := by
  have := clsT_mul (Subgroup.inv_mem _ hg) hg
  rw [inv_mul_cancel, clsT_Z (Zg K).one_mem] at this
  exact eq_neg_of_add_eq_zero_left this.symm

theorem clsT_one : clsT (1 : ModGL .G2 K) = 0 := clsT_Z (Zg K).one_mem

theorem clsT_zr_conj {g : ModGL .G2 K} (hg : g ∈ Qg K) :
    clsT (zr K * g * (zr K)⁻¹) = cn (cx 1 (clsT g)) := by
  have h1 := Xr_normalizes (1 : K) g hg
  have e : zr K * g * (zr K)⁻¹ = weylElt .G2 K iR 1 *
      (pinnedX .G2 K gR 1 * g * (pinnedX .G2 K gR 1)⁻¹) * (weylElt .G2 K iR 1)⁻¹ := by
    unfold zr; rw [xUnit_iR]; group
  rw [e, ← cn_clsT h1, ← cx_clsT 1 hg]

theorem norm_vec (s : K) :
    ((s, 0, 0, 0) : K × K × K × K) + Nmat (Xmat 1 ((s, 0, 0, 0) : K × K × K × K)) +
      Nmat (Xmat 1 (Nmat (Xmat 1 ((s, 0, 0, 0) : K × K × K × K)))) = (0, -s, -s, 0) := by
  simp only [Xmat, Nmat, Prod.mk_add_mk]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> (simp; try ring)

theorem extract_vec (s : K) :
    Xmat 1 ((0, -s, -s, 0) : K × K × K × K) + Xmat (-1) ((0, -s, -s, 0) : K × K × K × K) -
      (0, -s, -s, 0) - (0, -s, -s, 0) = (0, 0, 0, 6 * s) := by
  simp only [Xmat, Prod.mk_add_mk, Prod.mk_sub_mk]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> (simp; try ring)

@[expose] def vecHom (K : Type) [Field K] : (K × K × K × K) →+ V (Qg K) (Zg K) :=
  AddMonoidHom.mk' vec vec_add

theorem vecHom_apply (c : K × K × K × K) : vecHom K c = vec c := rfl

theorem vec_E (s : K) : vec ((s, 0, 0, 0) : K × K × K × K) = clsT (pinnedX .G2 K gA s) := by
  simp [vec, th_apply, pinnedX_zero .G2 K, clsT_one]

theorem clsT_conj_vec {g : ModGL .G2 K} (hg : g ∈ Qg K) (c : K × K × K × K)
    (hc : clsT g = vec c) : clsT (zr K * g * (zr K)⁻¹) = vec (Nmat (Xmat 1 c)) := by
  rw [clsT_zr_conj hg, hc, cx_vec, cn_vec]

theorem clsT_norm (s : K) :
    clsT (pinnedX .G2 K gA s * (zr K * pinnedX .G2 K gA s * (zr K)⁻¹) *
      (zr K * (zr K * pinnedX .G2 K gA s * (zr K)⁻¹) * (zr K)⁻¹)) = vec ((0, -s, -s, 0) : K × K × K × K) := by
  have hq := X_mem_Qg (K := K) isQRoot_a s
  have hy1 := zr_normalizes _ hq
  have hy2 := zr_normalizes _ hy1
  have c0 : clsT (pinnedX .G2 K gA s) = vec ((s, 0, 0, 0) : K × K × K × K) := (vec_E s).symm
  have c1 := clsT_conj_vec hq _ c0
  have c2 := clsT_conj_vec hy1 _ c1
  rw [clsT_mul (Subgroup.mul_mem _ hq hy1) hy2, clsT_mul hq hy1, c0, c1, c2, ← vec_add, ← vec_add,
    norm_vec]

theorem Xb_mem_of (H : Subgroup (ModGL .G2 K))
    (hXr : ∀ t : K, pinnedX .G2 K gR t ∈ H) (hZ : ∀ t : K, pinnedX .G2 K gC t ∈ H)
    (hcent : ∀ g ∈ Qg K, zr K * g * (zr K)⁻¹ = g → g ∈ H) (h3 : (3 : K) ≠ 0) (s : K) :
    pinnedX .G2 K gB (6 * s) ∈ H := by
  have hq := X_mem_Qg (K := K) isQRoot_a s
  obtain ⟨huQ, hufix⟩ := norm_fixed classTwoG2 zr_pow_three zr_normalizes zr_Z_fixed
    (Z_no_three_torsion h3) hq
  set u := pinnedX .G2 K gA s * (zr K * pinnedX .G2 K gA s * (zr K)⁻¹) *
      (zr K * (zr K * pinnedX .G2 K gA s * (zr K)⁻¹) * (zr K)⁻¹) with hu
  have huH : u ∈ H := hcent u huQ hufix
  have cu : clsT u = vec ((0, -s, -s, 0) : K × K × K × K) := clsT_norm s
  set x1 := pinnedX .G2 K gR 1
  set x2 := pinnedX .G2 K gR (-1)
  have e1 := Xr_normalizes (1 : K) u huQ
  have e2 := Xr_normalizes (-1 : K) u huQ
  set h := (x1 * u * x1⁻¹) * (x2 * u * x2⁻¹) * u⁻¹ * u⁻¹ with hh
  have hhH : h ∈ H := by
    refine H.mul_mem (H.mul_mem (H.mul_mem ?_ ?_) (H.inv_mem huH)) (H.inv_mem huH)
    · exact H.mul_mem (H.mul_mem (hXr 1) huH) (H.inv_mem (hXr 1))
    · exact H.mul_mem (H.mul_mem (hXr (-1)) huH) (H.inv_mem (hXr (-1)))
  have hhQ : h ∈ Qg K :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ e1 e2) (Subgroup.inv_mem _ huQ))
      (Subgroup.inv_mem _ huQ)
  have ch : clsT h = vec ((0, 0, 0, 6 * s) : K × K × K × K) := by
    have k1 := cx_clsT (1 : K) huQ
    have k2 := cx_clsT (-1 : K) huQ
    rw [hh, clsT_mul (Subgroup.mul_mem _ (Subgroup.mul_mem _ e1 e2) (Subgroup.inv_mem _ huQ))
        (Subgroup.inv_mem _ huQ),
      clsT_mul (Subgroup.mul_mem _ e1 e2) (Subgroup.inv_mem _ huQ), clsT_mul e1 e2,
      clsT_inv huQ, ← k1, ← k2, cu, cx_vec, cx_vec, ← extract_vec s]
    simp only [← vecHom_apply, map_add, map_sub]
    abel
  have cb : clsT (pinnedX .G2 K gB (6 * s)) = vec ((0, 0, 0, 6 * s) : K × K × K × K) := by
    simp [vec, th_apply, pinnedX_zero .G2 K, clsT_one]
  have hbQ := X_mem_Qg (K := K) isQRoot_b (6 * s)
  have hz := (clsT_eq_iff hbQ hhQ).1 (cb.trans ch.symm)
  obtain ⟨c, hc⟩ := mem_Zg.1 hz
  have : pinnedX .G2 K gB (6 * s) = h * (pinnedX .G2 K gC c)⁻¹ := by
    rw [← hc]; group
  rw [this]
  exact H.mul_mem hhH (H.inv_mem (hZ c))

theorem extract_vec_two (h2 : (2 : K) = 0) (t s : K) :
    Xmat t ((0, -s, -s, 0) : K × K × K × K) - (0, -s, -s, 0) = (0, 0, 0, 3 * t * (t - 1) * s) := by
  simp only [Xmat, Prod.mk_sub_mk]
  refine Prod.ext (by simp) (Prod.ext (by simp) (Prod.ext ?_ (by simp only; ring)))
  simp only
  linear_combination (t * s) * h2

theorem Xb_mem_of_two (H : Subgroup (ModGL .G2 K))
    (hXr : ∀ t : K, pinnedX .G2 K gR t ∈ H) (hZ : ∀ t : K, pinnedX .G2 K gC t ∈ H)
    (hcent : ∀ g ∈ Qg K, zr K * g * (zr K)⁻¹ = g → g ∈ H) (h2 : (2 : K) = 0) (h3 : (3 : K) ≠ 0)
    (t s : K) : pinnedX .G2 K gB (3 * t * (t - 1) * s) ∈ H := by
  have hq := X_mem_Qg (K := K) isQRoot_a s
  obtain ⟨huQ, hufix⟩ := norm_fixed classTwoG2 zr_pow_three zr_normalizes zr_Z_fixed
    (Z_no_three_torsion h3) hq
  set u := pinnedX .G2 K gA s * (zr K * pinnedX .G2 K gA s * (zr K)⁻¹) *
      (zr K * (zr K * pinnedX .G2 K gA s * (zr K)⁻¹) * (zr K)⁻¹) with hu
  have huH : u ∈ H := hcent u huQ hufix
  have cu : clsT u = vec ((0, -s, -s, 0) : K × K × K × K) := clsT_norm s
  have e1 := Xr_normalizes t u huQ
  set h := pinnedX .G2 K gR t * u * (pinnedX .G2 K gR t)⁻¹ * u⁻¹ with hh
  have hhH : h ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem (hXr t) huH) (H.inv_mem (hXr t))) (H.inv_mem huH)
  have hhQ : h ∈ Qg K := Subgroup.mul_mem _ e1 (Subgroup.inv_mem _ huQ)
  have ch : clsT h = vec ((0, 0, 0, 3 * t * (t - 1) * s) : K × K × K × K) := by
    rw [hh, clsT_mul e1 (Subgroup.inv_mem _ huQ), clsT_inv huQ, ← cx_clsT t huQ, cu, cx_vec,
      ← extract_vec_two h2 t s]
    simp only [← vecHom_apply, map_sub]
    abel
  have cb : clsT (pinnedX .G2 K gB (3 * t * (t - 1) * s)) =
      vec ((0, 0, 0, 3 * t * (t - 1) * s) : K × K × K × K) := by
    simp [vec, th_apply, pinnedX_zero .G2 K, clsT_one]
  have hbQ := X_mem_Qg (K := K) isQRoot_b (3 * t * (t - 1) * s)
  obtain ⟨c, hc⟩ := mem_Zg.1 ((clsT_eq_iff hbQ hhQ).1 (cb.trans ch.symm))
  have : pinnedX .G2 K gB (3 * t * (t - 1) * s) = h * (pinnedX .G2 K gC c)⁻¹ := by
    rw [← hc]; group
  rw [this]
  exact H.mul_mem hhH (H.inv_mem (hZ c))

end Generation

end CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport
