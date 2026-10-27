module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIClassicalConfig
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIILinearRigid
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLInnerInvolution
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner

public section

namespace CFSG.ComponentClassification.RankTwoHypIILinear

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoHypIIY
  CFSG.ComponentClassification.RankTwoHypIIClassical FourGroupEvenCanonical
  CFSG.ComponentClassification.UnbalancedCatalog.NonalternatingRadical

variable {K : Type} [Field K] {n : ℕ}

section Vectors

theorem exists_dotProduct_eq_one [CharP K 2] (hn : 1 ≤ n) {u : Fin n → K}
    (hnd : ¬ ∃ a : K, u = a • onesVec) :
    ∃ z : Fin n → K, onesVec ⬝ᵥ z = 0 ∧ u ⬝ᵥ z = 1 := by
  have hij : ∃ i j, u i ≠ u j := by
    by_contra h
    push Not at h
    exact hnd ⟨u ⟨0, by omega⟩, funext fun k => by
      rw [Pi.smul_apply, onesVec_apply, smul_eq_mul, mul_one, h k ⟨0, by omega⟩]⟩
  obtain ⟨i, j, hij⟩ := hij
  have hne : i ≠ j := fun h => hij (h ▸ rfl)
  have hsum : u i + u j ≠ 0 := by
    intro h
    exact hij (by rwa [CharTwo.add_eq_zero] at h)
  refine ⟨(u i + u j)⁻¹ • (Pi.single i 1 + Pi.single j 1), ?_, ?_⟩
  · rw [dotProduct_smul, dotProduct_add, onesVec_dotProduct_single, onesVec_dotProduct_single,
      CharTwo.add_self_eq_zero, smul_zero]
  · rw [dotProduct_smul, dotProduct_add, dotProduct_single, dotProduct_single, mul_one, mul_one,
      smul_eq_mul, inv_mul_cancel₀ hsum]

theorem exists_perp_not_mem_span [Finite K] (hn : 5 ≤ n) (u z : Fin n → K) :
    ∃ y : Fin n → K, onesVec ⬝ᵥ y = 0 ∧ u ⬝ᵥ y = 0 ∧ z ⬝ᵥ y = 0 ∧
      ¬ ∃ a : K, y = a • onesVec := by
  set Φ : (Fin n → K) →ₗ[K] (Fin 3 → K) :=
    Matrix.mulVecLin (Matrix.of ![(onesVec : Fin n → K), u, z]) with hΦ
  have hker : ∀ y, y ∈ LinearMap.ker Φ ↔ onesVec ⬝ᵥ y = 0 ∧ u ⬝ᵥ y = 0 ∧ z ⬝ᵥ y = 0 := by
    intro y
    rw [LinearMap.mem_ker, hΦ, Matrix.mulVecLin_apply]
    constructor
    · intro h
      refine ⟨?_, ?_, ?_⟩
      · have := congrFun h 0
        simpa [Matrix.mulVec, Matrix.of_apply] using this
      · have := congrFun h 1
        simpa [Matrix.mulVec, Matrix.of_apply] using this
      · have := congrFun h 2
        simpa [Matrix.mulVec, Matrix.of_apply] using this
    · rintro ⟨h0, h1, h2⟩
      funext k
      fin_cases k <;> simp [Matrix.mulVec, Matrix.of_apply, h0, h1, h2]
  by_contra hcon
  push Not at hcon
  have hle : LinearMap.ker Φ ≤ Submodule.span K {(onesVec : Fin n → K)} := by
    intro y hy
    obtain ⟨h0, h1, h2⟩ := (hker y).mp hy
    by_contra hy'
    obtain ⟨a, ha⟩ := hcon y h0 h1 h2
    exact hy' (ha ▸ Submodule.smul_mem _ a (Submodule.subset_span rfl))
  have h1 := Submodule.finrank_mono hle
  have h2 : Module.finrank K (Submodule.span K {(onesVec : Fin n → K)}) ≤ 1 := by
    have hne : (onesVec : Fin n → K) ≠ 0 := fun h => by
      have := congrFun h ⟨0, by omega⟩
      simp [onesVec_apply] at this
    rw [finrank_span_singleton hne]
  have h3 := LinearMap.finrank_range_add_finrank_ker Φ
  have h4 : Module.finrank K (LinearMap.range Φ) ≤ 3 := by
    have := Submodule.finrank_le (LinearMap.range Φ)
    rwa [Module.finrank_fin_fun] at this
  rw [Module.finrank_fin_fun] at h3
  omega

end Vectors

section Isometries

@[expose] def isoTransvMat (w : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  1 + vecMulVec w w

theorem isoTransvMat_mulVec (w x : Fin n → K) :
    isoTransvMat w *ᵥ x = x + (w ⬝ᵥ x) • w := by
  simp only [isoTransvMat, add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul]

theorem isoTransvMat_transpose (w : Fin n → K) : (isoTransvMat w)ᵀ = isoTransvMat w := by
  rw [isoTransvMat, transpose_add, transpose_one, transpose_vecMulVec]

theorem isoTransvMat_mul_self [CharP K 2] {w : Fin n → K} (hw : onesVec ⬝ᵥ w = 0) :
    isoTransvMat w * isoTransvMat w = 1 := by
  have hww : w ⬝ᵥ w = 0 := by rw [dotProduct_self_eq_sq, hw, zero_pow two_ne_zero]
  have h2 : ∀ M : Matrix (Fin n) (Fin n) K, M + M = 0 := fun M => by
    rw [← two_smul K M, CharTwo.two_eq_zero, zero_smul]
  simp only [isoTransvMat, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one,
    vecMulVec_mul_vecMulVec, hww, zero_smul, vecMulVec_zero, add_zero]
  rw [add_assoc, h2, add_zero]

variable [CharP K 2]

@[expose] def isoTransvGL {w : Fin n → K} (hw : onesVec ⬝ᵥ w = 0) : GL (Fin n) K :=
  ⟨isoTransvMat w, isoTransvMat w, isoTransvMat_mul_self hw, isoTransvMat_mul_self hw⟩

theorem coe_isoTransvGL {w : Fin n → K} (hw : onesVec ⬝ᵥ w = 0) :
    (isoTransvGL hw : Matrix (Fin n) (Fin n) K) = isoTransvMat w := rfl

theorem isoTransvGL_mem {w : Fin n → K} (hw : onesVec ⬝ᵥ w = 0) :
    isoTransvGL hw ∈ matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) K) := by
  rw [mem_matrixIsometryGroup, Matrix.mul_one, coe_isoTransvGL, isoTransvMat_transpose,
    isoTransvMat_mul_self hw]

end Isometries

section RadMem

variable (K) in
@[expose] def RadMem (N : Subgroup (MulAut (projectiveSL n K))) (u : Fin n → K) (c : K) : Prop :=
  ∃ g : GL (Fin n) K, (g : Matrix (Fin n) (Fin n) K) = radicalMatrix u c ∧ conjAut n K g ∈ N

variable {N : Subgroup (MulAut (projectiveSL n K))}

theorem RadMem.congr {u u' : Fin n → K} {c c' : K} (h : RadMem K N u c) (hu : u = u')
    (hc : c = c') : RadMem K N u' c' := hu ▸ hc ▸ h

variable [CharP K 2]

namespace RadMem

theorem mul (hev : Even n) {u u' : Fin n → K} {c c' : K} (h : RadMem K N u c)
    (h' : RadMem K N u' c') (hu : onesVec ⬝ᵥ u = 0) (hu' : onesVec ⬝ᵥ u' = 0) :
    RadMem K N (u + u') (c + c' + u ⬝ᵥ u') := by
  obtain ⟨g, hg, hgN⟩ := h
  obtain ⟨g', hg', hg'N⟩ := h'
  refine ⟨g * g', ?_, ?_⟩
  · rw [Units.val_mul, hg, hg', radicalMatrix_mul c c' (onesVec_dotProduct_onesVec hev) hu hu']
  · rw [map_mul]
    exact mul_mem hgN hg'N

theorem conj {u w : Fin n → K} {c : K} (h : RadMem K N u c)
    (hN : ∀ g ∈ matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) K), ∀ x ∈ N,
      conjAut n K g * x * (conjAut n K g)⁻¹ ∈ N)
    (hw : onesVec ⬝ᵥ w = 0) : RadMem K N (u + (w ⬝ᵥ u) • w) c := by
  obtain ⟨g, hg, hgN⟩ := h
  refine ⟨isoTransvGL hw * g * (isoTransvGL hw)⁻¹, ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, hg, conj_radicalMatrix (isoTransvGL_mem hw),
      coe_isoTransvGL, isoTransvMat_mulVec]
  · rw [map_mul, map_mul, map_inv]
    exact hN _ (isoTransvGL_mem hw) _ hgN

theorem add_smul_onesVec {u : Fin n → K} {c : K} (h : RadMem K N u c) (a : K) :
    RadMem K N (u + a • onesVec) c := by
  obtain ⟨g, hg, hgN⟩ := h
  exact ⟨g, by rw [hg, radicalMatrix_add_smul_onesVec], hgN⟩

omit [CharP K 2] in
theorem vec_add_self [CharP K 2] (u : Fin n → K) : u + u = 0 :=
  funext fun j => by rw [Pi.add_apply, CharTwo.add_self_eq_zero, Pi.zero_apply]

variable [Finite K] (hev : Even n)
  (hN : ∀ g ∈ matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) K), ∀ x ∈ N,
    conjAut n K g * x * (conjAut n K g)⁻¹ ∈ N)
include hev hN

theorem of_dotProduct_ne_zero {u z : Fin n → K} {c : K} (h : RadMem K N u c)
    (hu : onesVec ⬝ᵥ u = 0) (hz : onesVec ⬝ᵥ z = 0) (huz : u ⬝ᵥ z ≠ 0) :
    RadMem K N z (u ⬝ᵥ z) := by
  obtain ⟨β, hβ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (u ⬝ᵥ z)
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hβ
    exact huz hβ
  have hw0 : onesVec ⬝ᵥ (β⁻¹ • z) = 0 := by rw [dotProduct_smul, hz, smul_zero]
  have hwu : ((β⁻¹ • z) ⬝ᵥ u) • (β⁻¹ • z) = z := by
    rw [smul_dotProduct, dotProduct_comm z u, hβ, smul_eq_mul, smul_smul,
      show β⁻¹ * (β * β) * β⁻¹ = 1 by field_simp, one_smul]
  have h1 : RadMem K N (u + z) c := (h.conj hN hw0).congr (by rw [hwu]) rfl
  have h2 := h.mul hev h1 hu (by rw [dotProduct_add, hu, hz, add_zero])
  refine h2.congr ?_ ?_
  · rw [← add_assoc, vec_add_self, zero_add]
  · rw [CharTwo.add_self_eq_zero, zero_add, dotProduct_add, dotProduct_self_eq_sq, hu,
      zero_pow two_ne_zero, zero_add]

theorem smul {u z : Fin n → K} {c : K} (h : RadMem K N u c) (hu : onesVec ⬝ᵥ u = 0)
    (hz : onesVec ⬝ᵥ z = 0) (huz : u ⬝ᵥ z = 1) (κ : K) : RadMem K N (κ • u) κ := by
  have huu : u ⬝ᵥ u = 0 := by rw [dotProduct_self_eq_sq, hu, zero_pow two_ne_zero]
  have hzz : z ⬝ᵥ z = 0 := by rw [dotProduct_self_eq_sq, hz, zero_pow two_ne_zero]
  have h1 := h.of_dotProduct_ne_zero hev hN hu hz (by rw [huz]; exact one_ne_zero)
  have hz' : onesVec ⬝ᵥ (z + κ • u) = 0 := by
    rw [dotProduct_add, dotProduct_smul, hz, hu, smul_zero, add_zero]
  have huz' : u ⬝ᵥ (z + κ • u) = 1 := by
    rw [dotProduct_add, dotProduct_smul, huz, huu, smul_zero, add_zero]
  have h2 := h.of_dotProduct_ne_zero hev hN hu hz' (by rw [huz']; exact one_ne_zero)
  have h3 := h1.mul hev h2 hz hz'
  refine h3.congr ?_ ?_
  · rw [← add_assoc, vec_add_self, zero_add]
  · rw [huz', huz, CharTwo.add_self_eq_zero, zero_add, dotProduct_add, hzz, zero_add,
      dotProduct_smul, dotProduct_comm z u, huz, smul_eq_mul, mul_one]

theorem of_ne_zero {u z : Fin n → K} {c : K} (h : RadMem K N u c) (hu : onesVec ⬝ᵥ u = 0)
    (hz : onesVec ⬝ᵥ z = 0) (huz : u ⬝ᵥ z = 1) {μ : K} (hμ : μ ≠ 0) : RadMem K N u μ := by
  have h1 := h.smul hev hN hu hz huz μ⁻¹
  have hu1 : onesVec ⬝ᵥ (μ⁻¹ • u) = 0 := by rw [dotProduct_smul, hu, smul_zero]
  have hz1 : onesVec ⬝ᵥ (μ • z) = 0 := by rw [dotProduct_smul, hz, smul_zero]
  have huz1 : (μ⁻¹ • u) ⬝ᵥ (μ • z) = 1 := by
    rw [smul_dotProduct, dotProduct_smul, huz, smul_eq_mul, smul_eq_mul, mul_one,
      inv_mul_cancel₀ hμ]
  have h2 := h1.smul hev hN hu1 hz1 huz1 μ
  exact h2.congr (by rw [smul_smul, mul_inv_cancel₀ hμ, one_smul]) rfl

theorem exists_root (hn : 4 ≤ n) (hq : 4 ≤ Nat.card K ∨ 5 ≤ n) {u : Fin n → K} {c : K}
    (h : RadMem K N u c) (hu : onesVec ⬝ᵥ u = 0)
    (hne : (¬ ∃ a : K, u = a • onesVec) ∨ c ≠ 0) : ∃ μ : K, μ ≠ 0 ∧ RadMem K N 0 μ := by
  by_cases hd : ∃ a : K, u = a • onesVec
  · obtain ⟨a, rfl⟩ := hd
    have hc : c ≠ 0 := hne.resolve_left (not_not.mpr ⟨a, rfl⟩)
    refine ⟨c, hc, ?_⟩
    exact (h.add_smul_onesVec a).congr (by rw [← add_smul, CharTwo.add_self_eq_zero, zero_smul])
      rfl
  have key : ∀ (y : Fin n → K) (l : K), RadMem K N y l → onesVec ⬝ᵥ y = 0 →
      (¬ ∃ a : K, y = a • onesVec) → l ≠ 1 → ∃ μ : K, μ ≠ 0 ∧ RadMem K N 0 μ := by
    intro y l hy hy0 hyd hl
    obtain ⟨z, hz, hyz⟩ := exists_dotProduct_eq_one (by omega) hyd
    have h1 := hy.of_ne_zero hev hN hy0 hz hyz one_ne_zero
    have h2 := hy.mul hev h1 hy0 hy0
    refine ⟨l + 1, fun h0 => hl (CharTwo.add_eq_zero.mp h0), h2.congr (vec_add_self y) ?_⟩
    rw [dotProduct_self_eq_sq, hy0, zero_pow two_ne_zero, add_zero]
  by_cases hc1 : c = 1
  · subst hc1
    obtain ⟨z, hz, huz⟩ := exists_dotProduct_eq_one (by omega) hd
    rcases hq with hq | hq
    ·
      obtain ⟨μ, hμ0, hμ1⟩ : ∃ μ : K, μ ≠ 0 ∧ μ ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have hsurj : Function.Surjective (fun b : Bool => if b then (1 : K) else 0) := by
          intro x
          by_cases hx : x = 0
          · exact ⟨false, by simp [hx]⟩
          · exact ⟨true, by simp [hcon x hx]⟩
        have := Nat.card_le_card_of_surjective _ hsurj
        rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
        omega
      exact key u μ (h.of_ne_zero hev hN hu hz huz hμ0) hu hd hμ1
    ·
      obtain ⟨y, hy0, huy, hzy, hyd⟩ := exists_perp_not_mem_span hq u z
      have h1 := h.of_dotProduct_ne_zero hev hN hu hz (by rw [huz]; exact one_ne_zero)
      have hzy0 : onesVec ⬝ᵥ (z + y) = 0 := by rw [dotProduct_add, hz, hy0, add_zero]
      have huzy : u ⬝ᵥ (z + y) = 1 := by rw [dotProduct_add, huz, huy, add_zero]
      have h2 := h.of_dotProduct_ne_zero hev hN hu hzy0 (by rw [huzy]; exact one_ne_zero)
      have h3 := h1.mul hev h2 hz hzy0
      have hzz : z ⬝ᵥ z = 0 := by rw [dotProduct_self_eq_sq, hz, zero_pow two_ne_zero]
      have h4 : RadMem K N y 0 := h3.congr (by rw [← add_assoc, vec_add_self, zero_add]) (by
        rw [huzy, huz, CharTwo.add_self_eq_zero, zero_add, dotProduct_add, hzz, hzy, add_zero])
      exact key y 0 h4 hy0 hyd zero_ne_one
  · exact key u c h hu hd hc1

end RadMem

end RadMem

section Commutator

theorem conjAut_mem_inner_of_det {g : GL (Fin n) K} (h : (g : Matrix (Fin n) (Fin n) K).det = 1) :
    conjAut n K g ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  let g' : SpecialLinearGroup (Fin n) K := ⟨(g : Matrix (Fin n) (Fin n) K), h⟩
  refine ⟨proj n K g', ?_⟩
  rw [← conjAut_toGL]
  exact congrArg (conjAut n K) (Units.ext rfl)

theorem conjAut_mem_inner_of_det_eq_pow {g : GL (Fin n) K} {t : Kˣ}
    (h : (g : Matrix (Fin n) (Fin n) K).det = (t : K) ^ n) :
    conjAut n K g ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range :=
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_mem_range_conj_of_det_eq_pow (Units.ext (by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_pow_eq_pow_val]; exact h))

theorem conjAut_commutator_dualAut (g : GL (Fin n) K) :
    conjAut n K g * dualAut n K * (conjAut n K g)⁻¹ * (dualAut n K)⁻¹ =
      conjAut n K (g * GeneralLinearGroup.inverseTranspose g⁻¹) := by
  obtain ⟨-, -, -, hδδ, hδc, -⟩ := standard_automorphism_transport (K := K) (n := n)
  have hδinv : (dualAut n K)⁻¹ = dualAut n K := inv_eq_of_mul_eq_one_right hδδ
  rw [hδinv, map_mul, ← hδc g⁻¹, map_inv]
  group

theorem coe_mul_inverseTranspose_inv (g : GL (Fin n) K) :
    ((g * GeneralLinearGroup.inverseTranspose g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K)ᵀ := by
  rw [Units.val_mul, GeneralLinearGroup.coe_inverseTranspose, inv_inv]

theorem commutator_mem {E : Subgroup (MulAut (projectiveSL n K))} (hδ : dualAut n K ∈ E)
    {μ : K} {g₀ : GL (Fin n) K} (hg₀ : (g₀ : Matrix (Fin n) (Fin n) K) = radicalMatrix 0 μ)
    (hC : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ⊓
      centralizer {conjAut n K g₀} ≤ normalizer (E : Set (MulAut (projectiveSL n K))))
    {g : GL (Fin n) K} (hg1 : (g : Matrix (Fin n) (Fin n) K) *ᵥ onesVec = onesVec)
    (hg2 : (g : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ onesVec = onesVec)
    (hgX : conjAut n K g ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range) :
    conjAut n K (g * GeneralLinearGroup.inverseTranspose g⁻¹) ∈ E := by
  have hR : radicalMatrix (0 : Fin n → K) μ = 1 + μ • vecMulVec onesVec onesVec := by
    simp [radicalMatrix]
  have hcomm : g * g₀ = g₀ * g := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hg₀, hR, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul, hg1,
      ← mulVec_transpose, hg2]
  have hgC : conjAut n K g ∈ centralizer {conjAut n K g₀} := by
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hcomm]
  have hN := hC ⟨hgX, hgC⟩
  have h1 : conjAut n K g * dualAut n K * (conjAut n K g)⁻¹ ∈ E :=
    (mem_normalizer_iff.mp hN _).mp hδ
  rw [← conjAut_commutator_dualAut]
  exact mul_mem h1 (inv_mem hδ)

end Commutator

section Final

variable (K) in
@[expose] def ev (a : Fin n) : Fin n → K := Pi.single a 1

theorem one_add_smul_vecMulVec_mulVec (s : K) (u w x : Fin n → K) :
    (1 + s • vecMulVec u w) *ᵥ x = x + (s * (w ⬝ᵥ x)) • u := by
  simp only [add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_smul]

theorem one_add_smul_vecMulVec_transpose (s : K) (u w : Fin n → K) :
    (1 + s • vecMulVec u w)ᵀ = 1 + s • vecMulVec w u := by
  rw [transpose_add, transpose_one, transpose_smul, transpose_vecMulVec]

theorem det_one_add_smul_vecMulVec (s : K) (u w : Fin n → K) :
    (1 + s • vecMulVec u w).det = 1 + s * (w ⬝ᵥ u) := by
  rw [show s • vecMulVec u w = vecMulVec (s • u) w by
      ext i j
      simp [vecMulVec_apply, mul_assoc],
    vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, smul_eq_mul]

theorem three_eq_one_of_charTwo [CharP K 2] : (3 : K) = 1 := by
  linear_combination (CharTwo.two_eq_zero : (2 : K) = 0)

theorem four_eq_zero_of_charTwo [CharP K 2] : (4 : K) = 0 := by
  linear_combination (2 : K) * (CharTwo.two_eq_zero : (2 : K) = 0)

theorem eq_one_of_pow_four_eq_one [CharP K 2] {t : K} (h : t ^ 4 = 1) : t = 1 := by
  have h1 : (t + 1) ^ 4 = 0 := by
    linear_combination h + (2 * t ^ 3 + 3 * t ^ 2 + 2 * t + 1) * (CharTwo.two_eq_zero : (2 : K) = 0)
  have h2 : t + 1 = 0 := pow_eq_zero_iff (by norm_num) |>.mp h1
  rwa [CharTwo.add_eq_zero] at h2

theorem exists_ne_zero_ne_one [Finite K] (hq : 4 ≤ Nat.card K) : ∃ t : K, t ≠ 0 ∧ t ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hsurj : Function.Surjective (fun b : Bool => if b then (1 : K) else 0) := by
    intro x
    by_cases hx : x = 0
    · exact ⟨false, by simp [hx]⟩
    · exact ⟨true, by simp [hcon x hx]⟩
  have := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  omega

theorem false_of_root_four [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    {E : Subgroup (MulAut (projectiveSL 4 K))} (hE : CFSG.Open.IsElemAbelian 2 E)
    (hδ : dualAut 4 K ∈ E) {μ : K} {g₀ : GL (Fin 4) K}
    (hg₀ : (g₀ : Matrix (Fin 4) (Fin 4) K) = radicalMatrix 0 μ)
    (hC : (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range ⊓
      centralizer {conjAut 4 K g₀} ≤ normalizer (E : Set (MulAut (projectiveSL 4 K)))) :
    False := by
  obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one hq
  set s : K := t ^ 4 + 1 with hs
  have hs0 : s ≠ 0 := fun h => ht1 (eq_one_of_pow_four_eq_one (CharTwo.add_eq_zero.mp h))
  set u : Fin 4 → K := ev K 1 + ev K 2 with hu
  set w : Fin 4 → K := ev K 1 + ev K 3 with hw
  set A : Matrix (Fin 4) (Fin 4) K := 1 + s • vecMulVec u w with hA
  have hwu : w ⬝ᵥ u = 1 := by simp [hu, hw, ev, dotProduct_add]
  have hdet : A.det = t ^ 4 := by
    rw [hA, det_one_add_smul_vecMulVec, hwu, mul_one, hs, add_comm, add_assoc,
      CharTwo.add_self_eq_zero, add_zero]
  have hdet0 : A.det ≠ 0 := by rw [hdet]; exact pow_ne_zero _ ht0
  set g := GeneralLinearGroup.mkOfDetNeZero A hdet0 with hg
  have hgA : (g : Matrix (Fin 4) (Fin 4) K) = A := rfl
  have hg1 : (g : Matrix (Fin 4) (Fin 4) K) *ᵥ onesVec = onesVec := by
    rw [hgA, hA, one_add_smul_vecMulVec_mulVec]
    simp [hu, hw, ev, onesVec_apply, CharTwo.add_self_eq_zero]
  have hg2 : (g : Matrix (Fin 4) (Fin 4) K)ᵀ *ᵥ onesVec = onesVec := by
    rw [hgA, hA, one_add_smul_vecMulVec_transpose, one_add_smul_vecMulVec_mulVec]
    simp [hu, hw, ev, onesVec_apply, CharTwo.add_self_eq_zero]
  have hgX := conjAut_mem_inner_of_det_eq_pow (g := g) (t := Units.mk0 t ht0)
    (by rw [hgA, hdet]; rfl)
  have hmem := commutator_mem hδ hg₀ hC hg1 hg2 hgX
  have hsq := hE.2 _ hmem
  rw [← map_pow, conjAut_eq_one_iff (by norm_num)] at hsq
  obtain ⟨c, hc⟩ := hsq
  have hval : ((g * GeneralLinearGroup.inverseTranspose g⁻¹ : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = A * Aᵀ := by rw [coe_mul_inverseTranspose_inv, hgA]
  have hmat : (A * Aᵀ) * (A * Aᵀ) = scalar (Fin 4) (c : K) := by
    have := congrArg (fun x : GL (Fin 4) K => (x : Matrix (Fin 4) (Fin 4) K)) hc
    simp only [GeneralLinearGroup.coe_scalar] at this
    rw [this, sq, Units.val_mul, hval]
  have h0 : ((A * Aᵀ) * (A * Aᵀ)) *ᵥ ev K 0 = ev K 0 := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
    simp only [hA, one_add_smul_vecMulVec_transpose, one_add_smul_vecMulVec_mulVec]
    simp [hu, hw, ev]
  have hc1 : (c : K) = 1 := by
    have := congrFun (h0.symm.trans (by rw [hmat])) 0
    simpa [ev, Matrix.scalar_apply] using this.symm
  have h3 : ((A * Aᵀ) * (A * Aᵀ)) *ᵥ ev K 3 = ev K 3 + (s * s) • u := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
    simp only [hA, one_add_smul_vecMulVec_transpose, one_add_smul_vecMulVec_mulVec]
    simp only [hu, hw, ev, dotProduct_add, dotProduct_smul, dotProduct_single]
    ext k
    fin_cases k <;> simp <;> ring_nf <;>
      simp [CharTwo.two_eq_zero, three_eq_one_of_charTwo, four_eq_zero_of_charTwo]
  have h31 := congrFun (h3.symm.trans (by rw [hmat, hc1])) 1
  simp [hu, ev, Matrix.scalar_apply] at h31
  exact hs0 h31

theorem false_of_mul_eq_mul_scalar_six [CharP K 2] (hn : 6 ≤ n) {B₁ B₂ : Matrix (Fin n) (Fin n) K}
    (hB₁ : B₁ = 1 + (1 : K) • vecMulVec (ev K ⟨1, by omega⟩ + ev K ⟨2, by omega⟩)
      (ev K ⟨3, by omega⟩ + ev K ⟨4, by omega⟩))
    (hB₂ : B₂ = 1 + (1 : K) • vecMulVec (ev K ⟨2, by omega⟩ + ev K ⟨3, by omega⟩)
      (ev K ⟨4, by omega⟩ + ev K ⟨5, by omega⟩))
    {c : K} (h : (B₁ * B₁ᵀ) * (B₂ * B₂ᵀ) = (B₂ * B₂ᵀ) * (B₁ * B₁ᵀ) * scalar (Fin n) c) :
    False := by
  subst hB₁ hB₂
  have e0 := congrFun (congrArg (fun M : Matrix (Fin n) (Fin n) K => M *ᵥ ev K ⟨0, by omega⟩) h)
    ⟨0, by omega⟩
  have e4 := congrFun (congrArg (fun M : Matrix (Fin n) (Fin n) K => M *ᵥ ev K ⟨4, by omega⟩) h)
    ⟨1, by omega⟩
  simp only [← mulVec_mulVec, one_add_smul_vecMulVec_transpose, one_add_smul_vecMulVec_mulVec,
    scalar_apply] at e0 e4
  simp [ev, Fin.ext_iff, CharTwo.add_self_eq_zero] at e0 e4
  rw [← e0] at e4
  simp at e4

theorem false_of_root_six [Finite K] [CharP K 2] (hn : 6 ≤ n)
    {E : Subgroup (MulAut (projectiveSL n K))} (hE : CFSG.Open.IsElemAbelian 2 E)
    (hδ : dualAut n K ∈ E) {μ : K} {g₀ : GL (Fin n) K}
    (hg₀ : (g₀ : Matrix (Fin n) (Fin n) K) = radicalMatrix 0 μ)
    (hC : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ⊓
      centralizer {conjAut n K g₀} ≤ normalizer (E : Set (MulAut (projectiveSL n K)))) :
    False := by
  have key : ∀ u w : Fin n → K, w ⬝ᵥ u = 0 → onesVec ⬝ᵥ u = 0 → onesVec ⬝ᵥ w = 0 →
      ∃ g : GL (Fin n) K, (g : Matrix (Fin n) (Fin n) K) = 1 + (1 : K) • vecMulVec u w ∧
        conjAut n K (g * GeneralLinearGroup.inverseTranspose g⁻¹) ∈ E := by
    intro u w hwu hu hw
    have hdet : (1 + (1 : K) • vecMulVec u w).det = 1 := by
      rw [det_one_add_smul_vecMulVec, hwu, mul_zero, add_zero]
    refine ⟨GeneralLinearGroup.mkOfDetNeZero _ (by rw [hdet]; exact one_ne_zero), rfl, ?_⟩
    refine commutator_mem hδ hg₀ hC ?_ ?_ (conjAut_mem_inner_of_det hdet)
    · change (1 + (1 : K) • vecMulVec u w) *ᵥ onesVec = onesVec
      rw [one_add_smul_vecMulVec_mulVec, dotProduct_comm, hw, mul_zero, zero_smul, add_zero]
    · change (1 + (1 : K) • vecMulVec u w)ᵀ *ᵥ onesVec = onesVec
      rw [one_add_smul_vecMulVec_transpose, one_add_smul_vecMulVec_mulVec, dotProduct_comm, hu,
        mul_zero, zero_smul, add_zero]
  obtain ⟨g₁, hg₁, hm₁⟩ := key (ev K ⟨1, by omega⟩ + ev K ⟨2, by omega⟩)
    (ev K ⟨3, by omega⟩ + ev K ⟨4, by omega⟩) (by simp [ev, Fin.ext_iff])
    (by simp [ev, onesVec_apply, CharTwo.add_self_eq_zero])
    (by simp [ev, onesVec_apply, CharTwo.add_self_eq_zero])
  obtain ⟨g₂, hg₂, hm₂⟩ := key (ev K ⟨2, by omega⟩ + ev K ⟨3, by omega⟩)
    (ev K ⟨4, by omega⟩ + ev K ⟨5, by omega⟩) (by simp [ev, Fin.ext_iff])
    (by simp [ev, onesVec_apply, CharTwo.add_self_eq_zero])
    (by simp [ev, onesVec_apply, CharTwo.add_self_eq_zero])
  have hcomm := congrArg Subtype.val (hE.1.is_comm.comm ⟨_, hm₁⟩ ⟨_, hm₂⟩)
  simp only [coe_mul] at hcomm
  rw [← map_mul, ← map_mul, conjAut_eq_conjAut_iff (by omega)] at hcomm
  obtain ⟨c, hc⟩ := hcomm
  have hmat := congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) hc
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at hmat
  rw [← Units.val_mul g₁, ← Units.val_mul g₂, coe_mul_inverseTranspose_inv,
    coe_mul_inverseTranspose_inv] at hmat
  exact false_of_mul_eq_mul_scalar_six hn hg₁ hg₂ hmat

end Final

section Config

variable [Finite K]

theorem dualAut_not_mem_range (hn : 3 ≤ n) :
    dualAut n K ∉ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  rintro ⟨p, hp⟩
  apply ProjectivePlane.dualAut_not_mem_semilinearAutGroup (K := K) hn
  obtain ⟨g, rfl⟩ := proj_surjective n K p
  rw [← hp, ← conjAut_toGL]
  exact mem_semilinearAutGroup_iff.mpr ⟨SpecialLinearGroup.toGL g, 1, by rw [map_one, mul_one]⟩

theorem false_of_config_dualAut {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) (hev : Even n)
    (hn : 4 ≤ n) (h4 : ¬ (n = 4 ∧ m = 1)) {E M : Subgroup (MulAut (projectiveSL n K))}
    (hc : HypIIConfig (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range E M)
    (hδ : dualAut n K ∈ E)
    (hE0 : ∃ e ∈ E, e ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ∧
      e ≠ 1) : False := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  have : Finite (MulAut (projectiveSL n K)) := finite_mulAut_projectiveSL
  set X := (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range with hXdef
  have hXn : X.Normal := (autModel_mulAut (center_projectiveSL_eq_bot K (by omega))).normal
  have hδX : dualAut n K ∉ X := dualAut_not_mem_range (by omega)
  have hδ1 : dualAut n K ≠ 1 := fun h => hδX (h ▸ X.one_mem)
  obtain ⟨r, hr⟩ := hev
  set i : Fin n := ⟨0, by omega⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hRinn, hRC, hRn, hCR, -, hO⟩ :=
    even_linear_nonalternating_graph_radical (K := K) (by omega) hK (r := r) (by omega) hn i
  set R := (radicalGroup (K := K) i).map (conjAut n K) with hRdef
  have hev : Even n := ⟨r, hr⟩
  have hCδ : X ⊓ centralizer {dualAut n K} ≤ normalizer (E : Set (MulAut (projectiveSL n K))) :=
    hc.centralizer_le_normalizer hXn hδ hδ1 (hO X le_rfl)
  have hE₀N : ∀ x ∈ X ⊓ centralizer {dualAut n K}, ∀ y ∈ E ⊓ X, x * y * x⁻¹ ∈ E ⊓ X := by
    intro x hx y hy
    exact ⟨(mem_normalizer_iff.mp (hCδ hx) y).mp hy.1, hXn.conj_mem y hy.2 x⟩
  have hRN : ∀ x ∈ centralizer {dualAut n K}, ∀ y ∈ R, x * y * x⁻¹ ∈ R := by
    intro x hx y hy
    have := hRn.conj_mem ⟨y, hRC hy⟩ (mem_subgroupOf.mpr hy) ⟨x, hx⟩
    rwa [mem_subgroupOf] at this
  have hE₀δ : E ⊓ X ≤ centralizer {dualAut n K} := fun y hy => hc.le_centralizer hδ hy.1
  obtain ⟨x, ⟨hxE₀, hxR⟩, hx1⟩ : ∃ x ∈ (E ⊓ X) ⊓ R, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨e, heE, heX, he1⟩ := hE0
    apply he1
    have heC : e ∈ centralizer {dualAut n K} ⊓
        centralizer (R : Set (MulAut (projectiveSL n K))) := by
      refine mem_inf.mpr ⟨hE₀δ ⟨heE, heX⟩, ?_⟩
      rw [mem_centralizer_iff]
      intro y hy
      have h1 : e * y * e⁻¹ * y⁻¹ ∈ (E ⊓ X) ⊓ R := by
        refine Subgroup.mem_inf.mpr ⟨?_, R.mul_mem (hRN e (hE₀δ ⟨heE, heX⟩) y hy) (R.inv_mem hy)⟩
        have h2 := hE₀N y ⟨hRinn hy, hRC hy⟩ e⁻¹ (inv_mem ⟨heE, heX⟩)
        have := mul_mem (⟨heE, heX⟩ : e ∈ E ⊓ X) h2
        simpa [mul_assoc] using this
      have h3 := hcon _ h1
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
      exact h3.symm
    obtain ⟨g, hg, ε, hε, hge⟩ := exists_of_mem_centralizer_radicalImage hev (by omega) i heC
    rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
    · rw [pow_zero, mul_one] at hge
      exact hcon e ⟨⟨heE, heX⟩, hge ▸ mem_map_of_mem _ hg⟩
    · exfalso
      apply hδX
      rw [pow_one] at hge
      have : dualAut n K = (conjAut n K g)⁻¹ * e := by rw [hge]; group
      rw [this]
      exact mul_mem (inv_mem (hRinn (mem_map_of_mem _ hg))) heX
  obtain ⟨g, hg, rfl⟩ := mem_map.mp hxR
  obtain ⟨v, hv, c, hgv⟩ := (mem_radicalGroup hev).mp hg
  have hv0 : onesVec ⬝ᵥ v = 0 := (mem_radicalW.mp hv).1
  have hNnorm : ∀ h ∈ matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) K),
      ∀ y ∈ (E ⊓ X) ⊓ R, conjAut n K h * y * (conjAut n K h)⁻¹ ∈ (E ⊓ X) ⊓ R := by
    intro h hh y hy
    have hhX : conjAut n K h ∈ X :=
      conjAut_mem_inner_of_det (det_eq_one_of_mem_matrixIsometryGroup (C := 1) hh)
    have hhC : conjAut n K h ∈ centralizer {dualAut n K} :=
      mem_centralizer_singleton_iff.mpr (commute_dualAut_of_mem (by omega) hh).eq.symm
    exact ⟨hE₀N _ ⟨hhX, hhC⟩ y hy.1, hRN _ hhC y hy.2⟩
  have hmemN : RadMem K ((E ⊓ X) ⊓ R) v c := ⟨g, hgv, hxE₀, hxR⟩
  have hne : (¬ ∃ a : K, v = a • onesVec) ∨ c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨a, rfl⟩, rfl⟩ := hcon
    apply hx1
    have : g = 1 := Units.ext (by
      rw [hgv, Units.val_one, ← zero_add (a • onesVec), radicalMatrix_add_smul_onesVec,
        radicalMatrix_zero])
    rw [this, map_one]
  have hq : 4 ≤ Nat.card K ∨ 5 ≤ n := by
    by_cases hn4 : n = 4
    · left
      have hm2 : 2 ≤ m := by omega
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    · right
      omega
  obtain ⟨μ, hμ, g₀, hg₀, hg₀N⟩ := hmemN.exists_root hev hNnorm hn hq hv0 hne
  have hv₀E : conjAut n K g₀ ∈ E := hg₀N.1.1
  have hv₀X : conjAut n K g₀ ∈ X := hg₀N.1.2
  have hv₀1 : conjAut n K g₀ ≠ 1 := by
    intro h
    obtain ⟨a, ha⟩ := (conjAut_eq_one_iff (by omega) g₀).mp h
    have := congrFun (congrFun (congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K))
      ha) ⟨0, by omega⟩) ⟨1, by omega⟩
    simp [GeneralLinearGroup.coe_scalar, hg₀, radicalMatrix, vecMulVec_apply, onesVec_apply]
      at this
    exact hμ this.symm
  have hv₀2 : orderOf (conjAut n K g₀) = 2 := by
    refine orderOf_eq_prime ?_ hv₀1
    rw [sq, ← map_mul]
    have : g₀ * g₀ = 1 := Units.ext (by
      rw [Units.val_mul, hg₀, radicalMatrix_mul_self hev (by simp) μ, Units.val_one])
    rw [this, map_one]
  have hO₀ := even_linear_higher_inner_involution_full_centralizer_odd_core (by omega) hm hK
    (H := X) le_rfl hv₀X hv₀2
  have hCv₀ := hc.centralizer_le_normalizer hXn hv₀E hv₀1 hO₀
  by_cases hn4 : n = 4
  · subst hn4
    have hK4 : 4 ≤ Nat.card K := by
      have hm2 : 2 ≤ m := by omega
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    exact false_of_root_four hK4 hc.elemAbelian hδ hg₀ hCv₀
  · exact false_of_root_six (by omega) hc.elemAbelian hδ hg₀ hCv₀

end Config

end CFSG.ComponentClassification.RankTwoHypIILinear
