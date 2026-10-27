module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4SteinU
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpCore
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4JHat
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OrdU
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4TBlocks
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AltFrame
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InnerCase
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpU4

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace StabU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut UnitaryConj HBlocks ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.GSThmB Subgroup

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

omit [Field K] in
theorem stdG_mul_stdG {R : Type*} [CommRing R] :
    (!![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0] : Matrix (Fin 4) (Fin 4) R) *
      !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem stdG_transpose : (stdG : Matrix (Fin 4) (Fin 4) K)ᵀ = stdG := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [stdG]

theorem blk_mul_stdG (b f' : K) : blk 0 b f' 0 * (stdG : Matrix (Fin 4) (Fin 4) K) = bJ b f' := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk, stdG, bJ, Matrix.mul_apply, Fin.sum_univ_four]

theorem map_bar_mul_stdG (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG) :
    (P : Matrix (Fin 4) (Fin 4) K).map h.bar * (stdG * (P : Matrix (Fin 4) (Fin 4) K)ᵀ) = 1 := by
  have h1 : (P : Matrix (Fin 4) (Fin 4) K)ᵀ * (P : Matrix (Fin 4) (Fin 4) K).map h.bar = stdG := by
    have := congrArg Matrix.transpose hP
    rwa [uStar, Matrix.transpose_mul, Matrix.transpose_transpose, stdG_transpose] at this
  have h2 : (stdG * (P : Matrix (Fin 4) (Fin 4) K)ᵀ) * (P : Matrix (Fin 4) (Fin 4) K).map h.bar =
      1 := by
    rw [Matrix.mul_assoc, h1]
    exact stdG_mul_stdG
  exact mul_eq_one_comm.1 h2

theorem eq_conj_of_mul_eq_one (P : GL (Fin 4) K) {A Q Q' : Matrix (Fin 4) (Fin 4) K}
    (hQ : Q * Q' = 1) :
    A = (P : Matrix (Fin 4) (Fin 4) K) * ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * A * Q) * Q' := by
  have hPP : (P : Matrix (Fin 4) (Fin 4) K) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul, Matrix.mul_assoc, hQ,
    Matrix.mul_one]

theorem comm_cP_of_fix (P : GL (Fin 4) K) {A : GL (Fin 4) K} {g : unitarySU p f K 4}
    (hg : (A : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) = ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :
    ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * A * P) * cP P g =
      cP P g * ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * A * P) := by
  have hPP : (P : Matrix (Fin 4) (Fin 4) K) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAA : (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hg' : (A : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * A := by
    conv_rhs => rw [← hg]
    rw [Matrix.mul_assoc _ (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K), hAA, Matrix.mul_one]
  simp only [cP]
  calc (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * A * P *
        ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * P) =
      (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * ((A : Matrix (Fin 4) (Fin 4) K) *
        ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) * P := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (P : Matrix (Fin 4) (Fin 4) K) (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K),
          hPP, Matrix.one_mul]
    _ = (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        A) * P := by rw [hg']
    _ = _ := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (P : Matrix (Fin 4) (Fin 4) K) (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K),
          hPP, Matrix.one_mul]

theorem comm_cP_of_fix_bar (P : GL (Fin 4) K) {A : GL (Fin 4) K} {g : unitarySU p f K 4}
    (hg : (A : Matrix (Fin 4) (Fin 4) K) *
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
        (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) = ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :
    ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * A * (P : Matrix (Fin 4) (Fin 4) K).map h.bar) *
        (cP P g).map h.bar =
      cP P g * ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * A *
        (P : Matrix (Fin 4) (Fin 4) K).map h.bar) := by
  have hPP : (P : Matrix (Fin 4) (Fin 4) K) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPb : (P : Matrix (Fin 4) (Fin 4) K).map h.bar *
      (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar = 1 := by
    rw [← Matrix.map_mul, hPP, Matrix.map_one _ (map_zero _) (map_one _)]
  have hAA : (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hg' : (A : Matrix (Fin 4) (Fin 4) K) *
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar =
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * A := by
    conv_rhs => rw [← hg]
    rw [Matrix.mul_assoc _ (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K), hAA, Matrix.mul_one]
  simp only [cP, Matrix.map_mul]
  calc (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * A * (P : Matrix (Fin 4) (Fin 4) K).map h.bar *
        ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar *
          ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
          (P : Matrix (Fin 4) (Fin 4) K).map h.bar) =
      (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * ((A : Matrix (Fin 4) (Fin 4) K) *
        ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar) *
        (P : Matrix (Fin 4) (Fin 4) K).map h.bar := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc ((P : Matrix (Fin 4) (Fin 4) K).map h.bar), hPb, Matrix.one_mul]
    _ = (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        A) * (P : Matrix (Fin 4) (Fin 4) K).map h.bar := by rw [hg']
    _ = _ := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (P : Matrix (Fin 4) (Fin 4) K) (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K),
          hPP, Matrix.one_mul]

theorem trace_uU (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG) (c : K) :
    ((uU h P hP c : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).trace = 4 := by
  rw [uU, val_hypSU, trace_conj, trace_U12]

theorem trace_uL (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG) (c : K) :
    ((uL h P hP c : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).trace = 4 := by
  rw [uL, val_hypSU, trace_conj, trace_U21]

theorem trace_conj' (A : GL (Fin 4) K) (M : Matrix (Fin 4) (Fin 4) K) :
    ((A : Matrix (Fin 4) (Fin 4) K) * M * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)).trace = M.trace :=
  trace_conj A M

theorem trace_map_bar (M : Matrix (Fin 4) (Fin 4) K) : (M.map h.bar).trace = h.bar M.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.map_apply]
  rw [map_sum]

include h in
theorem inner_or_psp_J (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1) (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    {l : K} (hl : l ^ 2 = -1) (hbl : h.bar l * l = -1) {μ : Kˣ}
    (hμ : ∀ x : Kˣ, x ∈ Subgroup.zpowers μ)
    (α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))) (hα2 : α ^ 2 = 1)
    (h1 : α (QuotientGroup.mk (uU h P hP 1)) = QuotientGroup.mk (uU h P hP 1))
    (h2 : α (QuotientGroup.mk (uL h P hP 1)) = QuotientGroup.mk (uL h P hP 1))
    (h3 : α (QuotientGroup.mk (uU h P hP μ)) = QuotientGroup.mk (uU h P hP μ)) :
    α = 1 ∨ α = MulAut.conj (QuotientGroup.mk (hypSU h P hP (X1 l) (unitary_X1 h hbl)
      (det_X1 hl))) ∨
      ∃ M : Subgroup (StatedProj (StatedSU 4 (p ^ f) K)), (∀ y ∈ M, α y = y) ∧
        Blueprint.LieModel ↥M .PSp 2 p f := by
  classical
  have : Finite K := h.finite
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2K h2K
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hl
    exact one_ne_zero (by linear_combination hl : (1 : K) = 0)
  have hμb := bar_ne_of_generator h hμ
  have hPP : (P : Matrix (Fin 4) (Fin 4) K) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPP' : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  obtain ⟨A, ψ, hAu, hψ, hcase⟩ := exists_steinberg_U4 h hp2 hq α hα2
  have key : ∀ g : unitarySU p f K 4, α (QuotientGroup.mk g) = QuotientGroup.mk g →
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).trace = 4 →
      ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).trace = 4 → ψ g = g :=
    fun g hg ht ht' => eq_of_mk_eq_of_trace h4 (by rw [hψ, hg]) ht' ht
  have hαψ : ∀ φ : unitarySU p f K 4 →* unitarySU p f K 4, (∀ g, φ g = ψ g) →
      ∀ β : MulAut (StatedProj (StatedSU 4 (p ^ f) K)),
        (∀ g, β (QuotientGroup.mk g) = QuotientGroup.mk (φ g)) → α = β := by
    intro φ hφ β hβ
    ext z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
    rw [← hψ, hβ, hφ]
  set X := hypSU h P hP (X1 l) (unitary_X1 h hbl) (det_X1 hl) with hX
  rcases hcase with ⟨hψv, c, hc⟩ | ⟨hψv, hA⟩
  ·
    have htrψ : ∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).trace =
        ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).trace := fun g => by
      rw [hψv, trace_conj']
    have e : ∀ g : unitarySU p f K 4, ψ g = g →
        (A : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) = ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
      fun g hg => by rw [← hψv, hg]
    have c1 := comm_cP_of_fix P (e _ (key _ h1 (trace_uU h P hP 1)
      (by rw [htrψ]; exact trace_uU h P hP 1)))
    have c2 := comm_cP_of_fix P (e _ (key _ h2 (trace_uL h P hP 1)
      (by rw [htrψ]; exact trace_uL h P hP 1)))
    have c3 := comm_cP_of_fix P (e _ (key _ h3 (trace_uU h P hP μ)
      (by rw [htrψ]; exact trace_uU h P hP μ)))
    rw [cP_uU] at c1 c3
    rw [cP_uL] at c2
    obtain ⟨A', hA'⟩ : ∃ M : Matrix (Fin 4) (Fin 4) K,
        M = (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * A * P := ⟨_, rfl⟩
    rw [← hA'] at c1 c2 c3
    have hA'd := eq_blk_diag_of_comm h hμb c1 c2 c3
    set x := A' 0 0 with hx
    set y := A' 2 2 with hy
    have hAeq : (A : Matrix (Fin 4) (Fin 4) K) = (P : Matrix (Fin 4) (Fin 4) K) * A' *
        (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
      rw [hA']
      exact eq_conj_of_mul_eq_one P hPP
    have hA'2 : A' * A' = c • 1 := by
      rw [hA']
      calc (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * A * P * ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * A * P)
          = (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * ((A : Matrix (Fin 4) (Fin 4) K) * A) * P := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc (P : Matrix (Fin 4) (Fin 4) K), hPP, Matrix.one_mul]
        _ = c • 1 := by rw [hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPP']
    rw [hA'd, blk_mul_blk] at hA'2
    have ex := congrFun (congrFun hA'2 0) 0
    have ey := congrFun (congrFun hA'2 2) 2
    simp [blk] at ex ey
    have hxy : (y - x) * (y + x) = 0 := by linear_combination ey - ex
    have hx0 : x ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hAeq
      rw [det_mul, det_mul, hA'd, det_blk, h0] at this
      simp at this
      exact (GeneralLinearGroup.det A).ne_zero
        (by rw [GeneralLinearGroup.val_det_apply]; exact this)
    have hAA : (A : Matrix (Fin 4) (Fin 4) K) * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hψA : ∀ g : unitarySU p f K 4, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        (A : Matrix (Fin 4) (Fin 4) K) =
        (A : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
      intro g
      have hAi : (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      rw [hψv, Matrix.mul_assoc _ (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K), hAi, Matrix.mul_one]
    rcases mul_eq_zero.1 hxy with hh | hh
    · left
      have hyx : y = x := sub_eq_zero.1 hh
      have hAs : (A : Matrix (Fin 4) (Fin 4) K) = x • 1 := by
        rw [hAeq, hA'd, hyx]
        have hb : blk x 0 0 x = x • (1 : Matrix (Fin 4) (Fin 4) K) := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [blk]
        rw [hb, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPP]
      refine hαψ (MonoidHom.id _) (fun g => ?_) 1 (fun g => rfl)
      apply ext_val
      have := hψA g
      rw [hAs, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul] at this
      exact (smul_right_injective _ hx0 this).symm
    · right; left
      have hyx : y = -x := by linear_combination hh
      have hAs : (A : Matrix (Fin 4) (Fin 4) K) =
          (x * l⁻¹) • ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
        rw [hAeq, hA'd, hyx, hX, val_hypSU]
        have hb : blk x 0 0 (-x) = (x * l⁻¹) • X1 l := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [blk, X1] <;> field_simp
        rw [hb, Matrix.mul_smul, Matrix.smul_mul]
      have hc0 : x * l⁻¹ ≠ 0 := mul_ne_zero hx0 (inv_ne_zero hl0)
      refine hαψ (MulAut.conj X).toMonoidHom (fun g => ?_) (MulAut.conj (QuotientGroup.mk X))
        (fun g => ?_)
      · apply ext_val
        have e1 := hψA g
        rw [hAs, Matrix.mul_smul, Matrix.smul_mul] at e1
        have e2 := smul_right_injective _ hc0 e1
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
          Subgroup.coe_inv, Units.val_mul, Units.val_mul]
        rw [← e2, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.mul_one]
      · rw [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, QuotientGroup.mk_mul,
          QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  ·
    right; right
    have htrψ : ∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).trace =
        h.bar ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).trace := fun g => by
      rw [hψv, trace_conj', trace_map_bar]
    have h4' : h.bar 4 = 4 := map_ofNat h.bar 4
    have e : ∀ g : unitarySU p f K 4, ψ g = g →
        (A : Matrix (Fin 4) (Fin 4) K) *
          ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
          (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) = ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
      fun g hg => by rw [← hψv, hg]
    have c1 := comm_cP_of_fix_bar h P (e _ (key _ h1 (trace_uU h P hP 1)
      (by rw [htrψ, trace_uU, h4'])))
    have c2 := comm_cP_of_fix_bar h P (e _ (key _ h2 (trace_uL h P hP 1)
      (by rw [htrψ, trace_uL, h4'])))
    have c3 := comm_cP_of_fix_bar h P (e _ (key _ h3 (trace_uU h P hP μ)
      (by rw [htrψ, trace_uU, h4'])))
    rw [cP_uU, map_U12 h h.bar (comm_bar h h.bar), map_one] at c1
    rw [cP_uL, map_U21 h h.bar (comm_bar h h.bar), map_one] at c2
    rw [cP_uU, map_U12 h h.bar (comm_bar h h.bar)] at c3
    obtain ⟨A', hA'⟩ : ∃ M : Matrix (Fin 4) (Fin 4) K,
        M = (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * A * (P : Matrix (Fin 4) (Fin 4) K).map h.bar :=
      ⟨_, rfl⟩
    rw [← hA'] at c1 c2 c3
    have hblk := eq_blk_of_comm h c1 c2
    rw [hblk] at c3
    obtain ⟨r1, -, -, r4⟩ := blk_rel h c3
    have hx : A' 0 0 = 0 := by
      rcases mul_eq_zero.1 r1 with h0 | h0
      · exact h0
      · exact absurd (sub_eq_zero.1 h0) hμb
    have hy : A' 2 2 = 0 := by
      rcases mul_eq_zero.1 r4 with h0 | h0
      · exact h0
      · exfalso
        apply hμb
        have e := congrArg h.bar (sub_eq_zero.1 h0)
        rw [h.bar_bar, h.bar_bar] at e
        exact e
    rw [hx, hy] at hblk
    have hAeq : (A : Matrix (Fin 4) (Fin 4) K) = (P : Matrix (Fin 4) (Fin 4) K) * A' *
        (stdG * (P : Matrix (Fin 4) (Fin 4) K)ᵀ) := by
      rw [hA']
      exact eq_conj_of_mul_eq_one P (map_bar_mul_stdG h P hP)
    have hAt : (A : Matrix (Fin 4) (Fin 4) K)ᵀ = -(A : Matrix (Fin 4) (Fin 4) K) := by
      have e1 : (A : Matrix (Fin 4) (Fin 4) K) = (P : Matrix (Fin 4) (Fin 4) K) *
          bJ (A' 0 3) (A' 2 1) * (P : Matrix (Fin 4) (Fin 4) K)ᵀ := by
        rw [hAeq, ← blk_mul_stdG, ← hblk]
        simp only [Matrix.mul_assoc]
      rw [e1, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
        TBlocks.transpose_bJ, Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc]
    rcases hA with ⟨hAA, -⟩ | ⟨-, hAs⟩
    · exact exists_psp_of_alt_U4 h hp2 hq hAu hAA ψ hψv hψ
    · exfalso
      rw [hAs] at hAt
      have h0 : (A : Matrix (Fin 4) (Fin 4) K) = 0 := by
        have : (2 : K) • (A : Matrix (Fin 4) (Fin 4) K) = 0 := by
          rw [two_smul]
          nth_rewrite 1 [hAt]
          rw [neg_add_cancel]
        exact (smul_eq_zero.1 this).resolve_left h2K
      have := (GeneralLinearGroup.det A).ne_zero
      rw [GeneralLinearGroup.val_det_apply, h0, Matrix.det_zero] at this
      exact this rfl

include h in
theorem innerPSpAt_J_U4 (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1) (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    {l : K} (hl : l ^ 2 = -1) (hbl : h.bar l * l = -1)
    {J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hJX : J' ≤ Subgroup.centralizer {(QuotientGroup.mk (hypSU h P hP (X1 l) (unitary_X1 h hbl)
      (det_X1 hl)) : StatedProj (StatedSU 4 (p ^ f) K))})
    (hJp : ⁅J', J'⁆ = J') [IsSimpleGroup ↥J']
    (hcard : (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) ≤ 2 * Nat.card J') :
    InnerPSpAt (p ^ f) p f (QuotientGroup.mk (hypSU h P hP (X1 l) (unitary_X1 h hbl)
      (det_X1 hl)) : StatedProj (StatedSU 4 (p ^ f) K)) := by
  classical
  have : Finite K := h.finite
  have hq3 : p ^ f ≠ 3 := by omega
  set ℓ : StatedProj (StatedSU 4 (p ^ f) K) := QuotientGroup.mk (hypSU h P hP (X1 l)
    (unitary_X1 h hbl) (det_X1 hl)) with hℓ
  have hNdef : centralizerCore516 (p ^ f) ℓ = Quasithin.perfectCore (centralizer {ℓ}) := by
    unfold centralizerCore516
    rw [ite_eq_right hq3]
  have hJN : J' ≤ centralizerCore516 (p ^ f) ℓ := by
    rw [hNdef]
    exact Quasithin.le_perfectCore_of_perfect hJX hJp
  have hNC : centralizerCore516 (p ^ f) ℓ ≤ centralizer {ℓ} := by
    rw [hNdef]
    exact Quasithin.perfectCore_le _
  have hNp : ⁅centralizerCore516 (p ^ f) ℓ, centralizerCore516 (p ^ f) ℓ⁆ =
      centralizerCore516 (p ^ f) ℓ := by
    rw [hNdef]
    exact Quasithin.perfectCore_perfect _
  have hcardN : (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) ≤ 2 * Nat.card (centralizerCore516 (p ^ f) ℓ) :=
    hcard.trans (Nat.mul_le_mul_left 2 (Subgroup.card_le_of_le hJN))
  obtain ⟨-, -, hle⟩ := eq_of_perfect_U4 h hp2 P hP hl hbl hNC hNp hcardN
  have hN : centralizerCore516 (p ^ f) ℓ = J' :=
    (Subgroup.eq_of_le_of_card_ge hJN (by omega)).symm
  have heven : Even (Nat.card J') := by
    have h2 : 2 * Nat.card J' = (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) := by
      rw [hN] at hle
      omega
    exact even_of_two_mul_eq (h.prime.odd_of_ne_two hp2).pow h2
  refine ⟨pPrimeCore_centralizerCore516_eq_bot hJX hN.le (eq_bot_of_le_simple heven),
    fun ε hε2 hε1 hεℓ _ hεN => ?_⟩
  obtain ⟨hJU, hJL, -⟩ := eq_of_perfect_U4 h hp2 P hP hl hbl hJX hJp hcard
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hfix : ∀ y ∈ J', ε y = y := fun y hy => hεN y (by rw [hN]; exact hy)
  rcases inner_or_psp_J h hp2 hq P hP hl hbl hμ ε hε2 (hfix _ (hJU 1)) (hfix _ (hJL 1))
      (hfix _ (hJU μ)) with h1 | h1 | hM
  · exact absurd h1 hε1
  · exact absurd h1 hεℓ
  · exact hM

end StabU

end CFSG.ComponentClassification.CatFactsL4U4
