module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Blocks
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Cover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveQuadraticField
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace StabL

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag Blocks
  CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
open scoped commutatorElement

instance fact_even_card_fin_four : Fact (Even (Fintype.card (Fin 4))) := ⟨⟨2, rfl⟩⟩

variable {F : Type} [Field F]

theorem det_stdJ : (stdJ : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [stdJ, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

@[expose] def k₀ : SpecialLinearGroup (Fin 4) F := ⟨stdJ, det_stdJ⟩

@[expose] def slA (a b : F) : SpecialLinearGroup (Fin 4) F := ⟨uA a b, det_uA a b⟩

@[expose] def slB (a b : F) : SpecialLinearGroup (Fin 4) F := ⟨uB a b, det_uB a b⟩

@[expose] def slH : SpecialLinearGroup (Fin 4) F := ⟨hJ, det_hJ⟩

@[expose] def slW : SpecialLinearGroup (Fin 4) F := ⟨wJ, det_wJ⟩

variable (F) in
@[expose] def C₀ : Subgroup (SpecialLinearGroup (Fin 4) F) :=
  Subgroup.centralizer {k₀}

variable (F) in
@[expose] def S₀ : Subgroup (SpecialLinearGroup (Fin 4) F) := ⁅C₀ F, C₀ F⁆

variable (F) in
@[expose] def J₀ : Subgroup (projectiveSL 4 F) := (S₀ F).map (proj 4 F)

theorem coe_inv_eq {x : SpecialLinearGroup (Fin 4) F} {M : Matrix (Fin 4) (Fin 4) F}
    (h : (x : Matrix (Fin 4) (Fin 4) F) * M = 1) :
    ((x⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = M := by
  have h1 : ((x⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * x = 1 :=
    congrArg (fun y : SpecialLinearGroup (Fin 4) F => (y : Matrix (Fin 4) (Fin 4) F))
      (inv_mul_cancel x)
  calc ((x⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
      = ((x⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (x * M) := by
        rw [h, Matrix.mul_one]
    _ = (((x⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * x) * M :=
        (Matrix.mul_assoc _ _ _).symm
    _ = M := by rw [h1, Matrix.one_mul]

theorem coe_slH_inv : ((slH⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = -hJ :=
  coe_inv_eq (by rw [Matrix.mul_neg]; exact neg_eq_iff_eq_neg.2 (hJ_mul_hJ (F := F)))

theorem coe_slW_inv : ((slW⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = -wJ :=
  coe_inv_eq (by rw [Matrix.mul_neg]; exact neg_eq_iff_eq_neg.2 (wJ_mul_wJ (F := F)))

theorem coe_slA_inv (a b : F) :
    (((slA a b)⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = uA (-a) (-b) :=
  coe_inv_eq (by
    change uA a b * uA (-a) (-b) = 1
    rw [uA_mul_uA, add_neg_cancel, add_neg_cancel, uA_zero])

theorem coe_slB_inv (a b : F) :
    (((slB a b)⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = uB (-a) (-b) :=
  coe_inv_eq (by
    change uB a b * uB (-a) (-b) = 1
    rw [uB_mul_uB, add_neg_cancel, add_neg_cancel, uB_zero])

theorem mem_C₀_iff {x : SpecialLinearGroup (Fin 4) F} :
    x ∈ C₀ F ↔ (x : Matrix (Fin 4) (Fin 4) F) * stdJ = stdJ * (x : Matrix (Fin 4) (Fin 4) F) := by
  rw [C₀, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact congrArg (fun y : SpecialLinearGroup (Fin 4) F => (y : Matrix (Fin 4) (Fin 4) F)) h
  · intro h
    exact Subtype.ext h

theorem slH_mem_C₀ : (slH : SpecialLinearGroup (Fin 4) F) ∈ C₀ F :=
  mem_C₀_iff.2 (hJ_comm (F := F))

theorem slW_mem_C₀ : (slW : SpecialLinearGroup (Fin 4) F) ∈ C₀ F :=
  mem_C₀_iff.2 (wJ_comm (F := F))

theorem slA_mem_C₀ (a b : F) : slA a b ∈ C₀ F := mem_C₀_iff.2 (uA_comm (F := F) a b)

theorem slB_mem_C₀ (a b : F) : slB a b ∈ C₀ F := mem_C₀_iff.2 (uB_comm (F := F) a b)

theorem slA_mem_S₀ (h2 : (2 : F) ≠ 0) (a b : F) : slA a b ∈ S₀ F := by
  have h : ⁅(slH : SpecialLinearGroup (Fin 4) F), slA (-a / 2) (-b / 2)⁆ = slA a b := by
    apply Subtype.ext
    rw [commutatorElement_def, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, coe_slH_inv (F := F), coe_slA_inv]
    change hJ * uA (-a / 2) (-b / 2) * -hJ * uA (-(-a / 2)) (-(-b / 2)) = uA a b
    rw [commutator_hJ_uA]
    congr 1 <;> field_simp
  rw [← h]
  exact Subgroup.commutator_mem_commutator slH_mem_C₀ (slA_mem_C₀ _ _)

theorem slB_mem_S₀ (h2 : (2 : F) ≠ 0) (a b : F) : slB a b ∈ S₀ F := by
  have h : ⁅(slH : SpecialLinearGroup (Fin 4) F), slB (-a / 2) (-b / 2)⁆ = slB a b := by
    apply Subtype.ext
    rw [commutatorElement_def, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, coe_slH_inv (F := F), coe_slB_inv]
    change hJ * uB (-a / 2) (-b / 2) * -hJ * uB (-(-a / 2)) (-(-b / 2)) = uB a b
    rw [commutator_hJ_uB]
    congr 1 <;> field_simp
  rw [← h]
  exact Subgroup.commutator_mem_commutator slH_mem_C₀ (slB_mem_C₀ _ _)

theorem neg_one_mem_S₀ : (-1 : SpecialLinearGroup (Fin 4) F) ∈ S₀ F := by
  have h : ⁅(slH : SpecialLinearGroup (Fin 4) F), (slW : SpecialLinearGroup (Fin 4) F)⁆ = -1 := by
    apply Subtype.ext
    rw [commutatorElement_def, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_slH_inv (F := F),
      coe_slW_inv (F := F), Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
    exact commutator_hJ_wJ
  rw [← h]
  exact Subgroup.commutator_mem_commutator slH_mem_C₀ slW_mem_C₀

theorem trace_uA (a b : F) : (uA a b).trace = 4 := by
  simp [uA, Matrix.trace, Fin.sum_univ_four]
  norm_num

theorem trace_uB (a b : F) : (uB a b).trace = 4 := by
  simp [uB, Matrix.trace, Fin.sum_univ_four]
  norm_num

theorem eq_of_eq_or_neg_of_trace (h2 : (2 : F) ≠ 0) {M u : Matrix (Fin 4) (Fin 4) F}
    (hM : M = u ∨ M = -u) (htr : M.trace = u.trace) (hu : u.trace = 4) : M = u := by
  rcases hM with hM | hM
  · exact hM
  · exfalso
    rw [hM, Matrix.trace_neg, hu] at htr
    apply h2
    have : (2 : F) * 2 * 2 = 0 := by linear_combination -htr
    simpa using this

variable [Fintype F]

theorem two_ne_zero_of_card_mod_four (hF : Fintype.card F % 4 = 3) : (2 : F) ≠ 0 := by
  intro h0
  have hc : ringChar F = 2 := by
    have := (ringChar.spec F 2).1 (by exact_mod_cast h0)
    exact (Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime F (ringChar F)) Nat.prime_two).1 this
  have := FiniteField.even_card_iff_char_two.1 hc
  omega

theorem eq_of_proj_eq (hF : Fintype.card F % 4 = 3) {x y : SpecialLinearGroup (Fin 4) F}
    (h : proj 4 F x = proj 4 F y) :
    (y : Matrix (Fin 4) (Fin 4) F) = x ∨ (y : Matrix (Fin 4) (Fin 4) F) = -x := by
  rw [proj_eq_proj_iff, mem_scalars] at h
  obtain ⟨c, hc, hxy⟩ := h
  have hc4 : (c : F) ^ 4 = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
  have hy : (y : Matrix (Fin 4) (Fin 4) F) = x * scalar (Fin 4) (c : F) := by
    rw [← hxy, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  rcases eq_one_or_eq_neg_one_of_pow_four hF hc4 with h1 | h1
  · left
    rw [hy, h1, map_one, Matrix.mul_one]
  · right
    rw [hy, h1, map_neg, map_one, Matrix.mul_neg, Matrix.mul_one]

theorem comm_of_proj_comm (hF : Fintype.card F % 4 = 3) {X u : SpecialLinearGroup (Fin 4) F}
    (hu : (u : Matrix (Fin 4) (Fin 4) F).trace = 4)
    (h : proj 4 F X * proj 4 F u = proj 4 F u * proj 4 F X) :
    (X : Matrix (Fin 4) (Fin 4) F) * u = u * X := by
  have h2 : (2 : F) ≠ 0 := by
    intro h0
    have hc : ringChar F = 2 := by
      have := (ringChar.spec F 2).1 (by exact_mod_cast h0)
      exact (Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime F (ringChar F)) Nat.prime_two).1 this
    have := FiniteField.even_card_iff_char_two.1 hc
    omega
  have h1 : proj 4 F (X * u * X⁻¹) = proj 4 F u := by
    rw [map_mul, map_mul, map_inv, h, mul_inv_cancel_right]
  have h3 := eq_of_eq_or_neg_of_trace h2 (eq_of_proj_eq hF h1.symm) (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm,
      ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]) hu
  calc (X : Matrix (Fin 4) (Fin 4) F) * u = (X * u * X⁻¹ : SpecialLinearGroup (Fin 4) F) * X := by
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
          Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul X⁻¹, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
    _ = u * X := by rw [h3]

@[expose] def HasUnipotents (J' : Subgroup (projectiveSL 4 F)) : Prop :=
  proj 4 F (slA 1 0) ∈ J' ∧ proj 4 F (slA 0 1) ∈ J' ∧ proj 4 F (slB 1 0) ∈ J'

theorem eq_of_proj_mem_centralizer (hF : Fintype.card F % 4 = 3)
    {J' : Subgroup (projectiveSL 4 F)} (hJ' : HasUnipotents J') {X : SpecialLinearGroup (Fin 4) F}
    (hX : ∀ y ∈ J', proj 4 F X * y = y * proj 4 F X) :
    (X : Matrix (Fin 4) (Fin 4) F) = X 0 0 • 1 + X 1 0 • stdJ := by
  obtain ⟨h1, h2, h3⟩ := hJ'
  exact eq_of_comm_unipotents (comm_of_proj_comm hF (trace_uA 1 0) (hX _ h1))
    (comm_of_proj_comm hF (trace_uA 0 1) (hX _ h2)) (comm_of_proj_comm hF (trace_uB 1 0) (hX _ h3))

theorem conj_k₀_eq_or_neg (hF : Fintype.card F % 4 = 3) {J' : Subgroup (projectiveSL 4 F)}
    (hJk : J' ≤ Subgroup.centralizer {proj 4 F k₀}) (hJ' : HasUnipotents J')
    {h : SpecialLinearGroup (Fin 4) F} (hN : proj 4 F h ∈ Subgroup.normalizer (J' : Set _)) :
    ((h * k₀ * h⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = stdJ ∨
      ((h * k₀ * h⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = -stdJ := by
  classical
  have hns : ¬ IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff]
    omega
  set X := h * k₀ * h⁻¹ with hXdef
  have hcomm : ∀ y ∈ J', proj 4 F X * y = y * proj 4 F X := by
    intro y hy
    have hy' : (proj 4 F h)⁻¹ * y * proj 4 F h ∈ J' := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hN) y).mp hy
      simpa using this
    have hk := Subgroup.mem_centralizer_singleton_iff.mp (hJk hy')
    rw [hXdef, map_mul, map_mul, map_inv]
    calc proj 4 F h * proj 4 F k₀ * (proj 4 F h)⁻¹ * y
        = proj 4 F h * (proj 4 F k₀ * ((proj 4 F h)⁻¹ * y * proj 4 F h)) * (proj 4 F h)⁻¹ := by
          group
      _ = proj 4 F h * (((proj 4 F h)⁻¹ * y * proj 4 F h) * proj 4 F k₀) * (proj 4 F h)⁻¹ := by
          rw [hk]
      _ = y * (proj 4 F h * proj 4 F k₀ * (proj 4 F h)⁻¹) := by group
  have hX := eq_of_proj_mem_centralizer hF hJ' hcomm
  have hXX : (X : Matrix (Fin 4) (Fin 4) F) * X = -1 := by
    rw [hXdef, ← Matrix.SpecialLinearGroup.coe_mul]
    have : h * k₀ * h⁻¹ * (h * k₀ * h⁻¹) = h * (k₀ * k₀) * h⁻¹ := by group
    rw [this, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul]
    change _ * (stdJ * stdJ) * _ = _
    rw [stdJ_mul_stdJ, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul,
      ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  set a := X 0 0
  set b := X 1 0
  rw [hX] at hXX
  have e00 := congrFun (congrFun hXX 0) 0
  have e10 := congrFun (congrFun hXX 1) 0
  simp [stdJ, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] at e00 e10
  have hab : a * b = 0 := by
    have h2 : (2 : F) ≠ 0 := by
      intro h0
      apply hns
      exact ⟨1, by linear_combination -h0⟩
    have : (2 : F) * (a * b) = 0 := by linear_combination e10
    exact (mul_eq_zero.1 this).resolve_left h2
  rcases mul_eq_zero.1 hab with ha | hb
  · have hb2 : b * b = 1 := by rw [ha] at e00; linear_combination -e00
    rcases mul_self_eq_one_iff.1 hb2 with hb1 | hb1
    · left
      rw [hX, ha, hb1, zero_smul, zero_add, one_smul]
    · right
      rw [hX, ha, hb1, zero_smul, zero_add, neg_one_smul]
  · exfalso
    apply hns
    rw [hb] at e00
    exact ⟨a, by linear_combination -e00⟩

variable (F) in
@[expose] def Z₀ : Subgroup (SpecialLinearGroup (Fin 4) F) :=
  Subgroup.centralizer {slA 1 0, slA 0 1, slB 1 0}

omit [Fintype F] in
theorem eq_of_mem_Z₀ {X : SpecialLinearGroup (Fin 4) F} (hX : X ∈ Z₀ F) :
    (X : Matrix (Fin 4) (Fin 4) F) = X 0 0 • 1 + X 1 0 • stdJ := by
  have hc : ∀ u ∈ ({slA 1 0, slA 0 1, slB 1 0} : Set (SpecialLinearGroup (Fin 4) F)),
      (u : Matrix (Fin 4) (Fin 4) F) * X = X * u := fun u hu =>
    congrArg (fun y : SpecialLinearGroup (Fin 4) F => (y : Matrix (Fin 4) (Fin 4) F))
      (Subgroup.mem_centralizer_iff.mp hX u hu)
  exact eq_of_comm_unipotents (hc (slA 1 0) (by simp)).symm (hc (slA 0 1) (by simp)).symm
    (hc (slB 1 0) (by simp)).symm

omit [Fintype F] in
theorem smul_add_smul_mul (a b c d : F) :
    (a • 1 + b • stdJ : Matrix (Fin 4) (Fin 4) F) * (c • 1 + d • stdJ) =
      (a * c - b * d) • 1 + (a * d + b * c) • stdJ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stdJ, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;> ring

omit [Fintype F] in
theorem smul_add_smul_apply_zero_zero (a b : F) :
    (a • 1 + b • stdJ : Matrix (Fin 4) (Fin 4) F) 0 0 = a := by simp [stdJ]

omit [Fintype F] in
theorem smul_add_smul_apply_one_zero (a b : F) :
    (a • 1 + b • stdJ : Matrix (Fin 4) (Fin 4) F) 1 0 = b := by simp [stdJ]

omit [Fintype F] in
theorem eq_zero_of_add_mul_root {lam : F} (hns : ¬ IsSquare lam) {x y : F}
    (h : algebraMap F (extension lam) x +
      algebraMap F (extension lam) y * AdjoinRoot.root (quadraticPolynomial lam) = 0) :
    x = 0 ∧ y = 0 := by
  have : Fact (¬ IsSquare lam) := ⟨hns⟩
  have hy : y = 0 := by
    by_contra hy
    apply hns
    have hr : AdjoinRoot.root (quadraticPolynomial lam) =
        algebraMap F (extension lam) (-x / y) := by
      have hy' : algebraMap F (extension lam) y ≠ 0 :=
        (map_ne_zero (algebraMap F (extension lam))).2 hy
      rw [map_div₀, map_neg]
      field_simp
      linear_combination h
    have h2 := extension_root_square lam
    rw [hr, ← map_pow] at h2
    refine ⟨-x / y, ?_⟩
    rw [← sq]
    exact ((algebraMap F (extension lam)).injective h2).symm
  rw [hy, map_zero, zero_mul, add_zero, map_eq_zero] at h
  exact ⟨h, hy⟩

theorem isCyclic_Z₀ (hF : Fintype.card F % 4 = 3) : IsCyclic (Z₀ F) := by
  classical
  have hns : ¬ IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff]
    omega
  have : Fact (¬ IsSquare (-1 : F)) := ⟨hns⟩
  set E := extension (-1 : F)
  set r := AdjoinRoot.root (quadraticPolynomial (-1 : F))
  have hr : r * r = -1 := by
    rw [← sq, extension_root_square, map_neg, map_one]
  let ψ : Z₀ F →* E :=
    { toFun := fun X => algebraMap F E ((X : SpecialLinearGroup (Fin 4) F) 0 0) +
        algebraMap F E ((X : SpecialLinearGroup (Fin 4) F) 1 0) * r
      map_one' := by simp
      map_mul' := by
        intro X Y
        have hX := eq_of_mem_Z₀ X.2
        have hY := eq_of_mem_Z₀ Y.2
        have hXY : ((X * Y : Z₀ F) : Matrix (Fin 4) (Fin 4) F) =
            (((X : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) *
              ((Y : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := rfl
        rw [hX, hY, smul_add_smul_mul] at hXY
        have h00 := congrFun (congrFun hXY 0) 0
        have h10 := congrFun (congrFun hXY 1) 0
        rw [smul_add_smul_apply_zero_zero] at h00
        rw [smul_add_smul_apply_one_zero] at h10
        change algebraMap F E (((X * Y : Z₀ F) : SpecialLinearGroup (Fin 4) F) 0 0) +
            algebraMap F E (((X * Y : Z₀ F) : SpecialLinearGroup (Fin 4) F) 1 0) * r = _
        rw [h00, h10, map_sub, map_add, map_mul, map_mul, map_mul, map_mul]
        linear_combination (-(algebraMap F E ((X : SpecialLinearGroup (Fin 4) F) 1 0) *
          algebraMap F E ((Y : SpecialLinearGroup (Fin 4) F) 1 0))) * hr }
  apply isCyclic_of_injective_ringHom ψ
  intro X Y hXY
  have h := sub_eq_zero.2 hXY
  change algebraMap F E ((X : SpecialLinearGroup (Fin 4) F) 0 0) +
      algebraMap F E ((X : SpecialLinearGroup (Fin 4) F) 1 0) * r -
      (algebraMap F E ((Y : SpecialLinearGroup (Fin 4) F) 0 0) +
      algebraMap F E ((Y : SpecialLinearGroup (Fin 4) F) 1 0) * r) = 0 at h
  have h' : algebraMap F E ((X : SpecialLinearGroup (Fin 4) F) 0 0 -
      (Y : SpecialLinearGroup (Fin 4) F) 0 0) + algebraMap F E
      ((X : SpecialLinearGroup (Fin 4) F) 1 0 -
        (Y : SpecialLinearGroup (Fin 4) F) 1 0) * r = 0 := by
    rw [map_sub, map_sub]
    linear_combination h
  obtain ⟨h0, h1⟩ := eq_zero_of_add_mul_root hns h'
  apply Subtype.ext
  apply Subtype.ext
  rw [eq_of_mem_Z₀ X.2, eq_of_mem_Z₀ Y.2, sub_eq_zero.1 h0, sub_eq_zero.1 h1]

theorem isCyclic_centralizer (hF : Fintype.card F % 4 = 3) {J' : Subgroup (projectiveSL 4 F)}
    (hJ' : HasUnipotents J') : IsCyclic (Subgroup.centralizer (J' : Set (projectiveSL 4 F))) := by
  have := isCyclic_Z₀ hF
  have hle : Subgroup.centralizer (J' : Set (projectiveSL 4 F)) ≤ (Z₀ F).map (proj 4 F) := by
    intro x hx
    obtain ⟨X, rfl⟩ := proj_surjective 4 F x
    refine ⟨X, ?_, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hJ'
    rw [SetLike.mem_coe, Z₀, Subgroup.mem_centralizer_iff]
    intro u hu
    have key : ∀ u : SpecialLinearGroup (Fin 4) F, (u : Matrix (Fin 4) (Fin 4) F).trace = 4 →
        proj 4 F u ∈ J' → u * X = X * u := by
      intro u htr hu'
      apply Subtype.ext
      exact (comm_of_proj_comm hF htr (Subgroup.mem_centralizer_iff.mp hx _ hu').symm).symm
    rcases hu with rfl | rfl | rfl
    · exact key _ (trace_uA 1 0) h1
    · exact key _ (trace_uA 0 1) h2
    · exact key _ (trace_uB 1 0) h3
  have : IsCyclic ((Z₀ F).map (proj 4 F)) :=
    isCyclic_of_surjective ((proj 4 F).subgroupMap (Z₀ F))
      ((proj 4 F).subgroupMap_surjective (Z₀ F))
  exact Subgroup.isCyclic_of_le hle

end StabL

end CFSG.ComponentClassification.CatFactsL4U4
