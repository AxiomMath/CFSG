module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFourCoverMatrices
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoL3Even

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag FieldFourCover
open CFSG.LieType.Chevalley
open scoped commutatorElement

variable {F : Type} [Field F]

theorem commutatorElement_unipU (a b c a' b' c' : F) :
    ⁅unipU F a b c, unipU F a' b' c'⁆ = unipU F 0 0 (a * b' - a' * b) := by
  rw [commutatorElement_def, unipU_inv, unipU_inv, unipU_mul, unipU_mul, unipU_mul]
  congr 1 <;> ring

theorem unipU_mul_self [CharP F 2] (a b c : F) :
    unipU F a b c * unipU F a b c = unipU F 0 0 (a * b) := by
  rw [unipU_mul]
  congr 1
  · exact CharTwo.add_self_eq_zero a
  · exact CharTwo.add_self_eq_zero b
  · rw [CharTwo.add_self_eq_zero, zero_add]

@[expose] def torusSL (l : Fˣ) : SpecialLinearGroup (Fin 3) F :=
  ⟨!![(l : F), 0, 0; 0, (l : F)⁻¹ * (l : F)⁻¹, 0; 0, 0, (l : F)], by
    simp [Matrix.det_fin_three]⟩

theorem coe_torusSL (l : Fˣ) :
    (torusSL l : Matrix (Fin 3) (Fin 3) F) =
      !![(l : F), 0, 0; 0, (l : F)⁻¹ * (l : F)⁻¹, 0; 0, 0, (l : F)] :=
  rfl

theorem torusSL_mul_unipU (l : Fˣ) (a b c : F) :
    torusSL l * unipU F a b c =
      unipU F ((l : F) ^ 3 * a) ((l : F)⁻¹ ^ 3 * b) c * torusSL l := by
  have hl : (l : F) ≠ 0 := l.ne_zero
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_torusSL, coe_unipU,
    coe_unipU]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp

theorem torusSL_conj_unipU (l : Fˣ) (a b c : F) :
    torusSL l * unipU F a b c * (torusSL l)⁻¹ =
      unipU F ((l : F) ^ 3 * a) ((l : F)⁻¹ ^ 3 * b) c := by
  rw [mul_inv_eq_iff_eq_mul, torusSL_mul_unipU]

theorem commutatorElement_torusSL_unipU (l : Fˣ) (a b c : F) :
    ⁅torusSL l, unipU F a b c⁆ =
      unipU F (((l : F) ^ 3 - 1) * a) (((l : F)⁻¹ ^ 3 - 1) * b) ((1 - (l : F) ^ 3) * (a * b)) := by
  have hl : (l : F) ≠ 0 := l.ne_zero
  rw [commutatorElement_def, torusSL_conj_unipU, unipU_inv, unipU_mul]
  congr 1 <;> field_simp <;> ring

@[expose] def levi13Mat (B : SL2 F) : SpecialLinearGroup (Fin 3) F :=
  ⟨!![(B : Matrix (Fin 2) (Fin 2) F) 0 0, 0, (B : Matrix (Fin 2) (Fin 2) F) 0 1; 0, 1, 0;
      (B : Matrix (Fin 2) (Fin 2) F) 1 0, 0, (B : Matrix (Fin 2) (Fin 2) F) 1 1], by
    simp [Matrix.det_fin_three]
    linear_combination det_SL2 B⟩

theorem coe_levi13Mat (B : SL2 F) :
    (levi13Mat B : Matrix (Fin 3) (Fin 3) F) =
      !![(B : Matrix (Fin 2) (Fin 2) F) 0 0, 0, (B : Matrix (Fin 2) (Fin 2) F) 0 1; 0, 1, 0;
        (B : Matrix (Fin 2) (Fin 2) F) 1 0, 0, (B : Matrix (Fin 2) (Fin 2) F) 1 1] :=
  rfl

variable (F) in
@[expose] def levi13 : SL2 F →* SpecialLinearGroup (Fin 3) F where
  toFun := levi13Mat
  map_one' := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [coe_levi13Mat]
    fin_cases i <;> fin_cases j <;> simp
  map_mul' B B' := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_levi13Mat, coe_levi13Mat, coe_levi13Mat,
      Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem coe_levi13 (B : SL2 F) :
    (levi13 F B : Matrix (Fin 3) (Fin 3) F) =
      !![(B : Matrix (Fin 2) (Fin 2) F) 0 0, 0, (B : Matrix (Fin 2) (Fin 2) F) 0 1; 0, 1, 0;
        (B : Matrix (Fin 2) (Fin 2) F) 1 0, 0, (B : Matrix (Fin 2) (Fin 2) F) 1 1] :=
  rfl

variable (F) in
@[expose] def projLevi : SL2 F →* projectiveSL 3 F :=
  (proj 3 F).comp (levi13 F)

theorem projLevi_apply (B : SL2 F) : projLevi F B = proj 3 F (levi13 F B) :=
  rfl

theorem projLevi_injective : Function.Injective (projLevi F) := by
  rw [injective_iff_map_eq_one]
  intro B hB
  rw [projLevi_apply, ← map_one (proj 3 F)] at hB
  obtain ⟨d, -, hd⟩ := eq_mul_scalar_of_proj_eq hB
  have h00 := congrFun (congrFun hd 0) 0
  have h11 := congrFun (congrFun hd 1) 1
  have h02 := congrFun (congrFun hd 0) 2
  have h20 := congrFun (congrFun hd 2) 0
  have h22 := congrFun (congrFun hd 2) 2
  simp [coe_levi13] at h00 h11 h02 h20 h22
  rw [← h11, mul_one] at h00 h22
  refine SL2_ext ?_ ?_ ?_ ?_
  · rw [← h00]
    simp
  · rw [h02]
    simp
  · rw [h20]
    simp
  · rw [← h22]
    simp

theorem unipU_zero_zero_eq_levi13 (c : F) : unipU F 0 0 c = levi13 F (uSL c) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [coe_unipU, coe_levi13]
  fin_cases i <;> fin_cases j <;> simp [uSL]

theorem torusSL_mul_levi13 (l : Fˣ) (B : SL2 F) :
    torusSL l * levi13 F B = levi13 F B * torusSL l := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_torusSL, coe_levi13]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, mul_comm]

variable (F) in
@[expose] def x0 : projectiveSL 3 F :=
  proj 3 F (unipU F 0 0 1)

theorem x0_mem_projCenterW : x0 F ∈ projCenterW F :=
  mem_projCenterW.2 ⟨1, rfl⟩

theorem x0_ne_one : x0 F ≠ 1 := by
  rw [x0, ne_eq, proj_unipU_eq_one_iff]
  simp

theorem x0_mul_self [CharP F 2] : x0 F * x0 F = 1 := by
  rw [x0, ← map_mul, unipU_mul_self, mul_zero, unipU_zero, map_one]

theorem commute_of_mem_projCenterW {z u : projectiveSL 3 F} (hz : z ∈ projCenterW F)
    (hu : u ∈ projUnip F) : z * u = u * z := by
  obtain ⟨c, rfl⟩ := mem_projCenterW.1 hz
  obtain ⟨a, b, c', rfl⟩ := mem_projUnip.1 hu
  rw [← map_mul, ← map_mul, unipU_mul, unipU_mul]
  congr 2 <;> ring

theorem x0_mul_comm {u : projectiveSL 3 F} (hu : u ∈ projUnip F) : x0 F * u = u * x0 F :=
  commute_of_mem_projCenterW x0_mem_projCenterW hu

theorem commutatorElement_mem_projCenterW {u v : projectiveSL 3 F} (hu : u ∈ projUnip F)
    (hv : v ∈ projUnip F) : ⁅u, v⁆ ∈ projCenterW F := by
  obtain ⟨a, b, c, rfl⟩ := mem_projUnip.1 hu
  obtain ⟨a', b', c', rfl⟩ := mem_projUnip.1 hv
  rw [← map_commutatorElement, commutatorElement_unipU]
  exact mem_projCenterW.2 ⟨_, rfl⟩

variable (F) in
@[expose] def projTorus (l : Fˣ) : projectiveSL 3 F :=
  proj 3 F (torusSL l)

theorem projTorus_conj (l : Fˣ) (a b c : F) :
    projTorus F l * proj 3 F (unipU F a b c) * (projTorus F l)⁻¹ =
      proj 3 F (unipU F ((l : F) ^ 3 * a) ((l : F)⁻¹ ^ 3 * b) c) := by
  rw [projTorus, ← map_inv, ← map_mul, ← map_mul, torusSL_conj_unipU]

theorem projTorus_conj_mem (l : Fˣ) {u : projectiveSL 3 F} (hu : u ∈ projUnip F) :
    projTorus F l * u * (projTorus F l)⁻¹ ∈ projUnip F := by
  obtain ⟨a, b, c, rfl⟩ := mem_projUnip.1 hu
  rw [projTorus_conj]
  exact mem_projUnip.2 ⟨_, _, _, rfl⟩

theorem projTorus_mul_comm_of_mem_projCenterW (l : Fˣ) {z : projectiveSL 3 F}
    (hz : z ∈ projCenterW F) : projTorus F l * z = z * projTorus F l := by
  obtain ⟨c, rfl⟩ := mem_projCenterW.1 hz
  rw [← mul_inv_eq_iff_eq_mul, projTorus_conj, mul_zero, mul_zero]

theorem projTorus_mul_projLevi (l : Fˣ) (B : SL2 F) :
    projTorus F l * projLevi F B = projLevi F B * projTorus F l := by
  rw [projTorus, projLevi_apply, ← map_mul, ← map_mul, torusSL_mul_levi13]

theorem commutatorElement_projTorus_not_mem {l : Fˣ} (hl : (l : F) ^ 3 ≠ 1) :
    ⁅projTorus F l, proj 3 F (unipU F 1 0 0)⁆ ∉ projCenterW F := by
  intro h
  obtain ⟨c, hc⟩ := mem_projCenterW.1 h
  rw [projTorus, ← map_commutatorElement, commutatorElement_torusSL_unipU] at hc
  obtain ⟨h1, -, -⟩ := unipU_eq_of_proj_eq hc
  apply hl
  linear_combination -h1

theorem exists_commutator_mul_eq {l : Fˣ} (hl : (l : F) ^ 3 ≠ 1) {u : projectiveSL 3 F}
    (hu : u ∈ projUnip F) :
    ∃ v ∈ projUnip F, ∃ v' ∈ projUnip F, ∃ v'' ∈ projUnip F,
      u = ⁅projTorus F l, v⁆ * ⁅v', v''⁆ := by
  obtain ⟨a', b', c', rfl⟩ := mem_projUnip.1 hu
  have hl0 : (l : F) ≠ 0 := l.ne_zero
  have h1 : (l : F) ^ 3 - 1 ≠ 0 := sub_ne_zero.2 hl
  have h2 : (l : F)⁻¹ ^ 3 - 1 ≠ 0 := by
    rw [inv_pow, sub_ne_zero, ne_eq, inv_eq_one]
    exact hl
  obtain ⟨a, ha⟩ : ∃ a : F, a = a' / ((l : F) ^ 3 - 1) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : F, b = b' / ((l : F)⁻¹ ^ 3 - 1) := ⟨_, rfl⟩
  refine ⟨proj 3 F (unipU F a b 0), mem_projUnip.2 ⟨_, _, _, rfl⟩,
    proj 3 F (unipU F (c' - (1 - (l : F) ^ 3) * (a * b)) 0 0), mem_projUnip.2 ⟨_, _, _, rfl⟩,
    proj 3 F (unipU F 0 1 0), mem_projUnip.2 ⟨_, _, _, rfl⟩, ?_⟩
  rw [projTorus, ← map_commutatorElement, ← map_commutatorElement, ← map_mul,
    commutatorElement_torusSL_unipU, commutatorElement_unipU, unipU_mul]
  congr 2
  · rw [ha]
    field_simp
    ring
  · rw [hb]
    field_simp
    ring
  · ring

theorem exists_commutator_sq_eq_x0 [CharP F 2] {l : Fˣ} (hl : (l : F) ^ 3 ≠ 1) :
    ∃ v ∈ projUnip F, ⁅projTorus F l, v⁆ * ⁅projTorus F l, v⁆ = x0 F := by
  have h1 : (l : F) ^ 3 - 1 ≠ 0 := sub_ne_zero.2 hl
  have h2 : (l : F)⁻¹ ^ 3 - 1 ≠ 0 := by
    rw [inv_pow, sub_ne_zero, ne_eq, inv_eq_one]
    exact hl
  refine ⟨proj 3 F (unipU F ((l : F) ^ 3 - 1)⁻¹ ((l : F)⁻¹ ^ 3 - 1)⁻¹ 0),
    mem_projUnip.2 ⟨_, _, _, rfl⟩, ?_⟩
  rw [projTorus, ← map_commutatorElement, ← map_mul, commutatorElement_torusSL_unipU,
    unipU_mul_self, x0]
  congr 2
  field_simp

theorem isPGroup_zpowers_of_pow_two {G : Type*} [Group G] {x : G} {k : ℕ} (hx : x ^ 2 ^ k = 1) :
    IsPGroup 2 (zpowers x) := by
  rintro ⟨y, hy⟩
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
  refine ⟨k, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hx,
    _root_.one_zpow]

theorem exists_conj_eq_x0 [Finite F] [CharP F 2] {p : projectiveSL 3 F} (hp : p * p = 1)
    (hp1 : p ≠ 1) : ∃ y : projectiveSL 3 F, y * p * y⁻¹ = x0 F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ :=
    (isPGroup_zpowers_of_pow_two (x := p) (k := 1) (by rw [pow_one, sq, hp])).exists_le_sylow
  obtain ⟨U₀, hU₀⟩ := exists_sylow_projUnitriangular (K := F) 2 (n := 3) (by norm_num)
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq (projectiveSL 3 F) S U₀
  have hpU : y * p * y⁻¹ ∈ projUnip F := by
    have hmem : MulAut.conj y p ∈ ((y • S : Sylow 2 (projectiveSL 3 F)) :
        Subgroup (projectiveSL 3 F)) :=
      Subgroup.mem_map_of_mem _ (hS (mem_zpowers p))
    rw [hy, hU₀, ← projUnip_eq_projUnitriangular, MulAut.conj_apply] at hmem
    exact hmem
  obtain ⟨a, b, c, habc⟩ := mem_projUnip.1 hpU
  have hsq : proj 3 F (unipU F 0 0 (a * b)) = 1 := by
    rw [← unipU_mul_self, map_mul, habc]
    calc y * p * y⁻¹ * (y * p * y⁻¹) = y * (p * p) * y⁻¹ := by group
      _ = 1 := by rw [hp, mul_one, mul_inv_cancel]
  have hab : a * b = 0 := (proj_unipU_eq_one_iff.1 hsq).2.2
  have hne : proj 3 F (unipU F a b c) ≠ 1 := by
    rw [habc]
    intro h
    apply hp1
    calc p = y⁻¹ * (y * p * y⁻¹) * y := by group
      _ = 1 := by rw [h, mul_one, inv_mul_cancel]
  have hx0 : ∀ i : Fin 2, x0 F ∈ projRad F i := fun i =>
    projCenterW_le_projRad i x0_mem_projCenterW
  rcases mul_eq_zero.1 hab with ha | hb
  · subst ha
    obtain ⟨g, hg⟩ := projRad_transitive 1 (mem_projRad_one.2 ⟨b, c, rfl⟩) (hx0 1) hne x0_ne_one
    refine ⟨g * y, ?_⟩
    rw [← hg, habc]
    group
  · subst hb
    obtain ⟨g, hg⟩ := projRad_transitive 0 (mem_projRad_zero.2 ⟨a, c, rfl⟩) (hx0 0) hne x0_ne_one
    refine ⟨g * y, ?_⟩
    rw [← hg, habc]
    group

theorem coe_pow_apply_self_of_mem_upperTriangular {n : ℕ} {A : SpecialLinearGroup (Fin n) F}
    (hA : A ∈ upperTriangular n F) (i : Fin n) (k : ℕ) :
    ((A ^ k : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i i =
      (A : Matrix (Fin n) (Fin n) F) i i ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul,
      mul_apply_self_of_isUpperTriangular
        (mem_upperTriangular_iff_isUpperTriangular.1 (pow_mem hA k))
        (mem_upperTriangular_iff_isUpperTriangular.1 hA), ih, pow_succ]

theorem eq_of_pow_two_pow_eq [CharP F 2] {x y : F} {k : ℕ} (h : x ^ 2 ^ k = y ^ 2 ^ k) :
    x = y := by
  have h1 : (x - y) ^ 2 ^ k = 0 := by rw [sub_pow_char_pow, h, sub_self]
  exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero k two_ne_zero) |>.1 h1)

theorem unipU_x0_mul_apply (Y : SpecialLinearGroup (Fin 3) F) (i j : Fin 3) :
    ((unipU F 0 0 1 * Y : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j =
      (Y : Matrix (Fin 3) (Fin 3) F) i j +
        if i = 0 then (Y : Matrix (Fin 3) (Fin 3) F) 2 j else 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_unipU]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem mul_unipU_x0_apply (Y : SpecialLinearGroup (Fin 3) F) (i j : Fin 3) :
    ((Y * unipU F 0 0 1 : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j =
      (Y : Matrix (Fin 3) (Fin 3) F) i j +
        if j = 2 then (Y : Matrix (Fin 3) (Fin 3) F) i 0 else 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_unipU]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, add_comm]

theorem mem_projUnip_of_commute_x0 [CharP F 2] {y : projectiveSL 3 F}
    (hy : y * x0 F = x0 F * y) {k : ℕ} (hk : y ^ 2 ^ k = 1) : y ∈ projUnip F := by
  obtain ⟨Y, rfl⟩ := proj_surjective 3 F y
  have h1 : proj 3 F (Y * unipU F 0 0 1) = proj 3 F (unipU F 0 0 1 * Y) := by
    rw [map_mul, map_mul]
    exact hy
  obtain ⟨ω, -, hω⟩ := eq_mul_scalar_of_proj_eq h1
  set M : Matrix (Fin 3) (Fin 3) F := (Y : Matrix (Fin 3) (Fin 3) F) with hM
  have hdet : M.det = 1 := Y.2
  have e : ∀ i j, M i j + (if i = 0 then M 2 j else 0) =
      (M i j + if j = 2 then M i 0 else 0) * (ω : F) := by
    intro i j
    have := congrFun (congrFun hω i) j
    rwa [mul_scalar_apply, unipU_x0_mul_apply, mul_unipU_x0_apply] at this
  have e10 := e 1 0
  have e20 := e 2 0
  have e00 := e 0 0
  have e01 := e 0 1
  have e12 := e 1 2
  have e02 := e 0 2
  simp only [ite_true, ite_false, Fin.isValue, Fin.reduceEq, add_zero] at e10 e20 e00 e01 e12 e02
  have hω1 : (ω : F) = 1 := by
    by_contra hne
    have hne' : (1 : F) - ω ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    have h10 : M 1 0 = 0 := by
      have : M 1 0 * (1 - ω) = 0 := by linear_combination e10
      exact (mul_eq_zero.1 this).resolve_right hne'
    have h20 : M 2 0 = 0 := by
      have : M 2 0 * (1 - ω) = 0 := by linear_combination e20
      exact (mul_eq_zero.1 this).resolve_right hne'
    have h00 : M 0 0 = 0 := by
      have : M 0 0 * (1 - ω) = 0 := by linear_combination e00 - h20
      exact (mul_eq_zero.1 this).resolve_right hne'
    rw [Matrix.det_fin_three, h00, h10, h20] at hdet
    simp at hdet
  rw [hω1] at e00 e01 e12 e02
  have h20 : M 2 0 = 0 := by linear_combination e00
  have h21 : M 2 1 = 0 := by linear_combination e01
  have h10 : M 1 0 = 0 := by linear_combination -e12
  have h22 : M 2 2 = M 0 0 := by linear_combination e02
  have hup : Y ∈ upperTriangular 3 F := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    · exact h10
    · exact h20
    · exact h21
  have hk' : proj 3 F (Y ^ 2 ^ k) = 1 := by rw [map_pow, hk]
  obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 hk')
  have d0 := congrFun (congrFun hc 0) 0
  have d1 := congrFun (congrFun hc 1) 1
  rw [coe_pow_apply_self_of_mem_upperTriangular hup] at d0 d1
  simp only [scalar_apply, diagonal_apply_eq] at d0 d1
  have h11 : M 1 1 = M 0 0 := eq_of_pow_two_pow_eq (k := k) (by rw [d0, d1])
  have h0 : M 0 0 ≠ 0 := by
    intro h
    rw [Matrix.det_fin_three, h10, h20, h21, h] at hdet
    simp at hdet
  have he3 : M 0 0 ^ 3 = 1 := by
    rw [Matrix.det_fin_three, h10, h20, h21, h11, h22] at hdet
    linear_combination hdet
  set e0 : Fˣ := Units.mk0 (M 0 0) h0
  have he0 : e0 ^ 3 = 1 := Units.ext (by simp [e0, he3])
  refine mem_projUnip.2 ⟨M 0 1 / M 0 0, M 1 2 / M 0 0, M 0 2 / M 0 0, ?_⟩
  have hY : Y = scalarElement e0 he0 *
      unipU F (M 0 1 / M 0 0) (M 1 2 / M 0 0) (M 0 2 / M 0 0) := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement, coe_unipU, scalar_apply, diagonal_mul]
    fin_cases i <;> fin_cases j <;> simp [e0, ← hM, h10, h20, h21, h11, h22] <;> field_simp
  rw [hY, map_mul, proj_eq_one_iff.2 (scalarElement_mem_scalars e0 he0), one_mul]

theorem exists_eq_map_conj_projUnip [Finite F] [CharP F 2] {Q : Subgroup (projectiveSL 3 F)}
    (hQ : IsPGroup 2 Q) (hcard : Nat.card Q = Nat.card (projUnip F)) :
    ∃ y : projectiveSL 3 F, Q = (projUnip F).map (MulAut.conj y : projectiveSL 3 F →* _) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U₀, hU₀⟩ := exists_sylow_projUnitriangular (K := F) 2 (n := 3) (by norm_num)
  obtain ⟨S, hS⟩ := hQ.exists_le_sylow
  have hSU : Nat.card (S : Subgroup (projectiveSL 3 F)) = Nat.card (projUnip F) := by
    rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity U₀, hU₀,
      projUnip_eq_projUnitriangular]
  have hQS : Q = S := eq_of_le_of_card_ge hS (by rw [hSU, hcard])
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq (projectiveSL 3 F) U₀ S
  refine ⟨y, ?_⟩
  rw [hQS, ← hy, projUnip_eq_projUnitriangular, ← hU₀]
  rfl

@[expose] def torusGL (b : Fˣ) : GL (Fin 3) F :=
  ⟨diagonal ![1, (b : F), 1], diagonal ![1, ((b⁻¹ : Fˣ) : F), 1], by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp, by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp⟩

theorem coe_torusGL (b : Fˣ) :
    ((torusGL b : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal ![1, (b : F), 1] :=
  rfl

theorem coe_torusGL_inv (b : Fˣ) :
    (((torusGL b)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal ![1, ((b⁻¹ : Fˣ) : F), 1] :=
  rfl

theorem torusGL_mul_levi13 (b : Fˣ) (B : SL2 F) :
    ((torusGL b : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        (levi13 F B : Matrix (Fin 3) (Fin 3) F) =
      (levi13 F B : Matrix (Fin 3) (Fin 3) F) *
        ((torusGL b : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  rw [coe_torusGL]
  ext i j
  rw [diagonal_mul, mul_diagonal, coe_levi13]
  fin_cases i <;> fin_cases j <;> simp

theorem conjAut_torusGL_projLevi (b : Fˣ) (B : SL2 F) :
    conjAut 3 F (torusGL b) (projLevi F B) = projLevi F B := by
  rw [projLevi_apply, conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, torusGL_mul_levi13, mul_assoc, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, mul_one]

theorem conj_projTorus (l : Fˣ) :
    MulAut.conj (projTorus F l) = conjAut 3 F (torusGL (l⁻¹ ^ 3)) := by
  have h : SpecialLinearGroup.toGL (torusSL l) =
      GeneralLinearGroup.scalar (Fin 3) l * torusGL (l⁻¹ ^ 3) := by
    apply Units.ext
    have hl : (l : F) ≠ 0 := l.ne_zero
    rw [Units.val_mul, coe_torusGL, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_torusSL]
    ext i j
    rw [mul_diagonal]
    fin_cases i <;> fin_cases j <;> simp [GeneralLinearGroup.scalar]
    field_simp
  rw [projTorus, ← conjAut_toGL, h, map_mul, conjAut_scalar, one_mul]

variable (F) in
@[expose] def blockDiag : Subgroup (SpecialLinearGroup (Fin 3) F) where
  carrier := {M | (M : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 ∧ (M : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧
    (M : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 ∧ (M : Matrix (Fin 3) (Fin 3) F) 2 1 = 0}
  one_mem' := by simp
  mul_mem' := by
    rintro M N ⟨h01, h10, h12, h21⟩ ⟨h01', h10', h12', h21'⟩
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_three]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [h01, h10, h12, h21, h01', h10', h12', h21']
  inv_mem' := by
    rintro M ⟨h01, h10, h12, h21⟩
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [h01, h10, h12, h21]

theorem mem_blockDiag {M : SpecialLinearGroup (Fin 3) F} :
    M ∈ blockDiag F ↔ (M : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 ∧
      (M : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ (M : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 ∧
      (M : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 :=
  Iff.rfl

theorem blockDiag_mid_ne_zero {M : SpecialLinearGroup (Fin 3) F} (hM : M ∈ blockDiag F) :
    (M : Matrix (Fin 3) (Fin 3) F) 1 1 ≠ 0 := by
  obtain ⟨h01, h10, h12, h21⟩ := hM
  intro h
  have hdet : (M : Matrix (Fin 3) (Fin 3) F).det = 1 := M.2
  rw [Matrix.det_fin_three, h01, h10, h12, h21, h] at hdet
  simp at hdet

theorem blockDiag_mid_mul {M N : SpecialLinearGroup (Fin 3) F} (hM : M ∈ blockDiag F) :
    ((M * N : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 1 =
      (M : Matrix (Fin 3) (Fin 3) F) 1 1 * (N : Matrix (Fin 3) (Fin 3) F) 1 1 := by
  obtain ⟨-, h10, h12, -⟩ := hM
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, h10, h12]
  ring

variable (F) in
@[expose] def blockDiagMid : blockDiag F →* Fˣ where
  toFun M := Units.mk0 (((M : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 1)
    (blockDiag_mid_ne_zero M.2)
  map_one' := by
    ext
    simp
  map_mul' M N := by
    ext
    simp only [Subgroup.coe_mul, Units.val_mk0, Units.val_mul]
    exact blockDiag_mid_mul M.2

theorem mem_range_levi13_of_mid {M : SpecialLinearGroup (Fin 3) F} (hM : M ∈ blockDiag F)
    (h11 : (M : Matrix (Fin 3) (Fin 3) F) 1 1 = 1) : M ∈ (levi13 F).range := by
  obtain ⟨h01, h10, h12, h21⟩ := hM
  set N := (M : Matrix (Fin 3) (Fin 3) F) with hN
  have hdet : N 0 0 * N 2 2 - N 0 2 * N 2 0 = 1 := by
    have h := M.2
    rw [Matrix.det_fin_three, ← hN, h01, h10, h12, h21, h11] at h
    linear_combination h
  let B : SL2 F := ⟨!![N 0 0, N 0 2; N 2 0, N 2 2], by rw [Matrix.det_fin_two_of]; exact hdet⟩
  refine ⟨B, ?_⟩
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [coe_levi13, ← hN]
  fin_cases i <;> fin_cases j <;> simp [B, h01, h10, h12, h21, h11]

theorem range_levi13_le_blockDiag : (levi13 F).range ≤ blockDiag F := by
  rintro _ ⟨B, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [coe_levi13]

theorem commutator_blockDiag_le : ⁅blockDiag F, blockDiag F⁆ ≤ (levi13 F).range := by
  rw [Subgroup.commutator_le]
  intro M hM N hN
  have hc : ⁅M, N⁆ ∈ blockDiag F := by
    rw [commutatorElement_def]
    exact (blockDiag F).mul_mem ((blockDiag F).mul_mem ((blockDiag F).mul_mem hM hN)
      ((blockDiag F).inv_mem hM)) ((blockDiag F).inv_mem hN)
  refine mem_range_levi13_of_mid hc ?_
  have h := map_commutatorElement (blockDiagMid F) (⟨M, hM⟩ : blockDiag F) ⟨N, hN⟩
  rw [commutatorElement_eq_one_iff_mul_comm.2
    (mul_comm (blockDiagMid F ⟨M, hM⟩) (blockDiagMid F ⟨N, hN⟩))] at h
  have h' := congrArg (fun u : Fˣ => (u : F)) h
  rw [Units.val_one] at h'
  exact h'

variable (F) in
@[expose] def fixTorus (b : Fˣ) : Subgroup (projectiveSL 3 F) where
  carrier := {p | conjAut 3 F (torusGL b) p = p}
  one_mem' := map_one _
  mul_mem' := by
    intro p q hp hq
    simp only [Set.mem_ofPred_eq] at hp hq ⊢
    rw [map_mul, hp, hq]
  inv_mem' := by
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp ⊢
    rw [map_inv, hp]

theorem mem_fixTorus {b : Fˣ} {p : projectiveSL 3 F} :
    p ∈ fixTorus F b ↔ conjAut 3 F (torusGL b) p = p :=
  Iff.rfl

theorem range_projLevi_le_fixTorus (b : Fˣ) : (projLevi F).range ≤ fixTorus F b := by
  rintro _ ⟨B, rfl⟩
  exact conjAut_torusGL_projLevi b B

theorem fixTorus_le_map_blockDiag {b : Fˣ} (hb : b ≠ 1) :
    fixTorus F b ≤ (blockDiag F).map (proj 3 F) := by
  intro p hp
  obtain ⟨M, rfl⟩ := proj_surjective 3 F p
  rw [mem_fixTorus, conjAut_proj] at hp
  obtain ⟨ω, -, hω⟩ := eq_mul_scalar_of_proj_eq hp
  have hb' : (b : F) ≠ 1 := fun h => hb (Units.ext h)
  have hb0 : (b : F) ≠ 0 := b.ne_zero
  have e : ∀ i j, (M : Matrix (Fin 3) (Fin 3) F) i j =
      ![1, (b : F), 1] i * (M : Matrix (Fin 3) (Fin 3) F) i j * ![1, ((b⁻¹ : Fˣ) : F), 1] j *
        ω := by
    intro i j
    have := congrFun (congrFun hω i) j
    rwa [mul_scalar_apply, coe_slConjugation, coe_torusGL, coe_torusGL_inv, mul_diagonal,
      diagonal_mul] at this
  have e00 := e 0 0
  have e02 := e 0 2
  have e20 := e 2 0
  have e22 := e 2 2
  have e11 := e 1 1
  have e01 := e 0 1
  have e10 := e 1 0
  have e12 := e 1 2
  have e21 := e 2 1
  simp at e00 e02 e20 e22 e11 e01 e10 e12 e21
  have hdet : (M : Matrix (Fin 3) (Fin 3) F).det = 1 := M.2
  have hω1 : (ω : F) = 1 := by
    by_contra hne
    have hne' : (1 : F) - ω ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    have z : ∀ x : F, x = x * ω → x = 0 := fun x hx =>
      (mul_eq_zero.1 (show x * (1 - ω) = 0 by linear_combination hx)).resolve_right hne'
    rw [Matrix.det_fin_three, z _ e00, z _ e02, z _ e20, z _ e22] at hdet
    simp at hdet
  rw [hω1, mul_one] at e01 e10 e12 e21
  refine ⟨M, ⟨?_, ?_, ?_, ?_⟩, rfl⟩
  · have : (M : Matrix (Fin 3) (Fin 3) F) 0 1 * ((b : F) - 1) = 0 := by
      field_simp at e01
      linear_combination e01
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hb')
  · have : (M : Matrix (Fin 3) (Fin 3) F) 1 0 * ((b : F) - 1) = 0 := by
      linear_combination -e10
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hb')
  · have : (M : Matrix (Fin 3) (Fin 3) F) 1 2 * ((b : F) - 1) = 0 := by
      linear_combination -e12
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hb')
  · have : (M : Matrix (Fin 3) (Fin 3) F) 2 1 * ((b : F) - 1) = 0 := by
      field_simp at e21
      linear_combination e21
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hb')

theorem commutator_range_projLevi [Group.IsPerfect (SL2 F)] :
    ⁅(projLevi F).range, (projLevi F).range⁆ = (projLevi F).range := by
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
    Group.IsPerfect.commutator_eq_top]

theorem commutator_fixTorus [Group.IsPerfect (SL2 F)] {b : Fˣ} (hb : b ≠ 1) :
    ⁅fixTorus F b, fixTorus F b⁆ = (projLevi F).range := by
  refine le_antisymm ?_ ?_
  · calc ⁅fixTorus F b, fixTorus F b⁆
        ≤ ⁅(blockDiag F).map (proj 3 F), (blockDiag F).map (proj 3 F)⁆ :=
          Subgroup.commutator_mono (fixTorus_le_map_blockDiag hb) (fixTorus_le_map_blockDiag hb)
      _ = ⁅blockDiag F, blockDiag F⁆.map (proj 3 F) := (Subgroup.map_commutator _ _ _).symm
      _ ≤ (levi13 F).range.map (proj 3 F) := Subgroup.map_mono commutator_blockDiag_le
      _ = (projLevi F).range := by rw [projLevi, MonoidHom.range_comp]
  · calc (projLevi F).range = ⁅(projLevi F).range, (projLevi F).range⁆ :=
          commutator_range_projLevi.symm
      _ ≤ ⁅fixTorus F b, fixTorus F b⁆ :=
          Subgroup.commutator_mono (range_projLevi_le_fixTorus b) (range_projLevi_le_fixTorus b)

end CFSG.ComponentClassification.RankTwoL3Even
