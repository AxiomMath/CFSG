module

public import CFSG.LieType.Chevalley.RankOneGaussian
public import Mathlib.Algebra.CharP.CharAndCard
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
public import Mathlib.FieldTheory.Finite.Basic

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

open Matrix Subgroup LinearFlag CFSG.LieType.Chevalley

variable (k : Type) [Field k]

@[expose] def unipU (a b c : k) : SpecialLinearGroup (Fin 3) k :=
  ⟨!![1, a, c; 0, 1, b; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

variable {k}

theorem coe_unipU (a b c : k) :
    (unipU k a b c : Matrix (Fin 3) (Fin 3) k) = !![1, a, c; 0, 1, b; 0, 0, 1] :=
  rfl

theorem unipU_mul (a b c a' b' c' : k) :
    unipU k a b c * unipU k a' b' c' = unipU k (a + a') (b + b') (c + c' + a * b') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_unipU, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem unipU_zero : unipU k 0 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_unipU]

theorem unipU_inv (a b c : k) : (unipU k a b c)⁻¹ = unipU k (-a) (-b) (-c + a * b) := by
  rw [inv_eq_iff_mul_eq_one, unipU_mul, ← unipU_zero]
  congr 1 <;> ring

@[expose] def leviOneMat (B : SL2 k) : SpecialLinearGroup (Fin 3) k :=
  ⟨!![1, 0, 0; 0, (B : Matrix (Fin 2) (Fin 2) k) 0 0, (B : Matrix (Fin 2) (Fin 2) k) 0 1;
      0, (B : Matrix (Fin 2) (Fin 2) k) 1 0, (B : Matrix (Fin 2) (Fin 2) k) 1 1], by
    simp [Matrix.det_fin_three]
    linear_combination det_SL2 B⟩

@[expose] def leviTwoMat (B : SL2 k) : SpecialLinearGroup (Fin 3) k :=
  ⟨!![(B : Matrix (Fin 2) (Fin 2) k) 0 0, (B : Matrix (Fin 2) (Fin 2) k) 0 1, 0;
      (B : Matrix (Fin 2) (Fin 2) k) 1 0, (B : Matrix (Fin 2) (Fin 2) k) 1 1, 0; 0, 0, 1], by
    simp [Matrix.det_fin_three]
    linear_combination det_SL2 B⟩

theorem coe_leviOneMat (B : SL2 k) :
    (leviOneMat B : Matrix (Fin 3) (Fin 3) k) =
      !![1, 0, 0; 0, (B : Matrix (Fin 2) (Fin 2) k) 0 0, (B : Matrix (Fin 2) (Fin 2) k) 0 1;
        0, (B : Matrix (Fin 2) (Fin 2) k) 1 0, (B : Matrix (Fin 2) (Fin 2) k) 1 1] :=
  rfl

theorem coe_leviTwoMat (B : SL2 k) :
    (leviTwoMat B : Matrix (Fin 3) (Fin 3) k) =
      !![(B : Matrix (Fin 2) (Fin 2) k) 0 0, (B : Matrix (Fin 2) (Fin 2) k) 0 1, 0;
        (B : Matrix (Fin 2) (Fin 2) k) 1 0, (B : Matrix (Fin 2) (Fin 2) k) 1 1, 0; 0, 0, 1] :=
  rfl

variable (k) in
@[expose] def leviOne : SL2 k →* SpecialLinearGroup (Fin 3) k where
  toFun := leviOneMat
  map_one' := by
    ext i j
    rw [coe_leviOneMat]
    fin_cases i <;> fin_cases j <;> simp
  map_mul' B B' := by
    ext i j
    rw [SpecialLinearGroup.coe_mul, coe_leviOneMat, coe_leviOneMat, coe_leviOneMat,
      SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

variable (k) in
@[expose] def leviTwo : SL2 k →* SpecialLinearGroup (Fin 3) k where
  toFun := leviTwoMat
  map_one' := by
    ext i j
    rw [coe_leviTwoMat]
    fin_cases i <;> fin_cases j <;> simp
  map_mul' B B' := by
    ext i j
    rw [SpecialLinearGroup.coe_mul, coe_leviTwoMat, coe_leviTwoMat, coe_leviTwoMat,
      SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem coe_leviOne (B : SL2 k) :
    (leviOne k B : Matrix (Fin 3) (Fin 3) k) =
      !![1, 0, 0; 0, (B : Matrix (Fin 2) (Fin 2) k) 0 0, (B : Matrix (Fin 2) (Fin 2) k) 0 1;
        0, (B : Matrix (Fin 2) (Fin 2) k) 1 0, (B : Matrix (Fin 2) (Fin 2) k) 1 1] :=
  rfl

theorem coe_leviTwo (B : SL2 k) :
    (leviTwo k B : Matrix (Fin 3) (Fin 3) k) =
      !![(B : Matrix (Fin 2) (Fin 2) k) 0 0, (B : Matrix (Fin 2) (Fin 2) k) 0 1, 0;
        (B : Matrix (Fin 2) (Fin 2) k) 1 0, (B : Matrix (Fin 2) (Fin 2) k) 1 1, 0; 0, 0, 1] :=
  rfl

variable (k) in
@[expose] def levi (i : Fin 2) : SL2 k →* SpecialLinearGroup (Fin 3) k :=
  ![leviOne k, leviTwo k] i

variable (k) in
@[expose] def unipAll : Subgroup (SpecialLinearGroup (Fin 3) k) where
  carrier := {A | ∃ a b c, unipU k a b c = A}
  mul_mem' := by
    rintro _ _ ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
    exact ⟨_, _, _, (unipU_mul a b c a' b' c').symm⟩
  one_mem' := ⟨0, 0, 0, unipU_zero⟩
  inv_mem' := by
    rintro _ ⟨a, b, c, rfl⟩
    exact ⟨_, _, _, (unipU_inv a b c).symm⟩

variable (k) in
@[expose] def unipOne : Subgroup (SpecialLinearGroup (Fin 3) k) where
  carrier := {A | ∃ a c, unipU k a 0 c = A}
  mul_mem' := by
    rintro _ _ ⟨a, c, rfl⟩ ⟨a', c', rfl⟩
    refine ⟨a + a', c + c', ?_⟩
    rw [unipU_mul]
    congr 1 <;> ring
  one_mem' := ⟨0, 0, unipU_zero⟩
  inv_mem' := by
    rintro _ ⟨a, c, rfl⟩
    refine ⟨-a, -c, ?_⟩
    rw [unipU_inv]
    congr 1 <;> ring

variable (k) in
@[expose] def unipTwo : Subgroup (SpecialLinearGroup (Fin 3) k) where
  carrier := {A | ∃ b c, unipU k 0 b c = A}
  mul_mem' := by
    rintro _ _ ⟨b, c, rfl⟩ ⟨b', c', rfl⟩
    refine ⟨b + b', c + c', ?_⟩
    rw [unipU_mul]
    congr 1 <;> ring
  one_mem' := ⟨0, 0, unipU_zero⟩
  inv_mem' := by
    rintro _ ⟨b, c, rfl⟩
    refine ⟨-b, -c, ?_⟩
    rw [unipU_inv]
    congr 1 <;> ring

variable (k) in
@[expose] def unipCenter : Subgroup (SpecialLinearGroup (Fin 3) k) where
  carrier := {A | ∃ c, unipU k 0 0 c = A}
  mul_mem' := by
    rintro _ _ ⟨c, rfl⟩ ⟨c', rfl⟩
    refine ⟨c + c', ?_⟩
    rw [unipU_mul]
    congr 1 <;> ring
  one_mem' := ⟨0, unipU_zero⟩
  inv_mem' := by
    rintro _ ⟨c, rfl⟩
    refine ⟨-c, ?_⟩
    rw [unipU_inv]
    congr 1 <;> ring

variable (k) in
@[expose] def projUnip : Subgroup (projectiveSL 3 k) :=
  (unipAll k).map (proj 3 k)

variable (k) in
@[expose] def projRad (i : Fin 2) : Subgroup (projectiveSL 3 k) :=
  ![(unipOne k).map (proj 3 k), (unipTwo k).map (proj 3 k)] i

variable (k) in
@[expose] def projCenterW : Subgroup (projectiveSL 3 k) :=
  (unipCenter k).map (proj 3 k)

theorem mem_projUnip {x : projectiveSL 3 k} :
    x ∈ projUnip k ↔ ∃ a b c, proj 3 k (unipU k a b c) = x := by
  constructor
  · rintro ⟨_, ⟨a, b, c, rfl⟩, rfl⟩
    exact ⟨a, b, c, rfl⟩
  · rintro ⟨a, b, c, rfl⟩
    exact ⟨_, ⟨a, b, c, rfl⟩, rfl⟩

theorem mem_projRad_zero {x : projectiveSL 3 k} :
    x ∈ projRad k 0 ↔ ∃ a c, proj 3 k (unipU k a 0 c) = x := by
  constructor
  · rintro ⟨_, ⟨a, c, rfl⟩, rfl⟩
    exact ⟨a, c, rfl⟩
  · rintro ⟨a, c, rfl⟩
    exact ⟨_, ⟨a, c, rfl⟩, rfl⟩

theorem mem_projRad_one {x : projectiveSL 3 k} :
    x ∈ projRad k 1 ↔ ∃ b c, proj 3 k (unipU k 0 b c) = x := by
  constructor
  · rintro ⟨_, ⟨b, c, rfl⟩, rfl⟩
    exact ⟨b, c, rfl⟩
  · rintro ⟨b, c, rfl⟩
    exact ⟨_, ⟨b, c, rfl⟩, rfl⟩

theorem mem_projCenterW {x : projectiveSL 3 k} :
    x ∈ projCenterW k ↔ ∃ c, proj 3 k (unipU k 0 0 c) = x := by
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, ⟨c, rfl⟩, rfl⟩

variable (k) in
@[expose] def sl2Unip : Subgroup (SL2 k) where
  carrier := {B | ∃ a, uSL a = B}
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨a', rfl⟩
    refine ⟨a + a', ?_⟩
    refine SL2_ext ?_ ?_ ?_ ?_ <;>
      simp [coe_uSL, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, add_comm]
  one_mem' := ⟨0, SL2_ext (by simp [coe_uSL]) (by simp [coe_uSL]) (by simp [coe_uSL])
    (by simp [coe_uSL])⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    refine ⟨-a, ?_⟩
    rw [eq_inv_iff_mul_eq_one]
    refine SL2_ext ?_ ?_ ?_ ?_ <;>
      simp [coe_uSL, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem mem_sl2Unip {B : SL2 k} : B ∈ sl2Unip k ↔ ∃ a, uSL a = B :=
  Iff.rfl

theorem eq_mul_scalar_of_proj_eq {A B : SpecialLinearGroup (Fin 3) k}
    (h : proj 3 k A = proj 3 k B) :
    ∃ c : kˣ, c ^ 3 = 1 ∧ (B : Matrix (Fin 3) (Fin 3) k) =
      (A : Matrix (Fin 3) (Fin 3) k) * scalar (Fin 3) (c : k) := by
  obtain ⟨c, hc, hAB⟩ := mem_scalars.1 (proj_eq_proj_iff.1 h)
  refine ⟨c, hc, ?_⟩
  rw [← hAB, ← SpecialLinearGroup.coe_mul, mul_inv_cancel_left]

theorem mul_scalar_apply (A : Matrix (Fin 3) (Fin 3) k) (c : k) (i j : Fin 3) :
    (A * scalar (Fin 3) c) i j = A i j * c := by
  rw [scalar_apply, mul_diagonal]

theorem unipU_eq_of_proj_eq {a b c a' b' c' : k}
    (h : proj 3 k (unipU k a b c) = proj 3 k (unipU k a' b' c')) :
    a = a' ∧ b = b' ∧ c = c' := by
  obtain ⟨d, -, hd⟩ := eq_mul_scalar_of_proj_eq h
  have h00 := congrFun (congrFun hd 0) 0
  have h01 := congrFun (congrFun hd 0) 1
  have h12 := congrFun (congrFun hd 1) 2
  have h02 := congrFun (congrFun hd 0) 2
  simp only [mul_scalar_apply, coe_unipU] at h00 h01 h12 h02
  simp at h00 h01 h12 h02
  rw [← h00, mul_one] at h01 h12 h02
  exact ⟨h01.symm, h12.symm, h02.symm⟩

theorem proj_unipU_eq_one_iff {a b c : k} :
    proj 3 k (unipU k a b c) = 1 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro h
    rw [← map_one (proj 3 k), ← unipU_zero] at h
    exact unipU_eq_of_proj_eq h
  · rintro ⟨rfl, rfl, rfl⟩
    rw [unipU_zero, map_one]

section FieldFour

variable [Finite k]

theorem charP_two_of_card (hk : Nat.card k = 4) : CharP k 2 := by
  have := Fintype.ofFinite k
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hk]; norm_num)

theorem two_eq_zero_of_card (hk : Nat.card k = 4) : (2 : k) = 0 := by
  have := charP_two_of_card hk
  exact CharTwo.two_eq_zero

theorem three_ne_zero_of_card (hk : Nat.card k = 4) : (3 : k) ≠ 0 := by
  rw [show (3 : k) = 2 + 1 by norm_num, two_eq_zero_of_card hk, zero_add]
  exact one_ne_zero

theorem neg_eq_self_of_card (hk : Nat.card k = 4) (x : k) : -x = x := by
  have := charP_two_of_card hk
  exact CharTwo.neg_eq x

theorem pow_three_eq_one_of_card (hk : Nat.card k = 4) {x : k} (hx : x ≠ 0) : x ^ 3 = 1 := by
  have := Fintype.ofFinite k
  have h := FiniteField.pow_card_sub_one_eq_one x hx
  rwa [← Nat.card_eq_fintype_card, hk] at h

theorem exists_ne_zero_ne_one_of_card (hk : Nat.card k = 4) : ∃ t : k, t ≠ 0 ∧ t ≠ 1 := by
  by_contra h
  have h' : ∀ t : k, t ≠ 0 → t = 1 := fun t ht => by
    by_contra h1
    exact h ⟨t, ht, h1⟩
  have := Fintype.ofFinite k
  classical
  have hsub : (Finset.univ : Finset k) ⊆ {0, 1} := fun t _ => by
    by_cases ht : t = 0
    · simp [ht]
    · simp [h' t ht]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hk] at h1
  have h2 := Finset.card_insert_le (0 : k) {1}
  rw [Finset.card_singleton] at h2
  omega

end FieldFour

theorem trace_mul_scalar (A : Matrix (Fin 3) (Fin 3) k) (c : k) :
    trace (A * scalar (Fin 3) c) = c * trace A := by
  simp only [trace_fin_three, mul_scalar_apply]
  ring

theorem trace_conj (g x : SpecialLinearGroup (Fin 3) k) :
    trace ((g⁻¹ * x * g : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      trace (x : Matrix (Fin 3) (Fin 3) k) := by
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, Matrix.trace_mul_cycle,
    ← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one, one_mul]

theorem trace_unipU (a b c : k) : trace (unipU k a b c : Matrix (Fin 3) (Fin 3) k) = 3 := by
  simp [trace_fin_three, coe_unipU]
  norm_num

theorem exists_mul_eq_mul_of_mem_normalizer {U' : Subgroup (SpecialLinearGroup (Fin 3) k)}
    (htr : ∀ y ∈ U', trace (y : Matrix (Fin 3) (Fin 3) k) = 3) (h3 : (3 : k) ≠ 0)
    {g : SpecialLinearGroup (Fin 3) k}
    (hg : proj 3 k g ∈ normalizer ((U'.map (proj 3 k) : Subgroup _) : Set (projectiveSL 3 k)))
    {x : SpecialLinearGroup (Fin 3) k} (hx : x ∈ U') : ∃ y ∈ U', x * g = g * y := by
  have hg' : proj 3 k g⁻¹ ∈ normalizer ((U'.map (proj 3 k) : Subgroup _) :
      Set (projectiveSL 3 k)) := by
    rw [map_inv]
    exact inv_mem hg
  have hmem : proj 3 k (g⁻¹ * x * g) ∈ U'.map (proj 3 k) := by
    have h := (mem_normalizer_iff.1 hg' (proj 3 k x)).1 ⟨x, hx, rfl⟩
    rwa [← map_inv, inv_inv, ← map_mul, ← map_mul] at h
  obtain ⟨y, hy, hyx⟩ := hmem
  obtain ⟨c, -, hc⟩ := eq_mul_scalar_of_proj_eq hyx
  have hc1 : (c : k) = 1 := by
    have h1 := congrArg Matrix.trace hc
    rw [trace_conj, htr x hx, trace_mul_scalar, htr y hy] at h1
    have h2 : ((c : k) - 1) * 3 = 0 := by linear_combination -h1
    rcases mul_eq_zero.1 h2 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h h3
  refine ⟨y, hy, ?_⟩
  have : g⁻¹ * x * g = y := Subtype.ext (by
    rw [hc, hc1, scalar_apply, diagonal_one, mul_one])
  rw [← this]
  group

theorem scalar_mul_apply (A : Matrix (Fin 3) (Fin 3) k) (c : k) (i j : Fin 3) :
    (scalar (Fin 3) c * A) i j = c * A i j := by
  rw [scalar_apply, diagonal_mul]

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] {R : Subgroup G} {g : G}
    (h1 : ∀ x ∈ R, g * x * g⁻¹ ∈ R) (h2 : ∀ x ∈ R, g⁻¹ * x * g ∈ R) :
    g ∈ normalizer (R : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have h := h2 _ hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h

theorem proj_unipU_ne_one {a b c : k} (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    proj 3 k (unipU k a b c) ≠ 1 := by
  rw [Ne, proj_unipU_eq_one_iff]
  rintro ⟨rfl, rfl, rfl⟩
  simp at h

theorem projRad_zero : projRad k 0 = (unipOne k).map (proj 3 k) :=
  rfl

theorem projRad_one : projRad k 1 = (unipTwo k).map (proj 3 k) :=
  rfl

theorem levi_zero : levi k 0 = leviOne k :=
  rfl

theorem levi_one : levi k 1 = leviTwo k :=
  rfl

theorem leviOne_mul_unipU (B : SL2 k) (a c : k) :
    leviOne k B * unipU k a 0 c =
      unipU k (a * (B : Matrix (Fin 2) (Fin 2) k) 1 1 - c * (B : Matrix (Fin 2) (Fin 2) k) 1 0) 0
        (c * (B : Matrix (Fin 2) (Fin 2) k) 0 0 - a * (B : Matrix (Fin 2) (Fin 2) k) 0 1) *
        leviOne k B := by
  have hB := det_SL2 B
  ext i j
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, coe_leviOne, coe_unipU, coe_unipU]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · linear_combination (-a) * hB
  · linear_combination (-c) * hB

theorem leviOne_conj_mem (B : SL2 k) {x : projectiveSL 3 k} (hx : x ∈ projRad k 0) :
    proj 3 k (leviOne k B) * x * (proj 3 k (leviOne k B))⁻¹ ∈ projRad k 0 := by
  obtain ⟨a, c, rfl⟩ := mem_projRad_zero.1 hx
  rw [← map_inv, ← map_mul, ← map_mul, mul_inv_eq_iff_eq_mul.2 (leviOne_mul_unipU B a c)]
  exact mem_projRad_zero.2 ⟨_, _, rfl⟩

theorem leviOne_mem_normalizer (B : SL2 k) :
    proj 3 k (leviOne k B) ∈ normalizer (projRad k 0 : Set (projectiveSL 3 k)) := by
  refine mem_normalizer_of_conj_mem (fun x hx => leviOne_conj_mem B hx) fun x hx => ?_
  have h := leviOne_conj_mem B⁻¹ hx
  rwa [map_inv, map_inv, inv_inv] at h

theorem col_zero_of_mem_normalizer (h3 : (3 : k) ≠ 0) {g : SpecialLinearGroup (Fin 3) k}
    (hg : proj 3 k g ∈ normalizer (projRad k 0 : Set (projectiveSL 3 k))) :
    (g : Matrix (Fin 3) (Fin 3) k) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) k) 2 0 = 0 := by
  have htr : ∀ y ∈ unipOne k, trace (y : Matrix (Fin 3) (Fin 3) k) = 3 := by
    rintro _ ⟨a, c, rfl⟩
    exact trace_unipU a 0 c
  rw [projRad_zero] at hg
  obtain ⟨y, ⟨a, c, rfl⟩, hy⟩ :=
    exists_mul_eq_mul_of_mem_normalizer htr h3 hg (x := unipU k 1 0 0) ⟨1, 0, rfl⟩
  obtain ⟨y', ⟨a', c', rfl⟩, hy'⟩ :=
    exists_mul_eq_mul_of_mem_normalizer htr h3 hg (x := unipU k 0 0 1) ⟨0, 1, rfl⟩
  have e1 := congrArg (fun M : SpecialLinearGroup (Fin 3) k =>
    (M : Matrix (Fin 3) (Fin 3) k) 0 0) hy
  have e2 := congrArg (fun M : SpecialLinearGroup (Fin 3) k =>
    (M : Matrix (Fin 3) (Fin 3) k) 0 0) hy'
  simp [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, coe_unipU] at e1 e2
  exact ⟨e1, e2⟩

theorem eq_unipU_mul_leviOne {g : SpecialLinearGroup (Fin 3) k}
    (h00 : (g : Matrix (Fin 3) (Fin 3) k) 0 0 = 1) (h10 : (g : Matrix (Fin 3) (Fin 3) k) 1 0 = 0)
    (h20 : (g : Matrix (Fin 3) (Fin 3) k) 2 0 = 0) :
    ∃ (a c : k) (B : SL2 k), g = unipU k a 0 c * leviOne k B := by
  have hdet : (g : Matrix (Fin 3) (Fin 3) k) 1 1 * (g : Matrix (Fin 3) (Fin 3) k) 2 2 -
      (g : Matrix (Fin 3) (Fin 3) k) 1 2 * (g : Matrix (Fin 3) (Fin 3) k) 2 1 = 1 := by
    have h := g.2
    rw [Matrix.det_fin_three, h00, h10, h20] at h
    linear_combination h
  set M := (g : Matrix (Fin 3) (Fin 3) k) with hM
  let B : SL2 k := ⟨!![M 1 1, M 1 2; M 2 1, M 2 2], by rw [Matrix.det_fin_two_of]; exact hdet⟩
  refine ⟨M 0 1 * M 2 2 - M 0 2 * M 2 1, M 0 2 * M 1 1 - M 0 1 * M 1 2, B, ?_⟩
  ext i j
  rw [SpecialLinearGroup.coe_mul, coe_unipU, coe_leviOne, ← hM]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, B, h00, h10, h20]
  · linear_combination (-M 0 1) * hdet
  · linear_combination (-M 0 2) * hdet

section FieldFourParabolic

variable [Finite k] (hk : Nat.card k = 4)
include hk

theorem exists_proj_eq_scalar_mul {g : SpecialLinearGroup (Fin 3) k} {i : Fin 3}
    (hα : (g : Matrix (Fin 3) (Fin 3) k) i i ≠ 0) :
    ∃ g' : SpecialLinearGroup (Fin 3) k, proj 3 k g' = proj 3 k g ∧
      ∀ j l, (g' : Matrix (Fin 3) (Fin 3) k) j l =
        ((g : Matrix (Fin 3) (Fin 3) k) i i)⁻¹ * (g : Matrix (Fin 3) (Fin 3) k) j l := by
  set α := Units.mk0 _ hα with hαdef
  have hα3 : α⁻¹ ^ 3 = 1 := by
    rw [inv_pow, inv_eq_one]
    ext
    rw [Units.val_pow_eq_pow_val, hαdef, Units.val_mk0, Units.val_one]
    exact pow_three_eq_one_of_card hk hα
  refine ⟨scalarElement α⁻¹ hα3 * g, ?_, fun j l => ?_⟩
  · rw [map_mul, (proj_eq_one_iff).2 (scalarElement_mem_scalars _ _), one_mul]
  · rw [SpecialLinearGroup.coe_mul, coe_scalarElement, scalar_mul_apply, Units.val_inv_eq_inv_val,
      hαdef, Units.val_mk0]

theorem normalizer_projRad_zero :
    normalizer (projRad k 0 : Set (projectiveSL 3 k)) =
      projRad k 0 ⊔ ((proj 3 k).comp (leviOne k)).range := by
  refine le_antisymm (fun x hx => ?_) (sup_le le_normalizer ?_)
  · obtain ⟨g, rfl⟩ := proj_surjective 3 k x
    obtain ⟨h10, h20⟩ := col_zero_of_mem_normalizer (three_ne_zero_of_card hk) hx
    have hdet := g.2
    rw [Matrix.det_fin_three, h10, h20] at hdet
    have hα : (g : Matrix (Fin 3) (Fin 3) k) 0 0 ≠ 0 := by
      intro h
      rw [h] at hdet
      simp at hdet
    obtain ⟨g', hg', hentry⟩ := exists_proj_eq_scalar_mul hk hα
    obtain ⟨a, c, B, hB⟩ := eq_unipU_mul_leviOne (g := g')
      (by rw [hentry, inv_mul_cancel₀ hα]) (by rw [hentry, h10, mul_zero])
      (by rw [hentry, h20, mul_zero])
    rw [← hg', hB, map_mul]
    exact mul_mem_sup (mem_projRad_zero.2 ⟨a, c, rfl⟩) ⟨B, rfl⟩
  · rintro _ ⟨B, rfl⟩
    exact leviOne_mem_normalizer B

omit [Finite k] hk in
theorem projRad_zero_inf_range : projRad k 0 ⊓ ((proj 3 k).comp (leviOne k)).range = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, B, rfl⟩
  obtain ⟨a, c, hac⟩ := mem_projRad_zero.1 hx1
  obtain ⟨d, -, hd⟩ := eq_mul_scalar_of_proj_eq hac
  have h00 := congrFun (congrFun hd 0) 0
  have h01 := congrFun (congrFun hd 0) 1
  have h02 := congrFun (congrFun hd 0) 2
  simp [coe_unipU, coe_leviOne] at h00 h01 h02
  rw [Subgroup.mem_bot, ← hac, h01, h02, unipU_zero, map_one]

omit [Finite k] hk in
theorem leviOne_proj_injective : Function.Injective ((proj 3 k).comp (leviOne k)) := by
  rw [injective_iff_map_eq_one]
  intro B hB
  rw [MonoidHom.comp_apply, ← map_one (proj 3 k)] at hB
  obtain ⟨d, -, hd⟩ := eq_mul_scalar_of_proj_eq hB
  have h00 := congrFun (congrFun hd 0) 0
  have h11 := congrFun (congrFun hd 1) 1
  have h12 := congrFun (congrFun hd 1) 2
  have h21 := congrFun (congrFun hd 2) 1
  have h22 := congrFun (congrFun hd 2) 2
  simp [coe_leviOne] at h00 h11 h12 h21 h22
  rw [← h00, mul_one] at h11 h22
  refine SL2_ext ?_ ?_ ?_ ?_
  · rw [← h11]
    simp
  · rw [h12]
    simp
  · rw [h21]
    simp
  · rw [← h22]
    simp

omit [Finite k] hk in
theorem exists_leviOne_conj_base {a c : k} (h : a ≠ 0 ∨ c ≠ 0) :
    ∃ B : SL2 k, leviOne k B * unipU k 1 0 0 * (leviOne k B)⁻¹ = unipU k a 0 c := by
  have key : ∀ B : SL2 k, (B : Matrix (Fin 2) (Fin 2) k) 1 1 = a →
      -(B : Matrix (Fin 2) (Fin 2) k) 0 1 = c →
        leviOne k B * unipU k 1 0 0 * (leviOne k B)⁻¹ = unipU k a 0 c := by
    intro B h11 h01
    rw [mul_inv_eq_iff_eq_mul, leviOne_mul_unipU, h11, ← h01]
    congr 2 <;> ring
  by_cases ha : a = 0
  · have hc : c ≠ 0 := h.resolve_left (not_not.2 ha)
    refine ⟨⟨!![0, -c; c⁻¹, 0], by rw [Matrix.det_fin_two_of]; simp [hc]⟩, key _ ?_ ?_⟩
    · simp [ha]
    · simp
  · refine ⟨⟨!![a⁻¹, -c; 0, a], by rw [Matrix.det_fin_two_of]; simp [ha]⟩, key _ ?_ ?_⟩
    · simp
    · simp

omit [Finite k] hk in
theorem projRad_zero_transitive {r : projectiveSL 3 k} (hr : r ∈ projRad k 0)
    {s : projectiveSL 3 k} (hs : s ∈ projRad k 0) (hr1 : r ≠ 1) (hs1 : s ≠ 1) :
    ∃ B : SL2 k, proj 3 k (leviOne k B) * r * (proj 3 k (leviOne k B))⁻¹ = s := by
  obtain ⟨a, c, rfl⟩ := mem_projRad_zero.1 hr
  obtain ⟨a', c', rfl⟩ := mem_projRad_zero.1 hs
  have hne : ∀ {a c : k}, proj 3 k (unipU k a 0 c) ≠ 1 → a ≠ 0 ∨ c ≠ 0 := by
    intro a c h
    by_contra h'
    simp only [ne_eq, not_or, not_not] at h'
    exact h (proj_unipU_eq_one_iff.2 ⟨h'.1, rfl, h'.2⟩)
  obtain ⟨B, hB⟩ := exists_leviOne_conj_base (hne hr1)
  obtain ⟨B', hB'⟩ := exists_leviOne_conj_base (hne hs1)
  refine ⟨B' * B⁻¹, ?_⟩
  rw [← hB, ← hB']
  simp only [map_mul, map_inv]
  group

end FieldFourParabolic

theorem sq_eq_one_of_mem_projRad [Finite k] (hk : Nat.card k = 4) (i : Fin 2)
    {r : projectiveSL 3 k} (hr : r ∈ projRad k i) : r ^ 2 = 1 := by
  have := charP_two_of_card hk
  fin_cases i
  · obtain ⟨a, c, rfl⟩ := mem_projRad_zero.1 hr
    rw [← map_pow, sq, unipU_mul]
    simp only [CharTwo.add_self_eq_zero, mul_zero, unipU_zero, map_one]
  · obtain ⟨b, c, rfl⟩ := mem_projRad_one.1 hr
    rw [← map_pow, sq, unipU_mul]
    simp only [CharTwo.add_self_eq_zero, zero_mul, unipU_zero, map_one]

theorem commute_of_mem_projRad (i : Fin 2) {r s : projectiveSL 3 k} (hr : r ∈ projRad k i)
    (hs : s ∈ projRad k i) : r * s = s * r := by
  fin_cases i
  · obtain ⟨a, c, rfl⟩ := mem_projRad_zero.1 hr
    obtain ⟨a', c', rfl⟩ := mem_projRad_zero.1 hs
    rw [← map_mul, ← map_mul, unipU_mul, unipU_mul]
    congr 2 <;> ring
  · obtain ⟨b, c, rfl⟩ := mem_projRad_one.1 hr
    obtain ⟨b', c', rfl⟩ := mem_projRad_one.1 hs
    rw [← map_mul, ← map_mul, unipU_mul, unipU_mul]
    congr 2 <;> ring

theorem card_projRad [Finite k] (i : Fin 2) : Nat.card (projRad k i) = Nat.card k * Nat.card k := by
  fin_cases i
  · change Nat.card (projRad k 0) = _
    let f : k × k → projRad k 0 := fun p =>
      ⟨proj 3 k (unipU k p.1 0 p.2), mem_projRad_zero.2 ⟨_, _, rfl⟩⟩
    have hf : Function.Bijective f := by
      refine ⟨fun p q h => ?_, fun x => ?_⟩
      · obtain ⟨h1, -, h3⟩ := unipU_eq_of_proj_eq (congrArg Subtype.val h)
        exact Prod.ext h1 h3
      · obtain ⟨a, c, h⟩ := mem_projRad_zero.1 x.2
        exact ⟨(a, c), Subtype.ext h⟩
    rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]
  · change Nat.card (projRad k 1) = _
    let f : k × k → projRad k 1 := fun p =>
      ⟨proj 3 k (unipU k 0 p.1 p.2), mem_projRad_one.2 ⟨_, _, rfl⟩⟩
    have hf : Function.Bijective f := by
      refine ⟨fun p q h => ?_, fun x => ?_⟩
      · obtain ⟨-, h2, h3⟩ := unipU_eq_of_proj_eq (congrArg Subtype.val h)
        exact Prod.ext h2 h3
      · obtain ⟨b, c, h⟩ := mem_projRad_one.1 x.2
        exact ⟨(b, c), Subtype.ext h⟩
    rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]

theorem leviTwo_mul_unipU (B : SL2 k) (b c : k) :
    leviTwo k B * unipU k 0 b c =
      unipU k 0 ((B : Matrix (Fin 2) (Fin 2) k) 1 0 * c + (B : Matrix (Fin 2) (Fin 2) k) 1 1 * b)
        ((B : Matrix (Fin 2) (Fin 2) k) 0 0 * c + (B : Matrix (Fin 2) (Fin 2) k) 0 1 * b) *
        leviTwo k B := by
  ext i j
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, coe_leviTwo, coe_unipU, coe_unipU]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem leviTwo_conj_mem (B : SL2 k) {x : projectiveSL 3 k} (hx : x ∈ projRad k 1) :
    proj 3 k (leviTwo k B) * x * (proj 3 k (leviTwo k B))⁻¹ ∈ projRad k 1 := by
  obtain ⟨b, c, rfl⟩ := mem_projRad_one.1 hx
  rw [← map_inv, ← map_mul, ← map_mul, mul_inv_eq_iff_eq_mul.2 (leviTwo_mul_unipU B b c)]
  exact mem_projRad_one.2 ⟨_, _, rfl⟩

theorem leviTwo_mem_normalizer (B : SL2 k) :
    proj 3 k (leviTwo k B) ∈ normalizer (projRad k 1 : Set (projectiveSL 3 k)) := by
  refine mem_normalizer_of_conj_mem (fun x hx => leviTwo_conj_mem B hx) fun x hx => ?_
  have h := leviTwo_conj_mem B⁻¹ hx
  rwa [map_inv, map_inv, inv_inv] at h

theorem row_two_of_mem_normalizer (h3 : (3 : k) ≠ 0) {g : SpecialLinearGroup (Fin 3) k}
    (hg : proj 3 k g ∈ normalizer (projRad k 1 : Set (projectiveSL 3 k))) :
    (g : Matrix (Fin 3) (Fin 3) k) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) k) 2 1 = 0 := by
  have htr : ∀ y ∈ unipTwo k, trace (y : Matrix (Fin 3) (Fin 3) k) = 3 := by
    rintro _ ⟨b, c, rfl⟩
    exact trace_unipU 0 b c
  rw [projRad_one] at hg
  obtain ⟨y, ⟨b, c, rfl⟩, hy⟩ :=
    exists_mul_eq_mul_of_mem_normalizer htr h3 hg (x := unipU k 0 1 0) ⟨1, 0, rfl⟩
  have e1 := congrArg (fun M : SpecialLinearGroup (Fin 3) k =>
    (M : Matrix (Fin 3) (Fin 3) k) 1 0) hy
  have e2 := congrArg (fun M : SpecialLinearGroup (Fin 3) k =>
    (M : Matrix (Fin 3) (Fin 3) k) 1 1) hy
  simp [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, coe_unipU] at e1 e2
  exact ⟨e1, e2⟩

theorem eq_unipU_mul_leviTwo {g : SpecialLinearGroup (Fin 3) k}
    (h22 : (g : Matrix (Fin 3) (Fin 3) k) 2 2 = 1) (h20 : (g : Matrix (Fin 3) (Fin 3) k) 2 0 = 0)
    (h21 : (g : Matrix (Fin 3) (Fin 3) k) 2 1 = 0) :
    ∃ (b c : k) (B : SL2 k), g = unipU k 0 b c * leviTwo k B := by
  have hdet : (g : Matrix (Fin 3) (Fin 3) k) 0 0 * (g : Matrix (Fin 3) (Fin 3) k) 1 1 -
      (g : Matrix (Fin 3) (Fin 3) k) 0 1 * (g : Matrix (Fin 3) (Fin 3) k) 1 0 = 1 := by
    have h := g.2
    rw [Matrix.det_fin_three, h22, h20, h21] at h
    linear_combination h
  set M := (g : Matrix (Fin 3) (Fin 3) k) with hM
  let B : SL2 k := ⟨!![M 0 0, M 0 1; M 1 0, M 1 1], by rw [Matrix.det_fin_two_of]; exact hdet⟩
  refine ⟨M 1 2, M 0 2, B, ?_⟩
  ext i j
  rw [SpecialLinearGroup.coe_mul, coe_unipU, coe_leviTwo, ← hM]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, B, h22, h20, h21]

theorem projRad_one_inf_range : projRad k 1 ⊓ ((proj 3 k).comp (leviTwo k)).range = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, B, rfl⟩
  obtain ⟨b, c, hbc⟩ := mem_projRad_one.1 hx1
  obtain ⟨d, -, hd⟩ := eq_mul_scalar_of_proj_eq hbc
  have h22 := congrFun (congrFun hd 2) 2
  have h12 := congrFun (congrFun hd 1) 2
  have h02 := congrFun (congrFun hd 0) 2
  simp [coe_unipU, coe_leviTwo] at h22 h12 h02
  rw [Subgroup.mem_bot, ← hbc, h12, h02, unipU_zero, map_one]

theorem leviTwo_proj_injective : Function.Injective ((proj 3 k).comp (leviTwo k)) := by
  rw [injective_iff_map_eq_one]
  intro B hB
  rw [MonoidHom.comp_apply, ← map_one (proj 3 k)] at hB
  obtain ⟨d, -, hd⟩ := eq_mul_scalar_of_proj_eq hB
  have h22 := congrFun (congrFun hd 2) 2
  have h00 := congrFun (congrFun hd 0) 0
  have h01 := congrFun (congrFun hd 0) 1
  have h10 := congrFun (congrFun hd 1) 0
  have h11 := congrFun (congrFun hd 1) 1
  simp [coe_leviTwo] at h22 h00 h01 h10 h11
  rw [← h22, mul_one] at h00 h11
  refine SL2_ext ?_ ?_ ?_ ?_
  · rw [← h00]
    simp
  · rw [h01]
    simp
  · rw [h10]
    simp
  · rw [← h11]
    simp

theorem exists_leviTwo_conj_base {b c : k} (h : b ≠ 0 ∨ c ≠ 0) :
    ∃ B : SL2 k, leviTwo k B * unipU k 0 0 1 * (leviTwo k B)⁻¹ = unipU k 0 b c := by
  have key : ∀ B : SL2 k, (B : Matrix (Fin 2) (Fin 2) k) 1 0 = b →
      (B : Matrix (Fin 2) (Fin 2) k) 0 0 = c →
        leviTwo k B * unipU k 0 0 1 * (leviTwo k B)⁻¹ = unipU k 0 b c := by
    intro B h10 h00
    rw [mul_inv_eq_iff_eq_mul, leviTwo_mul_unipU, h10, h00]
    congr 2 <;> ring
  by_cases hc : c = 0
  · have hb : b ≠ 0 := h.resolve_right (not_not.2 hc)
    refine ⟨⟨!![0, -b⁻¹; b, 0], by rw [Matrix.det_fin_two_of]; simp [hb]⟩, key _ ?_ ?_⟩
    · simp
    · simp [hc]
  · refine ⟨⟨!![c, 0; b, c⁻¹], by rw [Matrix.det_fin_two_of]; simp [hc]⟩, key _ ?_ ?_⟩
    · simp
    · simp

theorem projRad_one_transitive {r : projectiveSL 3 k} (hr : r ∈ projRad k 1)
    {s : projectiveSL 3 k} (hs : s ∈ projRad k 1) (hr1 : r ≠ 1) (hs1 : s ≠ 1) :
    ∃ B : SL2 k, proj 3 k (leviTwo k B) * r * (proj 3 k (leviTwo k B))⁻¹ = s := by
  obtain ⟨b, c, rfl⟩ := mem_projRad_one.1 hr
  obtain ⟨b', c', rfl⟩ := mem_projRad_one.1 hs
  have hne : ∀ {b c : k}, proj 3 k (unipU k 0 b c) ≠ 1 → b ≠ 0 ∨ c ≠ 0 := by
    intro b c h
    by_contra h'
    simp only [ne_eq, not_or, not_not] at h'
    exact h (proj_unipU_eq_one_iff.2 ⟨rfl, h'.1, h'.2⟩)
  obtain ⟨B, hB⟩ := exists_leviTwo_conj_base (hne hr1)
  obtain ⟨B', hB'⟩ := exists_leviTwo_conj_base (hne hs1)
  refine ⟨B' * B⁻¹, ?_⟩
  rw [← hB, ← hB']
  simp only [map_mul, map_inv]
  group

theorem normalizer_projRad_one [Finite k] (hk : Nat.card k = 4) :
    normalizer (projRad k 1 : Set (projectiveSL 3 k)) =
      projRad k 1 ⊔ ((proj 3 k).comp (leviTwo k)).range := by
  refine le_antisymm (fun x hx => ?_) (sup_le le_normalizer ?_)
  · obtain ⟨g, rfl⟩ := proj_surjective 3 k x
    obtain ⟨h20, h21⟩ := row_two_of_mem_normalizer (three_ne_zero_of_card hk) hx
    have hdet := g.2
    rw [Matrix.det_fin_three, h20, h21] at hdet
    have hα : (g : Matrix (Fin 3) (Fin 3) k) 2 2 ≠ 0 := by
      intro h
      rw [h] at hdet
      simp at hdet
    obtain ⟨g', hg', hentry⟩ := exists_proj_eq_scalar_mul hk hα
    obtain ⟨b, c, B, hB⟩ := eq_unipU_mul_leviTwo (g := g')
      (by rw [hentry, inv_mul_cancel₀ hα]) (by rw [hentry, h20, mul_zero])
      (by rw [hentry, h21, mul_zero])
    rw [← hg', hB, map_mul]
    exact mul_mem_sup (mem_projRad_one.2 ⟨b, c, rfl⟩) ⟨B, rfl⟩
  · rintro _ ⟨B, rfl⟩
    exact leviTwo_mem_normalizer B

variable (k) in
@[expose] def leviProj (i : Fin 2) : SL2 k →* projectiveSL 3 k :=
  (proj 3 k).comp (levi k i)

theorem normalizer_projRad [Finite k] (hk : Nat.card k = 4) (i : Fin 2) :
    normalizer (projRad k i : Set (projectiveSL 3 k)) = projRad k i ⊔ (leviProj k i).range := by
  fin_cases i
  · exact normalizer_projRad_zero hk
  · exact normalizer_projRad_one hk

theorem projRad_inf_range (i : Fin 2) : projRad k i ⊓ (leviProj k i).range = ⊥ := by
  fin_cases i
  · exact projRad_zero_inf_range
  · exact projRad_one_inf_range

theorem leviProj_injective (i : Fin 2) : Function.Injective (leviProj k i) := by
  fin_cases i
  · exact leviOne_proj_injective
  · exact leviTwo_proj_injective

theorem projRad_transitive (i : Fin 2) {r : projectiveSL 3 k} (hr : r ∈ projRad k i)
    {s : projectiveSL 3 k} (hs : s ∈ projRad k i) (hr1 : r ≠ 1) (hs1 : s ≠ 1) :
    ∃ g : projectiveSL 3 k, g * r * g⁻¹ = s := by
  fin_cases i
  · obtain ⟨B, hB⟩ := projRad_zero_transitive hr hs hr1 hs1
    exact ⟨_, hB⟩
  · obtain ⟨B, hB⟩ := projRad_one_transitive hr hs hr1 hs1
    exact ⟨_, hB⟩

theorem exists_independent_projRad [Finite k] (hk : Nat.card k = 4) (i : Fin 2) :
    ∃ r₁ ∈ projRad k i, ∃ r₂ ∈ projRad k i, ∃ r₃ ∈ projRad k i, r₁ ≠ 1 ∧ r₂ ≠ 1 ∧ r₃ ≠ 1 ∧
      r₁ * r₂ ≠ 1 ∧ r₁ * r₃ ≠ 1 ∧ r₂ * r₃ ≠ 1 ∧ r₁ * (r₂ * r₃) ≠ 1 := by
  obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one_of_card hk
  have h1t : (1 : k) + t ≠ 0 := fun h => ht1 (by
    rw [show t = -1 by linear_combination h, neg_eq_self_of_card hk])
  fin_cases i
  · refine ⟨_, mem_projRad_zero.2 ⟨1, 0, rfl⟩, _, mem_projRad_zero.2 ⟨t, 0, rfl⟩, _,
      mem_projRad_zero.2 ⟨0, 1, rfl⟩, ?_⟩
    simp only [← map_mul, unipU_mul]
    refine ⟨proj_unipU_ne_one (by simp), proj_unipU_ne_one (by simp [ht0]),
      proj_unipU_ne_one (by simp), proj_unipU_ne_one (by simp [h1t]),
      proj_unipU_ne_one (by simp), proj_unipU_ne_one (by simp),
      proj_unipU_ne_one (by simp)⟩
  · refine ⟨_, mem_projRad_one.2 ⟨1, 0, rfl⟩, _, mem_projRad_one.2 ⟨t, 0, rfl⟩, _,
      mem_projRad_one.2 ⟨0, 1, rfl⟩, ?_⟩
    simp only [← map_mul, unipU_mul]
    refine ⟨proj_unipU_ne_one (by simp), proj_unipU_ne_one (by simp [ht0]),
      proj_unipU_ne_one (by simp), proj_unipU_ne_one (by simp [h1t]),
      proj_unipU_ne_one (by simp), proj_unipU_ne_one (by simp),
      proj_unipU_ne_one (by simp)⟩

theorem leviOne_uSL (a : k) : leviOne k (uSL a) = unipU k 0 a 0 := by
  ext i j
  rw [coe_leviOne, coe_unipU, coe_uSL]
  fin_cases i <;> fin_cases j <;> simp

theorem leviTwo_uSL (a : k) : leviTwo k (uSL a) = unipU k a 0 0 := by
  ext i j
  rw [coe_leviTwo, coe_unipU, coe_uSL]
  fin_cases i <;> fin_cases j <;> simp

theorem exists_map_sl2Unip_le (i : Fin 2) :
    ∃ j : Fin 2, (sl2Unip k).map (leviProj k i) ≤ projRad k j := by
  fin_cases i
  · refine ⟨1, ?_⟩
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact mem_projRad_one.2 ⟨a, 0, by rw [← leviOne_uSL]; rfl⟩
  · refine ⟨0, ?_⟩
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact mem_projRad_zero.2 ⟨a, 0, by rw [← leviTwo_uSL]; rfl⟩

theorem card_sl2Unip [Finite k] : Nat.card (sl2Unip k) = Nat.card k := by
  have hinj : Function.Injective (uSL : k → SL2 k) := fun a b h => by
    have := congrArg (fun B : SL2 k => (B : Matrix (Fin 2) (Fin 2) k) 0 1) h
    simpa [coe_uSL] using this
  let f : k → sl2Unip k := fun a => ⟨uSL a, a, rfl⟩
  have hf : Function.Bijective f :=
    ⟨fun a b h => hinj (congrArg Subtype.val h), fun ⟨_, a, rfl⟩ => ⟨a, rfl⟩⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem projRad_le_projUnip (i : Fin 2) : projRad k i ≤ projUnip k := by
  fin_cases i
  · intro x hx
    obtain ⟨a, c, rfl⟩ := mem_projRad_zero.1 hx
    exact mem_projUnip.2 ⟨a, 0, c, rfl⟩
  · intro x hx
    obtain ⟨b, c, rfl⟩ := mem_projRad_one.1 hx
    exact mem_projUnip.2 ⟨0, b, c, rfl⟩

theorem exists_mul_eq_of_mem_projUnip {x : projectiveSL 3 k} (hx : x ∈ projUnip k) :
    ∃ r₁ ∈ projRad k 0, ∃ r₂ ∈ projRad k 1, r₁ * r₂ = x := by
  obtain ⟨a, b, c, rfl⟩ := mem_projUnip.1 hx
  refine ⟨_, mem_projRad_zero.2 ⟨a, c - a * b, rfl⟩, _, mem_projRad_one.2 ⟨b, 0, rfl⟩, ?_⟩
  rw [← map_mul, unipU_mul]
  congr 2 <;> ring

theorem projRad_inf_eq : projRad k 0 ⊓ projRad k 1 = projCenterW k := by
  ext x
  rw [Subgroup.mem_inf, mem_projRad_zero, mem_projRad_one, mem_projCenterW]
  constructor
  · rintro ⟨⟨a, c, rfl⟩, ⟨b, c', h⟩⟩
    obtain ⟨h1, -, -⟩ := unipU_eq_of_proj_eq h
    exact ⟨c, by rw [← h1]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨⟨0, c, rfl⟩, ⟨0, c, rfl⟩⟩

theorem mem_projCenterW_of_commute {x : projectiveSL 3 k} (hx : x ∈ projUnip k)
    (h1 : x * proj 3 k (unipU k 1 0 0) = proj 3 k (unipU k 1 0 0) * x)
    (h2 : x * proj 3 k (unipU k 0 1 0) = proj 3 k (unipU k 0 1 0) * x) : x ∈ projCenterW k := by
  obtain ⟨a, b, c, rfl⟩ := mem_projUnip.1 hx
  rw [← map_mul, ← map_mul, unipU_mul, unipU_mul] at h1 h2
  obtain ⟨-, -, hb⟩ := unipU_eq_of_proj_eq h1
  obtain ⟨-, -, ha⟩ := unipU_eq_of_proj_eq h2
  have ha0 : a = 0 := by linear_combination ha
  have hb0 : b = 0 := by linear_combination -hb
  exact mem_projCenterW.2 ⟨c, by rw [ha0, hb0]⟩

theorem projCenterW_le_projRad (i : Fin 2) : projCenterW k ≤ projRad k i := by
  rw [← projRad_inf_eq]
  fin_cases i
  · exact inf_le_left
  · exact inf_le_right

theorem card_projCenterW [Finite k] : Nat.card (projCenterW k) = Nat.card k := by
  let f : k → projCenterW k := fun c => ⟨proj 3 k (unipU k 0 0 c), mem_projCenterW.2 ⟨c, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun c c' h => (unipU_eq_of_proj_eq (congrArg Subtype.val h)).2.2, fun x => ?_⟩
    obtain ⟨c, h⟩ := mem_projCenterW.1 x.2
    exact ⟨c, Subtype.ext h⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem card_projUnip [Finite k] :
    Nat.card (projUnip k) = Nat.card k * Nat.card k * Nat.card k := by
  let f : k × k × k → projUnip k := fun p =>
    ⟨proj 3 k (unipU k p.1 p.2.1 p.2.2), mem_projUnip.2 ⟨_, _, _, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q h => ?_, fun x => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := unipU_eq_of_proj_eq (congrArg Subtype.val h)
      exact Prod.ext h1 (Prod.ext h2 h3)
    · obtain ⟨a, b, c, h⟩ := mem_projUnip.1 x.2
      exact ⟨(a, b, c), Subtype.ext h⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Nat.card_prod, mul_assoc]

theorem unipAll_eq_unitriangular : unipAll k = unitriangular 3 k := by
  ext A
  rw [mem_unitriangular]
  constructor
  · rintro ⟨a, b, c, rfl⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [coe_unipU] at hij ⊢
    · fin_cases i <;> simp [coe_unipU]
  · rintro ⟨hlow, hdiag⟩
    refine ⟨(A : Matrix (Fin 3) (Fin 3) k) 0 1, (A : Matrix (Fin 3) (Fin 3) k) 1 2,
      (A : Matrix (Fin 3) (Fin 3) k) 0 2, ?_⟩
    ext i j
    rw [coe_unipU]
    fin_cases i <;> fin_cases j <;> simp [hdiag, hlow]

theorem projUnip_eq_projUnitriangular : projUnip k = projUnitriangular 3 k := by
  rw [projUnip, unipAll_eq_unitriangular]
  rfl

end CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
