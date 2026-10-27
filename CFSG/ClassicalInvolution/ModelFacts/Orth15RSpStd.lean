module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4Red
public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4NSAlg

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSp

open QuadraticAlgebra CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.Sp
open CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4 (QE r0 coe_r0 exists_conj_r0 sl2_sq_cases
  mem_sup_of_comm isQuasisimple_sl2 sup_le_normalizer_of_comm)
open scoped Matrix MatrixGroups

variable (F : Type) [Field F]

@[expose] noncomputable def R0 : Subgroup (StatedSp 2 F) := (longBlock F 2 0).range

@[expose] noncomputable def R0' : Subgroup (StatedSp 2 F) := (longBlock F 2 1).range

@[expose] noncomputable def x0 : StatedSp 2 F := longInv F 2 0

@[expose] noncomputable def blk (A B : SL(2, F)) : StatedSp 2 F :=
  longBlock F 2 0 A * longBlock F 2 1 B

@[expose] noncomputable def u0 : StatedSp 2 F := blk F r0 r0

@[expose] noncomputable def zneg : StatedSp 2 F :=
  ofSymplecticMat (-1) (by simp)

@[expose] noncomputable def t0 : StatedSp 2 F := x0 F * u0 F

variable {F}

theorem mat_blk (A B : SL(2, F)) : mat 2 F (blk F A B) =
    Matrix.fromBlocks (Matrix.diagonal ![A 0 0, B 0 0]) (Matrix.diagonal ![A 0 1, B 0 1])
      (Matrix.diagonal ![A 1 0, B 1 0]) (Matrix.diagonal ![A 1 1, B 1 1]) := by
  rw [blk, map_mul, mat_longBlock, mat_longBlock]
  ext a b
  rcases a with k | k <;> rcases b with l | l <;> fin_cases k <;> fin_cases l <;>
    simp [blockMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.fromBlocks, Matrix.one_apply]

theorem mat_zneg : mat 2 F (zneg F) = -1 := rfl

theorem mat_u0 : mat 2 F (u0 F) = gram F 2 := by
  rw [u0, mat_blk]
  ext a b
  rcases a with k | k <;> rcases b with l | l <;> fin_cases k <;> fin_cases l <;>
    simp [gram, coe_r0, Matrix.fromBlocks, Matrix.one_apply, Matrix.diagonal_apply]


theorem mat_x0 : mat 2 F (x0 F) =
    Matrix.diagonal (fun a => if a ∈ coords (0 : Fin 2) then (-1 : F) else 1) := mat_longInv 0

theorem longBlock_comm (A B : SL(2, F)) :
    longBlock F 2 0 A * longBlock F 2 1 B = longBlock F 2 1 B * longBlock F 2 0 A :=
  (commute_longRootSp2 (show (0 : Fin 2) ≠ 1 by decide) (x := longBlock F 2 0 A)
    (y := longBlock F 2 1 B) ⟨A, rfl⟩ ⟨B, rfl⟩).eq

theorem R0_comm_R0' {a b : StatedSp 2 F} (ha : a ∈ R0 F) (hb : b ∈ R0' F) : a * b = b * a := by
  obtain ⟨A, rfl⟩ := ha
  obtain ⟨B, rfl⟩ := hb
  exact longBlock_comm A B

theorem blk_mul (A B C D : SL(2, F)) : blk F A B * blk F C D = blk F (A * C) (B * D) := by
  unfold blk
  calc longBlock F 2 0 A * longBlock F 2 1 B * (longBlock F 2 0 C * longBlock F 2 1 D)
      = longBlock F 2 0 A * (longBlock F 2 1 B * longBlock F 2 0 C) * longBlock F 2 1 D := by group
    _ = longBlock F 2 0 A * (longBlock F 2 0 C * longBlock F 2 1 B) * longBlock F 2 1 D := by
        rw [← longBlock_comm C B]
    _ = longBlock F 2 0 (A * C) * longBlock F 2 1 (B * D) := by
        rw [map_mul, map_mul]
        group

theorem blk_one : blk F (1 : SL(2, F)) 1 = 1 := by simp [blk]

theorem blk_inv (A B : SL(2, F)) : (blk F A B)⁻¹ = blk F A⁻¹ B⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [blk_mul, mul_inv_cancel, mul_inv_cancel, blk_one])

theorem blk_mem (A B : SL(2, F)) : blk F A B ∈ R0 F ⊔ R0' F :=
  Subgroup.mul_mem_sup ⟨A, rfl⟩ ⟨B, rfl⟩

theorem u0_mem : u0 F ∈ R0 F ⊔ R0' F := blk_mem _ _

theorem x0_mem_R0 : x0 F ∈ R0 F := ⟨-1, rfl⟩

theorem u0_eq_blk : u0 F = blk F r0 r0 := rfl

theorem zneg_mul_self : zneg F * zneg F = 1 := by
  apply mat_injective
  rw [map_mul, mat_zneg, map_one]
  simp

theorem x0_mul_self : x0 F * x0 F = 1 := by
  apply mat_injective
  rw [map_mul, mat_x0, map_one, Matrix.diagonal_mul_diagonal]
  ext a b
  by_cases hab : a = b
  · subst hab
    by_cases ha : a ∈ coords (0 : Fin 2) <;> simp [ha]
  · simp [Matrix.one_apply_ne hab, Matrix.diagonal_apply_ne _ hab]

theorem u0_mul_self : u0 F * u0 F = zneg F := by
  apply mat_injective
  rw [map_mul, mat_u0, mat_zneg, gram_mul_gram]

theorem zneg_mem_center : zneg F ∈ Subgroup.center (StatedSp 2 F) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply mat_injective
  rw [map_mul, map_mul, mat_zneg]
  simp

theorem neg_one_comm (A : SL(2, F)) : (-1 : SL(2, F)) * A = A * (-1) := by
  apply Subtype.ext
  simp

theorem x0_mul_u0 : x0 F * u0 F = u0 F * x0 F := by
  unfold x0 longInv u0 blk
  calc longBlock F 2 0 (-1) * (longBlock F 2 0 r0 * longBlock F 2 1 r0)
      = longBlock F 2 0 ((-1) * r0) * longBlock F 2 1 r0 := by rw [map_mul]; group
    _ = longBlock F 2 0 (r0 * (-1)) * longBlock F 2 1 r0 := by rw [neg_one_comm]
    _ = longBlock F 2 0 r0 * (longBlock F 2 0 (-1) * longBlock F 2 1 r0) := by rw [map_mul]; group
    _ = longBlock F 2 0 r0 * (longBlock F 2 1 r0 * longBlock F 2 0 (-1)) := by
        rw [longBlock_comm]
    _ = longBlock F 2 0 r0 * longBlock F 2 1 r0 * longBlock F 2 0 (-1) := by group


theorem zneg_eq_blk : zneg F = blk F (-1) (-1) := by
  apply mat_injective
  rw [mat_zneg, mat_blk]
  ext a b
  rcases a with k | k <;> rcases b with l | l <;> fin_cases k <;> fin_cases l <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, Matrix.diagonal_apply]

theorem x0_eq_blk : x0 F = blk F (-1) 1 := by
  unfold x0 longInv blk
  simp

theorem zneg_mul_x0 : zneg F * x0 F = blk F 1 (-1) := by
  rw [zneg_eq_blk, x0_eq_blk, blk_mul]
  simp

theorem exists_scalar_of_mem_center {g : StatedSp 2 F} (hg : g ∈ Subgroup.center (StatedSp 2 F)) :
    ∃ r : F, mat 2 F g = r • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
  rw [CFSG.LieType.Universal.Symplectic.center_eq 2 F, Subgroup.mem_subgroupOf, StatedScalars,
    MonoidHom.mem_range] at hg
  obtain ⟨r, hr⟩ := hg
  refine ⟨r, ?_⟩
  rw [mat_apply, ← hr, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal]

theorem conj_cases (a g s : StatedSp 2 F) (ha : a * a = s) (hs : s = 1 ∨ s = zneg F)
    (hg : g * a * g⁻¹ * a⁻¹ ∈ Subgroup.center (StatedSp 2 F)) :
    g * a * g⁻¹ = a ∨ g * a * g⁻¹ = zneg F * a := by
  obtain ⟨r, hr⟩ := exists_scalar_of_mem_center hg
  have hy : mat 2 F (g * a * g⁻¹) = r • mat 2 F a := by
    have h1 : g * a * g⁻¹ = (g * a * g⁻¹ * a⁻¹) * a := by group
    rw [h1, map_mul, hr, Matrix.smul_mul, Matrix.one_mul]
  have hzc : g * s * g⁻¹ = s := by
    have hsc : s ∈ Subgroup.center (StatedSp 2 F) := by
      rcases hs with rfl | rfl
      · exact Subgroup.one_mem _
      · exact zneg_mem_center
    rw [Subgroup.mem_center_iff.mp hsc g]
    group
  have hyy : (g * a * g⁻¹) * (g * a * g⁻¹) = s := by
    calc (g * a * g⁻¹) * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = s := by rw [ha, hzc]
  have hms : (r * r) • mat 2 F s = mat 2 F s := by
    have h1 := congrArg (mat 2 F) hyy
    rw [map_mul, hy, Matrix.smul_mul, Matrix.mul_smul, ← map_mul, ha, smul_smul] at h1
    exact h1
  have hr2 : r * r = 1 := by
    rcases hs with rfl | rfl
    · have := congrFun (congrFun hms (Sum.inl 0)) (Sum.inl 0)
      simpa using this
    · have := congrFun (congrFun hms (Sum.inl 0)) (Sum.inl 0)
      rw [mat_zneg] at this
      simpa using this
  rcases mul_self_eq_one_iff.mp hr2 with hr1 | hr1
  · left
    apply mat_injective
    rw [hy, hr1, one_smul]
  · right
    apply mat_injective
    rw [hy, hr1, neg_one_smul, map_mul, mat_zneg, neg_one_mul]


theorem zneg_mul_x0_eq_longInv : zneg F * x0 F = longInv F 2 1 := by
  rw [zneg_mul_x0]
  unfold blk longInv
  simp

theorem R0_eq (h2 : (2 : F) ≠ 0) : R0 F = longRootGroup (x0 F) :=
  range_longBlock_eq_longRootGroup h2 0

theorem R0'_eq (h2 : (2 : F) ≠ 0) : R0' F = longRootGroup (zneg F * x0 F) := by
  rw [zneg_mul_x0_eq_longInv]
  exact range_longBlock_eq_longRootGroup h2 1

theorem zneg_conj (g : StatedSp 2 F) : g * zneg F * g⁻¹ = zneg F := by
  rw [Subgroup.mem_center_iff.mp zneg_mem_center g]
  group

theorem map_conj_fix (h2 : (2 : F) ≠ 0) {g : StatedSp 2 F} (hg : g * x0 F * g⁻¹ = x0 F) :
    (R0 F).map (MulAut.conj g).toMonoidHom = R0 F ∧
      (R0' F).map (MulAut.conj g).toMonoidHom = R0' F := by
  refine ⟨?_, ?_⟩
  · rw [R0_eq h2, ← longRootGroup_conj, hg]
  · have : g * (zneg F * x0 F) * g⁻¹ = zneg F * x0 F := by
      calc g * (zneg F * x0 F) * g⁻¹ = (g * zneg F * g⁻¹) * (g * x0 F * g⁻¹) := by group
        _ = zneg F * x0 F := by rw [zneg_conj, hg]
    rw [R0'_eq h2, ← longRootGroup_conj, this]

theorem map_conj_swap (h2 : (2 : F) ≠ 0) {g : StatedSp 2 F} (hg : g * x0 F * g⁻¹ = zneg F * x0 F) :
    (R0 F).map (MulAut.conj g).toMonoidHom = R0' F ∧
      (R0' F).map (MulAut.conj g).toMonoidHom = R0 F := by
  refine ⟨?_, ?_⟩
  · rw [R0_eq h2, ← longRootGroup_conj, hg, R0'_eq h2]
  · have : g * (zneg F * x0 F) * g⁻¹ = x0 F := by
      calc g * (zneg F * x0 F) * g⁻¹ = (g * zneg F * g⁻¹) * (g * x0 F * g⁻¹) := by group
        _ = zneg F * (zneg F * x0 F) := by rw [zneg_conj, hg]
        _ = x0 F := by rw [← mul_assoc, zneg_mul_self, one_mul]
    rw [R0'_eq h2, ← longRootGroup_conj, this, R0_eq h2]

theorem slayer_x0 (h2 : (2 : F) ≠ 0) [Finite F] (h4 : 4 ≤ Nat.card F) :
    SLayer (x0 F) (R0 F ⊔ R0' F) := by
  have hq : CFSG.IsQuasisimple SL(2, F) := isQuasisimple_sl2 h4
  have : Group.IsPerfect SL(2, F) := hq.1
  have hperf0 : Group.IsPerfect (R0 F) := Group.IsPerfect.range (longBlock F 2 0)
  have hperf2 : Group.IsPerfect (R0' F) := Group.IsPerfect.range (longBlock F 2 1)
  have hq0 : CFSG.IsQuasisimple ↥(R0 F) :=
    isQuasisimple_of_equiv (MonoidHom.ofInjective (longBlock_injective 0)) hq
  have hq2 : CFSG.IsQuasisimple ↥(R0' F) :=
    isQuasisimple_of_equiv (MonoidHom.ofInjective (longBlock_injective 1)) hq
  have hn0 := sup_le_normalizer_of_comm (A := R0 F) (B := R0' F) fun a ha b hb =>
    R0_comm_R0' ha hb
  have hn2 := sup_le_normalizer_of_comm (A := R0' F) (B := R0 F) fun a ha b hb =>
    (R0_comm_R0' hb ha).symm
  rw [sup_comm] at hn2
  have hx0c : ∀ A : SL(2, F), longBlock F 2 0 A * x0 F = x0 F * longBlock F 2 0 A := fun A => by
    unfold x0 longInv
    rw [← map_mul, ← map_mul, mul_neg_one, neg_one_mul]
  have hx0c' : ∀ B : SL(2, F), longBlock F 2 1 B * x0 F = x0 F * longBlock F 2 1 B := fun B => by
    unfold x0 longInv
    exact (longBlock_comm (-1) B).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    have : R0 F ⊔ R0' F ≤ Subgroup.centralizer ({x0 F} : Set (StatedSp 2 F)) := by
      refine sup_le ?_ ?_
      · rintro _ ⟨A, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hx0c A
      · rintro _ ⟨B, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hx0c' B
    exact Subgroup.mem_centralizer_singleton_iff.mp (this hp)
  · intro g hg p hp
    have hmem : g * p * g⁻¹ ∈ (R0 F ⊔ R0' F).map (MulAut.conj g).toMonoidHom := ⟨p, hp, rfl⟩
    rw [Subgroup.map_sup] at hmem
    rcases conj_cases (x0 F) g 1 x0_mul_self (Or.inl rfl) (by simpa [x0_mul_self] using hg) with
      h | h
    · obtain ⟨e1, e2⟩ := map_conj_fix h2 h
      rwa [e1, e2] at hmem
    · obtain ⟨e1, e2⟩ := map_conj_swap h2 h
      rwa [e1, e2, sup_comm] at hmem
  · refine sup_le ?_ ?_
    · exact (Subgroup.commutator_eq_self (H := R0 F)).symm.le.trans
        (Subgroup.commutator_mono le_sup_left le_sup_left)
    · exact (Subgroup.commutator_eq_self (H := R0' F)).symm.le.trans
        (Subgroup.commutator_mono le_sup_right le_sup_right)
  · refine ⟨{R0 F, R0' F}, ?_, ?_⟩
    · intro H hH
      rcases hH with rfl | hH
      · exact ⟨le_sup_left, hq0, fun p hp h hh => (Subgroup.mem_normalizer_iff.mp (hn0 hp) h).mp hh⟩
      · rw [Set.mem_singleton_iff] at hH
        subst hH
        exact ⟨le_sup_right, hq2, fun p hp h hh =>
          (Subgroup.mem_normalizer_iff.mp (hn2 hp) h).mp hh⟩
    · exact sup_le (le_iSup₂_of_le (R0 F) (Set.mem_insert _ _) le_rfl)
        (le_iSup₂_of_le (R0' F) (Set.mem_insert_of_mem _ rfl) le_rfl)


theorem sl2_eq_one_of_coe {r : SL(2, F)} (h : (r : Matrix (Fin 2) (Fin 2) F) = 1) : r = 1 :=
  Subtype.ext h

theorem sl2_eq_neg_one_of_coe {r : SL(2, F)} (h : (r : Matrix (Fin 2) (Fin 2) F) = -1) :
    r = -1 := Subtype.ext (by simpa using h)

theorem classify_w [Finite F] (h2 : (2 : F) ≠ 0) {w : StatedSp 2 F} (hw : w ∈ R0 F ⊔ R0' F)
    (hw2 : w * w ∈ Subgroup.center (StatedSp 2 F)) :
    w = 1 ∨ w = x0 F ∨ w = zneg F * x0 F ∨ w = zneg F ∨
      ∃ h ∈ R0 F ⊔ R0' F, w = h * u0 F * h⁻¹ := by
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_comm (fun a ha b hb => R0_comm_R0' ha hb) hw
  obtain ⟨r, rfl⟩ := ha
  obtain ⟨r', rfl⟩ := hb
  have hwb : w = blk F r r' := hab.symm
  subst hwb
  rw [blk_mul] at hw2
  obtain ⟨μ, hμ⟩ := exists_scalar_of_mem_center hw2
  rw [mat_blk] at hμ
  have f00 := congrFun (congrFun hμ (Sum.inl 0)) (Sum.inl 0)
  have f01 := congrFun (congrFun hμ (Sum.inl 0)) (Sum.inr 0)
  have f10 := congrFun (congrFun hμ (Sum.inr 0)) (Sum.inl 0)
  have f11 := congrFun (congrFun hμ (Sum.inr 0)) (Sum.inr 0)
  have g00 := congrFun (congrFun hμ (Sum.inl 1)) (Sum.inl 1)
  have g01 := congrFun (congrFun hμ (Sum.inl 1)) (Sum.inr 1)
  have g10 := congrFun (congrFun hμ (Sum.inr 1)) (Sum.inl 1)
  have g11 := congrFun (congrFun hμ (Sum.inr 1)) (Sum.inr 1)
  simp [Matrix.fromBlocks, Matrix.one_apply] at f00 f01 f10 f11 g00 g01 g10 g11
  have hrr : (r : Matrix (Fin 2) (Fin 2) F) * r = μ • 1 := by
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using f00
    · simpa using f01
    · simpa using f10
    · simpa using f11
  have hrr' : (r' : Matrix (Fin 2) (Fin 2) F) * r' = μ • 1 := by
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using g00
    · simpa using g01
    · simpa using g10
    · simpa using g11
  rcases sl2_sq_cases h2 r hrr with ⟨hμ1, hr1 | hr1⟩ | ⟨hμ1, hr1⟩ <;>
    rcases sl2_sq_cases h2 r' hrr' with ⟨hμ1', hr1' | hr1'⟩ | ⟨hμ1', hr1'⟩
  · left
    rw [sl2_eq_one_of_coe hr1, sl2_eq_one_of_coe hr1', blk_one]
  · right; right; left
    rw [sl2_eq_one_of_coe hr1, sl2_eq_neg_one_of_coe hr1', zneg_mul_x0]
  · exfalso
    apply h2
    linear_combination hμ1' - hμ1
  · right; left
    rw [sl2_eq_neg_one_of_coe hr1, sl2_eq_one_of_coe hr1', x0_eq_blk]
  · right; right; right; left
    rw [sl2_eq_neg_one_of_coe hr1, sl2_eq_neg_one_of_coe hr1', zneg_eq_blk]
  · exfalso
    apply h2
    linear_combination hμ1' - hμ1
  · exfalso
    apply h2
    linear_combination hμ1 - hμ1'
  · exfalso
    apply h2
    linear_combination hμ1 - hμ1'
  · obtain ⟨h₁, hh₁⟩ := exists_conj_r0 h2 r hr1
    obtain ⟨h₂, hh₂⟩ := exists_conj_r0 h2 r' hr1'
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨blk F h₁ h₂, blk_mem _ _, ?_⟩)))
    rw [u0_eq_blk, blk_inv, blk_mul, blk_mul, hh₁, hh₂]


theorem r0_inv : (r0⁻¹ : SL(2, F)) = -r0 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_neg, coe_r0,
    Matrix.adjugate_fin_two_of]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem r0_mul_self : r0 * r0 = (-1 : SL(2, F)) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_r0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem t0_eq_blk : t0 F = blk F (-r0) r0 := by
  rw [t0, x0_eq_blk, u0_eq_blk, blk_mul, neg_one_mul]
  simp

theorem t0_eq_blk' : t0 F = blk F r0⁻¹ r0 := by
  rw [t0_eq_blk, r0_inv]

theorem t0_mem : t0 F ∈ R0 F ⊔ R0' F := by
  rw [t0_eq_blk]
  exact blk_mem _ _

theorem exists_conj_t0 [Finite F] (h2 : (2 : F) ≠ 0) :
    ∃ g' : StatedSp 2 F, g' * u0 F * g'⁻¹ = t0 F ∧ g' * x0 F * g'⁻¹ = x0 F := by
  have hr : (((r0⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) * ((r0⁻¹ : SL(2, F)) :
      Matrix (Fin 2) (Fin 2) F) = -1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, r0_inv, neg_mul_neg, r0_mul_self]
    simp
  obtain ⟨h, hh⟩ := exists_conj_r0 h2 r0⁻¹ hr
  refine ⟨blk F h 1, ?_, ?_⟩
  · have e : blk F h 1 * u0 F * (blk F h 1)⁻¹ = blk F (h * r0 * h⁻¹) (1 * r0 * 1⁻¹) := by
      rw [u0_eq_blk, blk_inv, blk_mul, blk_mul]
    rw [e, hh, t0_eq_blk']
    simp
  · have e : blk F h 1 * x0 F * (blk F h 1)⁻¹ = blk F (h * (-1) * h⁻¹) (1 * 1 * 1⁻¹) := by
      rw [x0_eq_blk, blk_inv, blk_mul, blk_mul]
    have : h * (-1 : SL(2, F)) * h⁻¹ = -1 := by
      rw [← neg_one_comm h]
      simp
    rw [e, this, x0_eq_blk]
    simp

theorem u0_not_central : u0 F ∉ Subgroup.center (StatedSp 2 F) := by
  intro h
  obtain ⟨r, hr⟩ := exists_scalar_of_mem_center h
  have e := congrFun (congrFun hr (Sum.inl 0)) (Sum.inr 0)
  rw [mat_u0] at e
  simp [gram, Matrix.fromBlocks, Matrix.one_apply] at e

theorem t0_not_central : t0 F ∉ Subgroup.center (StatedSp 2 F) := by
  intro h
  obtain ⟨r, hr⟩ := exists_scalar_of_mem_center h
  have e := congrFun (congrFun hr (Sum.inl 0)) (Sum.inr 0)
  rw [t0_eq_blk, mat_blk] at e
  simp [coe_r0, Matrix.fromBlocks, Matrix.one_apply] at e

theorem x0_not_central (h2 : (2 : F) ≠ 0) : x0 F ∉ Subgroup.center (StatedSp 2 F) := by
  intro h
  obtain ⟨r, hr⟩ := exists_scalar_of_mem_center h
  have e0 := congrFun (congrFun hr (Sum.inl 0)) (Sum.inl 0)
  have e1 := congrFun (congrFun hr (Sum.inl 1)) (Sum.inl 1)
  rw [mat_x0] at e0 e1
  simp [coords, Matrix.diagonal_apply] at e0 e1
  apply h2
  linear_combination e1 - e0


end CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSp
