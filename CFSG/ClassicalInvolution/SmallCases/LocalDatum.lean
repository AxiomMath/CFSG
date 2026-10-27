module

public import CFSG.ClassicalInvolution.SmallCases.LocalDatumRank

public section

namespace CFSG.ClassicalInvolution

open Matrix CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open scoped MatrixGroups

section Matrices

variable {F : Type} [Field F]

@[expose] def dgA : SL(3, F) := blockSL F 3 2 0 (by omega) (-1)

@[expose] def dgB : SL(3, F) := blockSL F 3 2 1 (by omega) (-1)

theorem coe_dgA : ((dgA : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal ![-1, -1, 1] := by
  rw [dgA, coe_blockSL_three_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem coe_dgB : ((dgB : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal ![1, -1, -1] := by
  rw [dgB, coe_blockSL_three_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem dgA_mul_self : (dgA : SL(3, F)) * dgA = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_dgA, Matrix.diagonal_mul_diagonal,
    Matrix.SpecialLinearGroup.coe_one, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem dgB_mul_self : (dgB : SL(3, F)) * dgB = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_dgB, Matrix.diagonal_mul_diagonal,
    Matrix.SpecialLinearGroup.coe_one, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem dgA_inv : (dgA : SL(3, F))⁻¹ = dgA := inv_eq_of_mul_eq_one_right dgA_mul_self

theorem dgB_inv : (dgB : SL(3, F))⁻¹ = dgB := inv_eq_of_mul_eq_one_right dgB_mul_self

theorem dgA_mul_dgB : (dgA : SL(3, F)) * dgB = dgB * dgA := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_dgA, coe_dgB,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

theorem dgA_conj (x : SL(3, F)) : dgA * x * dgA⁻¹ = diagConj3 (-1) (-1) x := by
  apply Subtype.ext
  rw [dgA_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_dgA,
    coe_diagConj3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply]

theorem dgB_conj (x : SL(3, F)) : dgB * x * dgB⁻¹ = diagConj3 (-1) 1 x := by
  apply Subtype.ext
  rw [dgB_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_dgB,
    coe_diagConj3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply]

theorem diagConj3_mul (a b a' b' : Fˣ) (x : SL(3, F)) :
    diagConj3 a b (diagConj3 a' b' x) = diagConj3 (a * a') (b * b') x := by
  apply Subtype.ext
  rw [coe_diagConj3, coe_diagConj3, coe_diagConj3]
  have h1 : Matrix.diagonal ![(a : F), (b : F), 1] * Matrix.diagonal ![(a' : F), (b' : F), 1] =
      Matrix.diagonal ![((a * a' : Fˣ) : F), ((b * b' : Fˣ) : F), 1] := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp
  have h2 : Matrix.diagonal ![((a'⁻¹ : Fˣ) : F), ((b'⁻¹ : Fˣ) : F), 1] *
      Matrix.diagonal ![((a⁻¹ : Fˣ) : F), ((b⁻¹ : Fˣ) : F), 1] =
        Matrix.diagonal ![(((a * a')⁻¹ : Fˣ) : F), (((b * b')⁻¹ : Fˣ) : F), 1] := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [mul_comm]
  calc Matrix.diagonal ![(a : F), (b : F), 1] * (Matrix.diagonal ![(a' : F), (b' : F), 1] *
        (x : Matrix (Fin 3) (Fin 3) F) *
          Matrix.diagonal ![((a'⁻¹ : Fˣ) : F), ((b'⁻¹ : Fˣ) : F), 1]) *
        Matrix.diagonal ![((a⁻¹ : Fˣ) : F), ((b⁻¹ : Fˣ) : F), 1]
      = (Matrix.diagonal ![(a : F), (b : F), 1] * Matrix.diagonal ![(a' : F), (b' : F), 1]) *
        (x : Matrix (Fin 3) (Fin 3) F) *
          (Matrix.diagonal ![((a'⁻¹ : Fˣ) : F), ((b'⁻¹ : Fˣ) : F), 1] *
            Matrix.diagonal ![((a⁻¹ : Fˣ) : F), ((b⁻¹ : Fˣ) : F), 1]) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, h2]

theorem diagConj3_one (x : SL(3, F)) : diagConj3 1 1 x = x := by
  apply Subtype.ext
  rw [coe_diagConj3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply]

end Matrices

section Center

variable {F : Type} [Field F]

private theorem eq_one_of_sq_eq_zero {ω : F} {N : Matrix (Fin 3) (Fin 3) F} {k : Fin 3}
    (hN : N * N = 0) (hk : N k k = 0)
    (h : (ω • ((1 : Matrix (Fin 3) (Fin 3) F) + N) - 1) * (ω • (1 + N) - 1) = 0) : ω = 1 := by
  have h1 : (ω • ((1 : Matrix (Fin 3) (Fin 3) F) + N) - 1) =
      (ω - 1) • (1 : Matrix (Fin 3) (Fin 3) F) + ω • N := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [sub_smul]
      ring
    · simp [Matrix.one_apply_ne hab]
  rw [h1] at h
  have h2 : ((ω - 1) • (1 : Matrix (Fin 3) (Fin 3) F) + ω • N) *
      ((ω - 1) • (1 : Matrix (Fin 3) (Fin 3) F) + ω • N) =
        ((ω - 1) ^ 2) • (1 : Matrix (Fin 3) (Fin 3) F) + (2 * ω * (ω - 1)) • N := by
    have e : (ω • N) * (ω • N) = 0 := by rw [Matrix.smul_mul, Matrix.mul_smul, hN]; simp
    calc _ = ((ω - 1) • (1 : Matrix (Fin 3) (Fin 3) F)) * ((ω - 1) • 1) +
          ((ω - 1) • (1 : Matrix (Fin 3) (Fin 3) F)) * (ω • N) +
          (ω • N) * ((ω - 1) • (1 : Matrix (Fin 3) (Fin 3) F)) + (ω • N) * (ω • N) := by
          simp only [Matrix.add_mul, Matrix.mul_add]; abel
      _ = _ := by
          rw [e]
          simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
          rw [add_zero]
          module
  rw [h2] at h
  have h3 := congrFun (congrFun h k) k
  simp [hk] at h3
  have : ω - 1 = 0 := by simpa using h3
  linear_combination this

private theorem single_mul_self {i j : Fin 3} (hij : i ≠ j) (c : F) :
    Matrix.single i j c * Matrix.single i j c = 0 :=
  Matrix.single_mul_single_of_ne c i j i hij.symm c

theorem mem_center_of_forall_commutator_mem_center {x : SL(3, F)}
    (h : ∀ y : SL(3, F), x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center SL(3, F)) :
    x ∈ Subgroup.center SL(3, F) := by
  have hXX : (x : Matrix (Fin 3) (Fin 3) F) *
      ((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hXX' : ((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
      (x : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hcomm : ∀ tr : Matrix.TransvectionStruct (Fin 3) F,
      Commute tr.toMatrix (x : Matrix (Fin 3) (Fin 3) F) := by
    intro tr
    set y : SL(3, F) := ⟨tr.toMatrix, tr.det⟩ with hy
    obtain ⟨ω, -, hω⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (h y)
    set N : Matrix (Fin 3) (Fin 3) F := Matrix.single tr.i tr.j tr.c with hN
    have hY : tr.toMatrix = 1 + N := rfl
    have hNN : N * N = 0 := single_mul_self tr.hij tr.c
    have hNkk : N tr.i tr.i = 0 := by
      simp [hN, tr.hij.symm]
    have hz : x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
    have hXY : (x : Matrix (Fin 3) (Fin 3) F) * tr.toMatrix *
        ((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = ω • tr.toMatrix := by
      have hω' : Matrix.scalar (Fin 3) ω = (x : Matrix (Fin 3) (Fin 3) F) * (y : Matrix _ _ F) *
          ((x⁻¹ : SL(3, F)) : Matrix _ _ F) * ((y⁻¹ : SL(3, F)) : Matrix _ _ F) := by
        simpa only [Matrix.SpecialLinearGroup.coe_mul] using hω
      have := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F)) hz
      simp only [Matrix.SpecialLinearGroup.coe_mul] at this
      rw [← hω'] at this
      rw [show (x : Matrix (Fin 3) (Fin 3) F) * tr.toMatrix * ((x⁻¹ : SL(3, F)) : Matrix _ _ F) =
        (x : Matrix _ _ F) * (y : Matrix _ _ F) * ((x⁻¹ : SL(3, F)) : Matrix _ _ F) from rfl,
        this, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
    have hXN : (x : Matrix (Fin 3) (Fin 3) F) * N *
        ((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = ω • (1 + N) - 1 := by
      have e : N = tr.toMatrix - 1 := by rw [hY]; abel
      have e2 : (x : Matrix (Fin 3) (Fin 3) F) * N *
          ((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
            (x : Matrix (Fin 3) (Fin 3) F) * tr.toMatrix *
              ((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) - 1 := by
        rw [e, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hXX]
      rw [e2, hXY, ← hY]
    have hsq : (ω • ((1 : Matrix (Fin 3) (Fin 3) F) + N) - 1) * (ω • (1 + N) - 1) = 0 := by
      rw [← hXN]
      calc _ = (x : Matrix (Fin 3) (Fin 3) F) * N *
            (((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * (x : Matrix (Fin 3) (Fin 3) F)) * N *
              ((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by simp only [Matrix.mul_assoc]
        _ = 0 := by
          rw [hXX', Matrix.mul_one, Matrix.mul_assoc (x : Matrix (Fin 3) (Fin 3) F) N N, hNN,
            Matrix.mul_zero, Matrix.zero_mul]
    have hω1 : ω = 1 := eq_one_of_sq_eq_zero hNN hNkk hsq
    rw [hω1, one_smul] at hXY
    have h2 := congrArg (· * (x : Matrix (Fin 3) (Fin 3) F)) hXY
    simp only [Matrix.mul_assoc, hXX', Matrix.mul_one] at h2
    exact h2.symm
  obtain ⟨r, hr⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct hcomm
  refine Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨r, ?_, hr⟩
  have := x.2
  rw [← hr, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at this
  exact this

end Center

section Centralizer

variable {F : Type} [Field F] {G : Type} [Group G]

theorem eq_one_of_mem_range_of_centralizes {θ : SL(3, F) →* G}
    (hker : θ.ker ≤ Subgroup.center SL(3, F)) {m : G} (hm : m ∈ θ.range)
    (hc : ∀ x, m * θ x = θ x * m) {k : ℕ} (hk : orderOf m = 2 ^ k) : m = 1 := by
  obtain ⟨x, rfl⟩ := hm
  have hx : x ∈ Subgroup.center SL(3, F) := by
    refine mem_center_of_forall_commutator_mem_center fun y => hker ?_
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    have h := hc y
    calc θ x * θ y * (θ x)⁻¹ * (θ y)⁻¹ = (θ x * θ y) * (θ x)⁻¹ * (θ y)⁻¹ := rfl
      _ = (θ y * θ x) * (θ x)⁻¹ * (θ y)⁻¹ := by rw [h]
      _ = 1 := by group
  obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hr, ← map_pow]
    have : r ^ 3 = 1 := by simpa using hr3
    rw [this, map_one]
    rfl
  have h3 : (θ x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hdvd : 2 ^ k ∣ 3 := hk ▸ orderOf_dvd_of_pow_eq_one h3
  have hk0 : 2 ^ k = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)) hdvd
  rw [hk0, orderOf_eq_one_iff] at hk
  exact hk

end Centralizer

section Action

variable {F : Type} [Field F] {G : Type} [Group G]

@[expose] def SignAct (θ : SL(3, F) →* G) (e : G) : Prop :=
  ∃ a b : Fˣ, (a = 1 ∨ a = -1) ∧ (b = 1 ∨ b = -1) ∧
    ∀ x : SL(3, F), e * θ x * e⁻¹ = θ (diagConj3 a b x)

namespace SignAct

variable {θ : SL(3, F) →* G}

theorem one : SignAct θ (1 : G) :=
  ⟨1, 1, Or.inl rfl, Or.inl rfl, fun x => by simp [diagConj3_one]⟩

theorem of_commute {t : G} (h : ∀ x, t * θ x = θ x * t) : SignAct θ t :=
  ⟨1, 1, Or.inl rfl, Or.inl rfl, fun x => by
    rw [diagConj3_one, h x]
    group⟩

theorem mul {e e' : G} (h : SignAct θ e) (h' : SignAct θ e') : SignAct θ (e * e') := by
  obtain ⟨a, b, ha, hb, h⟩ := h
  obtain ⟨a', b', ha', hb', h'⟩ := h'
  refine ⟨a * a', b * b', ?_, ?_, fun x => ?_⟩
  · rcases ha with rfl | rfl <;> rcases ha' with rfl | rfl <;> simp
  · rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl <;> simp
  · calc e * e' * θ x * (e * e')⁻¹ = e * (e' * θ x * e'⁻¹) * e⁻¹ := by group
      _ = e * θ (diagConj3 a' b' x) * e⁻¹ := by rw [h' x]
      _ = θ (diagConj3 a b (diagConj3 a' b' x)) := h _
      _ = θ (diagConj3 (a * a') (b * b') x) := by rw [diagConj3_mul]

theorem inv {e : G} (h : SignAct θ e) : SignAct θ e⁻¹ := by
  obtain ⟨a, b, ha, hb, h⟩ := h
  refine ⟨a⁻¹, b⁻¹, ?_, ?_, fun x => ?_⟩
  · rcases ha with rfl | rfl <;> simp
  · rcases hb with rfl | rfl <;> simp
  · have h1 := h (diagConj3 a⁻¹ b⁻¹ x)
    rw [diagConj3_mul, mul_inv_cancel, mul_inv_cancel, diagConj3_one] at h1
    rw [inv_inv]
    calc e⁻¹ * θ x * e = e⁻¹ * (e * θ (diagConj3 a⁻¹ b⁻¹ x) * e⁻¹) * e := by rw [h1]
      _ = θ (diagConj3 a⁻¹ b⁻¹ x) := by group

end SignAct

end Action

section FrameGroup

variable {F : Type} [Field F] {G : Type} [Group G]

@[expose] def frameGroup (θ : SL(3, F) →* G) (t : G) : Subgroup G :=
  Subgroup.closure {θ dgA, θ dgB, t}

section Basic

variable {θ : SL(3, F) →* G} {t : G}

theorem z₁_mem_frameGroup : θ dgA ∈ frameGroup θ t :=
  Subgroup.subset_closure (by simp)

theorem z₂_mem_frameGroup : θ dgB ∈ frameGroup θ t :=
  Subgroup.subset_closure (by simp)

theorem t_mem_frameGroup : t ∈ frameGroup θ t :=
  Subgroup.subset_closure (by simp)

theorem signAct_z₁ : SignAct θ (θ dgA) :=
  ⟨-1, -1, Or.inr rfl, Or.inr rfl, fun x => by
    rw [← map_inv, ← map_mul, ← map_mul, dgA_conj]⟩

theorem signAct_z₂ : SignAct θ (θ dgB) :=
  ⟨-1, 1, Or.inr rfl, Or.inl rfl, fun x => by
    rw [← map_inv, ← map_mul, ← map_mul, dgB_conj]⟩

theorem signAct_of_mem_frameGroup (ht : ∀ x, t * θ x = θ x * t) {e : G}
    (he : e ∈ frameGroup θ t) : SignAct θ e := by
  induction he using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with rfl | rfl | rfl
    · exact signAct_z₁
    · exact signAct_z₂
    · exact SignAct.of_commute ht
  | one => exact SignAct.one
  | mul x y _ _ hx hy => exact hx.mul hy
  | inv x _ hx => exact hx.inv

theorem frameGroup_comm (ht : ∀ x, t * θ x = θ x * t) {x y : G} (hx : x ∈ frameGroup θ t)
    (hy : y ∈ frameGroup θ t) : x * y = y * x := by
  have hcomm : ({θ dgA, θ dgB, t} : Set G).Pairwise Commute := by
    have h12 : θ dgA * θ dgB = θ dgB * θ dgA := by rw [← map_mul, ← map_mul, dgA_mul_dgB]
    have h13 : θ dgA * t = t * θ dgA := (ht _).symm
    have h23 : θ dgB * t = t * θ dgB := (ht _).symm
    intro a ha b hb _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact absurd rfl ‹_›
    · exact h12
    · exact h13
    · exact h12.symm
    · exact absurd rfl ‹_›
    · exact h23
    · exact h13.symm
    · exact h23.symm
    · exact absurd rfl ‹_›
  have := Subgroup.isMulCommutative_closure hcomm
  exact setLike_mul_comm (s := Subgroup.closure ({θ dgA, θ dgB, t} : Set G)) hx hy

theorem frameGroup_sq (ht : ∀ x, t * θ x = θ x * t) (ht2 : t * t = 1) {x : G}
    (hx : x ∈ frameGroup θ t) : x * x = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with rfl | rfl | rfl
    · rw [← map_mul, dgA_mul_self, map_one]
    · rw [← map_mul, dgB_mul_self, map_one]
    · exact ht2
  | one => simp
  | mul x y hx hy hx1 hy1 =>
    have hc := frameGroup_comm ht hx hy
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hc]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx1, hy1, one_mul]
  | inv x _ hx => rw [← _root_.mul_inv_rev, hx, inv_one]

@[expose] def diagGL2 (a b : Fˣ) : GL (Fin 2) F :=
  ⟨Matrix.diagonal ![(a : F), (b : F)], Matrix.diagonal ![((a⁻¹ : Fˣ) : F), ((b⁻¹ : Fˣ) : F)],
    diag2_mul_diag2 a b, by simpa using diag2_mul_diag2 a⁻¹ b⁻¹⟩

theorem diagConj2_eq_slConjugation (a b : Fˣ) (s : SL(2, F)) :
    diagConj2 a b s = slConjugation 2 F (diagGL2 a b) s := by
  apply Subtype.ext
  rw [slConjugation_matrix, coe_diagConj2]
  rfl

@[expose] def chart₁ (θ : SL(3, F) →* G) : SL(2, F) →* G :=
  θ.comp (blockSL F 3 2 0 (by omega))

@[expose] def chart₂ (θ : SL(3, F) →* G) : SL(2, F) →* G :=
  θ.comp (blockSL F 3 2 1 (by omega))

theorem range_chart₁ (θ : SL(3, F) →* G) : (chart₁ θ).range = (B12 F).map θ :=
  MonoidHom.range_comp _ _

theorem range_chart₂ (θ : SL(3, F) →* G) : (chart₂ θ).range = (B23 F).map θ :=
  MonoidHom.range_comp _ _

theorem act_chart₁ {e : G} {a b : Fˣ} (h : ∀ x, e * θ x * e⁻¹ = θ (diagConj3 a b x))
    (s : SL(2, F)) : e * chart₁ θ s * e⁻¹ = chart₁ θ (slConjugation 2 F (diagGL2 a b) s) := by
  simp only [chart₁, MonoidHom.comp_apply]
  rw [h, diagConj3_blockSL_zero, diagConj2_eq_slConjugation]

theorem act_chart₂ {e : G} {a b : Fˣ} (h : ∀ x, e * θ x * e⁻¹ = θ (diagConj3 a b x))
    (s : SL(2, F)) : e * chart₂ θ s * e⁻¹ = chart₂ θ (slConjugation 2 F (diagGL2 b 1) s) := by
  simp only [chart₂, MonoidHom.comp_apply]
  rw [h, diagConj3_blockSL_one, diagConj2_eq_slConjugation]

@[expose] def tr2 : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem diagConj2_tr2 (a b : Fˣ) :
    ((diagConj2 a b (tr2 : SL(2, F)) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1 =
      (a : F) * ((b⁻¹ : Fˣ) : F) := by
  rw [coe_diagConj2]
  simp [tr2, Matrix.mul_apply, Matrix.diagonal_apply]

theorem eq_of_diagConj2_tr2 {a b : Fˣ} (h : diagConj2 a b (tr2 : SL(2, F)) = tr2) : a = b := by
  have h1 : ((diagConj2 a b (tr2 : SL(2, F)) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1 =
      ((tr2 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1 := by rw [h]
  rw [diagConj2_tr2] at h1
  have h2 : ((tr2 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1 = 1 := by simp [tr2]
  rw [h2, Units.val_inv_eq_inv_val] at h1
  exact Units.ext ((mul_inv_eq_one₀ b.ne_zero).mp h1)

theorem neg_eq_iff_not_eq {a b : Fˣ} (h : (-1 : Fˣ) ≠ 1) (ha : a = 1 ∨ a = -1)
    (hb : b = 1 ∨ b = -1) : -a = b ↔ ¬ a = b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [h, h.symm]

theorem z₁_conj (x : SL(3, F)) : θ dgA * θ x * (θ dgA)⁻¹ = θ (diagConj3 (-1) (-1) x) := by
  rw [← map_inv, ← map_mul, ← map_mul, dgA_conj]

theorem z₂_conj (x : SL(3, F)) : θ dgB * θ x * (θ dgB)⁻¹ = θ (diagConj3 (-1) 1 x) := by
  rw [← map_inv, ← map_mul, ← map_mul, dgB_conj]

theorem centralizes_chart₁_iff (hker : θ.ker ≤ Subgroup.center SL(3, F)) {e : G} {a b : Fˣ}
    (h : ∀ x, e * θ x * e⁻¹ = θ (diagConj3 a b x)) :
    (∀ k ∈ (chart₁ θ).range, k * e = e * k) ↔ a = b := by
  have hinj : Function.Injective (chart₁ θ) :=
    comp_blockSL_injective hker (by omega) (by omega)
  constructor
  · intro hc
    have h1 := hc (chart₁ θ tr2) ⟨tr2, rfl⟩
    have h2 : e * chart₁ θ tr2 * e⁻¹ = chart₁ θ tr2 := by rw [← h1]; group
    rw [act_chart₁ h] at h2
    have h3 := hinj h2
    rw [← diagConj2_eq_slConjugation] at h3
    exact eq_of_diagConj2_tr2 h3
  · rintro rfl k ⟨s, rfl⟩
    have h1 := act_chart₁ h s
    rw [← diagConj2_eq_slConjugation, diagConj2_self] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm

theorem centralizes_chart₂_iff (hker : θ.ker ≤ Subgroup.center SL(3, F)) {e : G} {a b : Fˣ}
    (h : ∀ x, e * θ x * e⁻¹ = θ (diagConj3 a b x)) :
    (∀ k ∈ (chart₂ θ).range, k * e = e * k) ↔ b = 1 := by
  have hinj : Function.Injective (chart₂ θ) :=
    comp_blockSL_injective hker (by omega) (by omega)
  constructor
  · intro hc
    have h1 := hc (chart₂ θ tr2) ⟨tr2, rfl⟩
    have h2 : e * chart₂ θ tr2 * e⁻¹ = chart₂ θ tr2 := by rw [← h1]; group
    rw [act_chart₂ h] at h2
    have h3 := hinj h2
    rw [← diagConj2_eq_slConjugation] at h3
    exact eq_of_diagConj2_tr2 h3
  · rintro rfl k ⟨s, rfl⟩
    have h1 := act_chart₂ h s
    rw [← diagConj2_eq_slConjugation, diagConj2_self] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm

theorem index_two_chart₁ (hker : θ.ker ≤ Subgroup.center SL(3, F))
    (ht : ∀ x, t * θ x = θ x * t) (hneg : (-1 : Fˣ) ≠ 1) :
    (axisSub (frameGroup θ t) (chart₁ θ).range).relIndex (frameGroup θ t) = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨θ dgB, z₂_mem_frameGroup, fun b hb => ?_⟩
  obtain ⟨a, c, ha, hc, hab⟩ := signAct_of_mem_frameGroup ht hb
  have hbz : b * θ dgB ∈ frameGroup θ t := (frameGroup θ t).mul_mem hb z₂_mem_frameGroup
  have hbz_act : ∀ x, (b * θ dgB) * θ x * (b * θ dgB)⁻¹ =
      θ (diagConj3 (a * -1) (c * 1) x) := fun x => by
    calc (b * θ dgB) * θ x * (b * θ dgB)⁻¹ = b * (θ dgB * θ x * (θ dgB)⁻¹) * b⁻¹ := by group
      _ = θ (diagConj3 (a * -1) (c * 1) x) := by rw [z₂_conj, hab, diagConj3_mul]
  rw [xor_iff_iff_not, mem_axisSub_iff, mem_axisSub_iff]
  simp only [hb, hbz, true_and]
  rw [centralizes_chart₁_iff hker hbz_act, centralizes_chart₁_iff hker hab]
  simpa using neg_eq_iff_not_eq hneg ha hc

theorem index_two_chart₂ (hker : θ.ker ≤ Subgroup.center SL(3, F))
    (ht : ∀ x, t * θ x = θ x * t) (hneg : (-1 : Fˣ) ≠ 1) :
    (axisSub (frameGroup θ t) (chart₂ θ).range).relIndex (frameGroup θ t) = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨θ dgA, z₁_mem_frameGroup, fun b hb => ?_⟩
  obtain ⟨a, c, ha, hc, hab⟩ := signAct_of_mem_frameGroup ht hb
  have hbz : b * θ dgA ∈ frameGroup θ t := (frameGroup θ t).mul_mem hb z₁_mem_frameGroup
  have hbz_act : ∀ x, (b * θ dgA) * θ x * (b * θ dgA)⁻¹ =
      θ (diagConj3 (a * -1) (c * -1) x) := fun x => by
    calc (b * θ dgA) * θ x * (b * θ dgA)⁻¹ = b * (θ dgA * θ x * (θ dgA)⁻¹) * b⁻¹ := by group
      _ = θ (diagConj3 (a * -1) (c * -1) x) := by rw [z₁_conj, hab, diagConj3_mul]
  rw [xor_iff_iff_not, mem_axisSub_iff, mem_axisSub_iff]
  simp only [hb, hbz, true_and]
  rw [centralizes_chart₂_iff hker hbz_act, centralizes_chart₂_iff hker hab]
  have := neg_eq_iff_not_eq hneg hc (Or.inl rfl : (1 : Fˣ) = 1 ∨ (1 : Fˣ) = -1)
  simpa using this

theorem diagData_chart₁ (hker : θ.ker ≤ Subgroup.center SL(3, F))
    (ht : ∀ x, t * θ x = θ x * t) (ht2 : t * t = 1) (hneg : (-1 : Fˣ) ≠ 1) :
    DiagData (chart₁ θ) (frameGroup θ t) where
  inj := comp_blockSL_injective hker (by omega) (by omega)
  comm := fun x hx y hy => frameGroup_comm ht hx hy
  sq := fun x hx => frameGroup_sq ht ht2 hx
  neg_mem := z₁_mem_frameGroup
  diag := fun e he => by
    obtain ⟨a, b, -, -, h⟩ := signAct_of_mem_frameGroup ht he
    exact ⟨diagGL2 a b, act_chart₁ h⟩
  index_two := index_two_chart₁ hker ht hneg

theorem diagData_chart₂ (hker : θ.ker ≤ Subgroup.center SL(3, F))
    (ht : ∀ x, t * θ x = θ x * t) (ht2 : t * t = 1) (hneg : (-1 : Fˣ) ≠ 1) :
    DiagData (chart₂ θ) (frameGroup θ t) where
  inj := comp_blockSL_injective hker (by omega) (by omega)
  comm := fun x hx y hy => frameGroup_comm ht hx hy
  sq := fun x hx => frameGroup_sq ht ht2 hx
  neg_mem := z₂_mem_frameGroup
  diag := fun e he => by
    obtain ⟨a, b, -, -, h⟩ := signAct_of_mem_frameGroup ht he
    exact ⟨diagGL2 b 1, act_chart₂ h⟩
  index_two := index_two_chart₂ hker ht hneg

theorem inSigma_frameGroup_left (hker : θ.ker ≤ Subgroup.center SL(3, F))
    (ht : ∀ x, t * θ x = θ x * t) (ht2 : t * t = 1) (hneg : (-1 : Fˣ) ≠ 1) :
    InSigma F (frameGroup θ t) ((B12 F).map θ) :=
  ⟨chart₁ θ, range_chart₁ θ, diagData_chart₁ hker ht ht2 hneg⟩

theorem inSigma_frameGroup_right (hker : θ.ker ≤ Subgroup.center SL(3, F))
    (ht : ∀ x, t * θ x = θ x * t) (ht2 : t * t = 1) (hneg : (-1 : Fˣ) ≠ 1) :
    InSigma F (frameGroup θ t) ((B23 F).map θ) :=
  ⟨chart₂ θ, range_chart₂ θ, diagData_chart₂ hker ht ht2 hneg⟩

theorem frameGroup_diagAction (ht : ∀ x, t * θ x = θ x * t) :
    DiagAction θ (frameGroup θ t) := fun e he => by
  obtain ⟨a, b, -, -, h⟩ := signAct_of_mem_frameGroup ht he
  exact ⟨a, b, h⟩

theorem eight_le_card_frameGroup [Finite G] (hker : θ.ker ≤ Subgroup.center SL(3, F))
    (ht : ∀ x, t * θ x = θ x * t) (ht2 : t * t = 1) (hneg : (-1 : Fˣ) ≠ 1)
    (hz : θ dgA ≠ 1) (ht1 : t ≠ 1) (hnot : t ∉ θ.range) :
    8 ≤ Nat.card (frameGroup θ t) := by
  classical
  have := Fintype.ofFinite G
  set A := frameGroup θ t with hA
  set C := axisSub A (chart₁ θ).range with hC
  have hCA : C ≤ A := inf_le_left
  have hidx : C.relIndex A = 2 := index_two_chart₁ hker ht hneg
  have h1 := (C.subgroupOf A).card_mul_index
  have h3 : Nat.card (C.subgroupOf A) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCA).toEquiv
  rw [h3] at h1
  have hidx' : (C.subgroupOf A).index = 2 := hidx
  rw [hidx'] at h1
  have hz1 : θ dgA ∈ C := by
    refine mem_axisSub_iff.mpr ⟨z₁_mem_frameGroup, ?_⟩
    exact (centralizes_chart₁_iff hker (a := -1) (b := -1) z₁_conj).mpr rfl
  have ht1' : t ∈ C := by
    refine mem_axisSub_iff.mpr ⟨t_mem_frameGroup, ?_⟩
    exact (centralizes_chart₁_iff hker (a := 1) (b := 1) (fun x => by
      rw [diagConj3_one, ht x]; group)).mpr rfl
  have hzt : θ dgA ≠ t := fun h => hnot (h ▸ ⟨dgA, rfl⟩)
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hS : ({1, θ dgA, t, θ dgA * t} : Finset G) ⊆ (C : Set G).toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Set.mem_toFinset]
    rcases hx with rfl | rfl | rfl | rfl
    · exact C.one_mem
    · exact hz1
    · exact ht1'
    · exact C.mul_mem hz1 ht1'
  have hcard : ({1, θ dgA, t, θ dgA * t} : Finset G).card = 4 := by
    have n1 : (1 : G) ∉ ({θ dgA, t, θ dgA * t} : Finset G) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨hz.symm, ht1.symm, fun h => hzt ?_⟩
      rw [← hti]
      exact eq_inv_of_mul_eq_one_left h.symm
    have n2 : θ dgA ∉ ({t, θ dgA * t} : Finset G) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨hzt, fun h => ht1 ?_⟩
      exact mul_left_cancel (a := θ dgA) (b := t) (c := 1) (by rw [mul_one]; exact h.symm)
    have n3 : t ∉ ({θ dgA * t} : Finset G) := by
      simp only [Finset.mem_singleton]
      exact fun h => hz (mul_right_cancel (a := θ dgA) (b := t) (c := 1)
        (by rw [one_mul]; exact h.symm))
    rw [Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2,
      Finset.card_insert_of_notMem n3, Finset.card_singleton]
  have h4 : 4 ≤ Nat.card C := by
    have := Finset.card_le_card hS
    rw [hcard] at this
    simpa [Nat.card_eq_fintype_card, Set.toFinset_card] using this
  omega

theorem not_commutes_chart (hker : θ.ker ≤ Subgroup.center SL(3, F)) :
    ¬ Commutes ((B12 F).map θ) ((B23 F).map θ) := by
  intro hc
  set a : SL(3, F) := blockSL F 3 2 0 (by omega) tr2 with ha
  set b : SL(3, F) := blockSL F 3 2 1 (by omega) tr2 with hb
  have h := hc (θ a) ⟨a, ⟨tr2, rfl⟩, rfl⟩ (θ b) ⟨b, ⟨tr2, rfl⟩, rfl⟩
  rw [← map_mul, ← map_mul] at h
  obtain ⟨z, hz⟩ : ∃ z : SL(3, F), z = (b * a)⁻¹ * (a * b) := ⟨_, rfl⟩
  have hk : z ∈ θ.ker := by
    rw [hz, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨ω, -, hω⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (hker hk)
  have h' : a * b = b * a * z := by rw [hz]; group
  have hm := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F)) h'
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hm
  rw [← hω, ha, hb, coe_blockSL_three_zero, coe_blockSL_three_one] at hm
  have h02 := congrFun (congrFun hm 0) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, tr2, Matrix.scalar_apply, Matrix.diagonal_apply]
    at h02

theorem chart_ne (hker : θ.ker ≤ Subgroup.center SL(3, F)) :
    (B12 F).map θ ≠ (B23 F).map θ := by
  intro h
  set a : SL(3, F) := blockSL F 3 2 0 (by omega) tr2 with ha
  have hx : θ a ∈ (B23 F).map θ := h ▸ ⟨a, ⟨tr2, rfl⟩, rfl⟩
  obtain ⟨b, ⟨s, rfl⟩, hb⟩ := hx
  obtain ⟨z, hz⟩ : ∃ z : SL(3, F), z = (blockSL F 3 2 1 (by omega) s)⁻¹ * a := ⟨_, rfl⟩
  have hk : z ∈ θ.ker := by
    rw [hz, MonoidHom.mem_ker, map_mul, map_inv, hb, inv_mul_cancel]
  obtain ⟨ω, -, hω⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (hker hk)
  have h' : a = blockSL F 3 2 1 (by omega) s * z := by rw [hz]; group
  have hm := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F)) h'
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hm
  rw [← hω, ha, coe_blockSL_three_zero, coe_blockSL_three_one] at hm
  have h01 := congrFun (congrFun hm 0) 1
  simp [Matrix.mul_apply, tr2, Matrix.scalar_apply, Matrix.diagonal_apply] at h01

end Basic

section LocalDatum

variable {F : Type} [Field F] {G : Type} [Group G]

structure LocalDatum (F : Type) [Field F] {G : Type} [Group G] (L₁ L₂ : Subgroup G) (t : G) :
    Prop where
  chart : ∃ θ : SL(3, F) →* G, θ.ker ≤ Subgroup.center SL(3, F) ∧ (B12 F).map θ = L₁ ∧
    (B23 F).map θ = L₂ ∧ ∀ x, t * θ x = θ x * t
  two_element : ∃ k : ℕ, orderOf t = 2 ^ (k + 1)

theorem LocalDatum.exists_frameGroup [Finite G] [Finite F] {L₁ L₂ : Subgroup G} {t : G}
    (hLD : LocalDatum F L₁ L₂ t) (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) :
    ∃ A : Subgroup G, 8 ≤ Nat.card A ∧ (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧
      (∀ x ∈ A, x * x = 1) ∧ InSigma F A L₁ ∧ InSigma F A L₂ ∧ ¬ Commutes L₁ L₂ ∧
        LinearA2Pair F A L₁ L₂ ∧ IsLine A L₁ L₂ ∧ IsLine A L₂ L₁ := by
  obtain ⟨θ, hker, hL₁, hL₂, ht⟩ := hLD.chart
  obtain ⟨k, hk⟩ := hLD.two_element
  set t' : G := t ^ (2 ^ k) with ht'
  have hord : orderOf t' = 2 := by
    rw [ht', orderOf_pow_of_dvd (by positivity) (by rw [hk]; exact pow_dvd_pow 2 (Nat.le_succ k)),
      hk, pow_succ, Nat.mul_div_cancel_left _ (by positivity)]
  have ht'2 : t' * t' = 1 := by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hord])
  have ht'1 : t' ≠ 1 := fun h => by
    rw [h, orderOf_one] at hord
    omega
  have htc : ∀ x, t' * θ x = θ x * t' := fun x => ((Commute.pow_left (ht x) (2 ^ k)) : _)
  have hnot : t' ∉ θ.range := fun hm =>
    ht'1 (eq_one_of_mem_range_of_centralizes hker hm htc (k := 1) (by simpa using hord))
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  have hneg : (-1 : Fˣ) ≠ 1 := fun h => h2 (by
    have := congrArg Units.val h
    simp only [Units.val_neg, Units.val_one] at this
    linear_combination -this)
  have hz : θ dgA ≠ 1 := fun h => sl2_neg_one_ne_one hodd
    (comp_blockSL_injective hker (by omega) (by omega)
      (show chart₁ θ (-1) = chart₁ θ 1 by rw [map_one]; exact h))
  have hS₁ : InSigma F (frameGroup θ t') L₁ := by
    rw [← hL₁]
    exact inSigma_frameGroup_left hker htc ht'2 hneg
  have hS₂ : InSigma F (frameGroup θ t') L₂ := by
    rw [← hL₂]
    exact inSigma_frameGroup_right hker htc ht'2 hneg
  have hLin : LinearA2Pair F (frameGroup θ t') L₁ L₂ :=
    linearA2Pair_of_diagAction hker hL₁ hL₂ (frameGroup_diagAction htc) hS₁ hS₂
  have hline := hLin.isLine hS₁ hS₂ hodd h5
  have hLnc : ¬ Commutes L₁ L₂ := by
    rw [← hL₁, ← hL₂]
    exact not_commutes_chart hker
  exact ⟨frameGroup θ t', eight_le_card_frameGroup hker htc ht'2 hneg hz ht'1 hnot,
    fun x hx y hy => frameGroup_comm htc hx hy, fun x hx => frameGroup_sq htc ht'2 hx, hS₁, hS₂,
    hLnc, hLin, hline.1, hline.2⟩

theorem LocalDatum.exists_rankFrame [Finite G] [Finite F] {L₁ L₂ : Subgroup G} {t : G}
    (hLD : LocalDatum F L₁ L₂ t) (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (h₁ : L₁ ∈ Ω) (h₂ : L₂ ∈ Ω) :
    ∃ A : Subgroup G, RankFrame F Ω A (sigmaSet F Ω A) ∧ L₁ ∈ sigmaSet F Ω A ∧
      L₂ ∈ sigmaSet F Ω A ∧ L₁ ≠ L₂ ∧ ¬ Commutes L₁ L₂ ∧ LinearA2Pair F A L₁ L₂ ∧
        IsLine A L₁ L₂ ∧ IsLine A L₂ L₁ := by
  obtain ⟨A, hcard, -, hsq, hS₁, hS₂, hnc, hLin, hl₁, hl₂⟩ := hLD.exists_frameGroup hodd h5
  obtain ⟨θ, hker, hL₁, hL₂, -⟩ := hLD.chart
  have hne : L₁ ≠ L₂ := by
    rw [← hL₁, ← hL₂]
    exact chart_ne hker
  exact ⟨A, ⟨hodd, h5, hΩ, hsq, rfl, ⟨L₁, ⟨h₁, hS₁⟩, L₂, ⟨h₂, hS₂⟩, hne⟩, hcard⟩, ⟨h₁, hS₁⟩,
    ⟨h₂, hS₂⟩, hne, hnc, hLin, hl₁, hl₂⟩

end LocalDatum

end FrameGroup

end CFSG.ClassicalInvolution
