module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

section MulClosed

variable {G : Type*} [Group G] [Finite G]

theorem inv_mem_of_mulClosed {S : Set G} (h1 : (1 : G) ∈ S)
    (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) {x : G} (hx : x ∈ S) : x⁻¹ ∈ S := by
  have hpow : ∀ n : ℕ, x ^ n ∈ S := fun n => by
    induction n with
    | zero => simpa using h1
    | succ n ih =>
      rw [pow_succ]
      exact hmul _ ih _ hx
  obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers (x := x) (y := x⁻¹)).2
    (Subgroup.inv_mem _ (Subgroup.mem_zpowers x))
  change x ^ n = x⁻¹ at hn
  rw [← hn]
  exact hpow n

@[expose] def uFiveSubgroupOfMulClosed (S : Set G) (h1 : (1 : G) ∈ S)
    (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) : Subgroup G where
  carrier := S
  one_mem' := h1
  mul_mem' := fun {a b} ha hb => hmul a ha b hb
  inv_mem' := fun {_} hx => inv_mem_of_mulClosed h1 hmul hx

end MulClosed

variable {F : Type*} [Field F]

@[expose] def IsStrictUpperFive (N : Matrix (Fin 5) (Fin 5) F) : Prop :=
  ∀ i j : Fin 5, j ≤ i → N i j = 0

theorem IsStrictUpperFive.eq {N : Matrix (Fin 5) (Fin 5) F} (hN : IsStrictUpperFive N) :
    N = !![0, N 0 1, N 0 2, N 0 3, N 0 4; 0, 0, N 1 2, N 1 3, N 1 4; 0, 0, 0, N 2 3, N 2 4;
      0, 0, 0, 0, N 3 4; 0, 0, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> exact hN _ _ (by decide)

theorem isStrictUpperFive_of_eq {N : Matrix (Fin 5) (Fin 5) F} {a01 a02 a03 a04 a12 a13 a14 a23
    a24 a34 : F} (h : N = !![0, a01, a02, a03, a04; 0, 0, a12, a13, a14; 0, 0, 0, a23, a24;
      0, 0, 0, 0, a34; 0, 0, 0, 0, 0]) : IsStrictUpperFive N := by
  subst h
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

theorem IsStrictUpperFive.add {N N' : Matrix (Fin 5) (Fin 5) F} (hN : IsStrictUpperFive N)
    (hN' : IsStrictUpperFive N') : IsStrictUpperFive (N + N') := fun i j hij => by
  rw [Matrix.add_apply, hN i j hij, hN' i j hij, add_zero]

theorem IsStrictUpperFive.smul {N : Matrix (Fin 5) (Fin 5) F} (hN : IsStrictUpperFive N)
    (a : F) : IsStrictUpperFive (a • N) := fun i j hij => by
  rw [Matrix.smul_apply, hN i j hij, smul_zero]

theorem isStrictUpperFive_single {i j : Fin 5} (hij : i < j) (a : F) :
    IsStrictUpperFive (single i j a) := fun k l hkl => by
  rw [Matrix.single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact absurd hkl (not_le.2 hij)
  · rfl

theorem det_one_add_of_isStrictUpperFive {N : Matrix (Fin 5) (Fin 5) F}
    (hN : IsStrictUpperFive N) : (1 + N).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [hN _ _ le_rfl]
  · intro i j hij
    have hij' : j < i := hij
    rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij'), hN i j hij'.le, add_zero]

@[expose] def uFiveElt (N : Matrix (Fin 5) (Fin 5) F) (hN : IsStrictUpperFive N) :
    unitriangular 5 F :=
  ⟨⟨1 + N, det_one_add_of_isStrictUpperFive hN⟩, by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · change (1 + N) i j = 0
      rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij), hN i j hij.le, add_zero]
    · change (1 + N) i i = 1
      rw [Matrix.add_apply, Matrix.one_apply_eq, hN i i le_rfl, add_zero]⟩

abbrev ypsMat (x : unitriangular 5 F) : Matrix (Fin 5) (Fin 5) F :=
  ((x : SpecialLinearGroup (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)

theorem ypsMat_mul (x y : unitriangular 5 F) : ypsMat (x * y) = ypsMat x * ypsMat y := rfl

theorem ypsMat_one : ypsMat (1 : unitriangular 5 F) = 1 := rfl

theorem ypsMat_uFiveElt {N : Matrix (Fin 5) (Fin 5) F} (hN : IsStrictUpperFive N) :
    ypsMat (uFiveElt N hN) = 1 + N := rfl

theorem ypsMat_injective : Function.Injective (ypsMat (F := F)) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

theorem ypsMat_apply_of_lt (x : unitriangular 5 F) {i j : Fin 5} (h : j < i) : ypsMat x i j = 0 :=
  x.2.1 i j h

theorem ypsMat_apply_self (x : unitriangular 5 F) (i : Fin 5) : ypsMat x i i = 1 :=
  x.2.2 i

theorem isStrictUpperFive_ypsMat_sub_one (x : unitriangular 5 F) :
    IsStrictUpperFive (ypsMat x - 1) := fun i j hij => by
  rcases hij.lt_or_eq with h | h
  · rw [Matrix.sub_apply, ypsMat_apply_of_lt x h, Matrix.one_apply_ne (ne_of_gt h), sub_zero]
  · subst h
    rw [Matrix.sub_apply, ypsMat_apply_self, Matrix.one_apply_eq, sub_self]

theorem ypsMat_eq (x : unitriangular 5 F) :
    ypsMat x = !![1, ypsMat x 0 1, ypsMat x 0 2, ypsMat x 0 3, ypsMat x 0 4;
      0, 1, ypsMat x 1 2, ypsMat x 1 3, ypsMat x 1 4; 0, 0, 1, ypsMat x 2 3, ypsMat x 2 4;
      0, 0, 0, 1, ypsMat x 3 4; 0, 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    first
    | exact ypsMat_apply_self x _
    | exact ypsMat_apply_of_lt x (by decide)

@[expose] def uFiveRoot (i j : Fin 5) (hij : i < j) (a : F) : unitriangular 5 F :=
  uFiveElt (single i j a) (isStrictUpperFive_single hij a)

theorem ypsMat_uFiveRoot (i j : Fin 5) (hij : i < j) (a : F) :
    ypsMat (uFiveRoot i j hij a) = 1 + single i j a := rfl

theorem uFiveRoot_mul (i j : Fin 5) (hij : i < j) (a b : F) :
    uFiveRoot i j hij a * uFiveRoot i j hij b = uFiveRoot i j hij (a + b) := by
  apply ypsMat_injective
  rw [ypsMat_mul, ypsMat_uFiveRoot, ypsMat_uFiveRoot, ypsMat_uFiveRoot]
  have h0 : single i j a * single i j b = 0 := single_mul_single_of_ne a i j i (ne_of_gt hij) b
  simp only [add_mul, mul_add, one_mul, mul_one, h0, add_zero, single_add]
  abel

theorem uFiveRoot_inv (i j : Fin 5) (hij : i < j) (a : F) :
    (uFiveRoot i j hij a)⁻¹ = uFiveRoot i j hij (-a) :=
  inv_eq_of_mul_eq_one_right (by
    rw [uFiveRoot_mul, add_neg_cancel]
    exact ypsMat_injective (by rw [ypsMat_uFiveRoot, single_zero, add_zero, ypsMat_one]))

theorem ypsMat_mul_apply_succ (x y : unitriangular 5 F) (k : Fin 4) :
    ypsMat (x * y) k.castSucc k.succ = ypsMat x k.castSucc k.succ + ypsMat y k.castSucc k.succ := by
  rw [ypsMat_mul, ypsMat_eq x, ypsMat_eq y]
  fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_five] <;> ring

section Finite

variable [Finite F]

@[expose] def uFiveTwisted (e : F) : Subgroup (unitriangular 5 F) :=
  uFiveSubgroupOfMulClosed {x | ypsMat x 1 2 = 0 ∧ ypsMat x 1 3 = 0 ∧ ypsMat x 2 3 = 0 ∧
      ypsMat x 3 4 = 0 ∧ ypsMat x 1 4 = -e * ypsMat x 0 2 ∧ ypsMat x 2 4 = e * ypsMat x 0 1}
    (by simp [ypsMat_one])
    (by
      rintro x ⟨h1, h2, h3, h4, h5, h6⟩ y ⟨h1', h2', h3', h4', h5', h6'⟩
      simp only [Set.mem_ofPred_eq, ypsMat_mul]
      rw [ypsMat_eq x, ypsMat_eq y]
      simp only [Matrix.mul_apply, Fin.sum_univ_five]
      simp [h1, h2, h3, h4, h5, h6, h1', h2', h3', h4', h5', h6']
      constructor <;> ring)

theorem mem_uFiveTwisted {e : F} {x : unitriangular 5 F} :
    x ∈ uFiveTwisted e ↔ ypsMat x 1 2 = 0 ∧ ypsMat x 1 3 = 0 ∧ ypsMat x 2 3 = 0 ∧
      ypsMat x 3 4 = 0 ∧ ypsMat x 1 4 = -e * ypsMat x 0 2 ∧ ypsMat x 2 4 = e * ypsMat x 0 1 :=
  Iff.rfl

@[expose] def uFiveRow : Subgroup (unitriangular 5 F) :=
  uFiveSubgroupOfMulClosed {x | ypsMat x 1 2 = 0 ∧ ypsMat x 1 3 = 0 ∧ ypsMat x 1 4 = 0 ∧
      ypsMat x 2 3 = 0 ∧ ypsMat x 2 4 = 0 ∧ ypsMat x 3 4 = 0}
    (by simp [ypsMat_one])
    (by
      rintro x ⟨h1, h2, h3, h4, h5, h6⟩ y ⟨h1', h2', h3', h4', h5', h6'⟩
      simp only [Set.mem_ofPred_eq, ypsMat_mul]
      rw [ypsMat_eq x, ypsMat_eq y]
      simp only [Matrix.mul_apply, Fin.sum_univ_five]
      simp [h1, h2, h3, h4, h5, h6, h1', h2', h3', h4', h5', h6'])

theorem mem_uFiveRow {x : unitriangular 5 F} :
    x ∈ uFiveRow ↔ ypsMat x 1 2 = 0 ∧ ypsMat x 1 3 = 0 ∧ ypsMat x 1 4 = 0 ∧
      ypsMat x 2 3 = 0 ∧ ypsMat x 2 4 = 0 ∧ ypsMat x 3 4 = 0 := Iff.rfl

@[expose] def uFiveCol : Subgroup (unitriangular 5 F) :=
  uFiveSubgroupOfMulClosed {x | ypsMat x 0 1 = 0 ∧ ypsMat x 0 2 = 0 ∧ ypsMat x 0 3 = 0 ∧
      ypsMat x 1 2 = 0 ∧ ypsMat x 1 3 = 0 ∧ ypsMat x 2 3 = 0}
    (by simp [ypsMat_one])
    (by
      rintro x ⟨h1, h2, h3, h4, h5, h6⟩ y ⟨h1', h2', h3', h4', h5', h6'⟩
      simp only [Set.mem_ofPred_eq, ypsMat_mul]
      rw [ypsMat_eq x, ypsMat_eq y]
      simp only [Matrix.mul_apply, Fin.sum_univ_five]
      simp [h1, h2, h3, h4, h5, h6, h1', h2', h3', h4', h5', h6'])

theorem mem_uFiveCol {x : unitriangular 5 F} :
    x ∈ uFiveCol ↔ ypsMat x 0 1 = 0 ∧ ypsMat x 0 2 = 0 ∧ ypsMat x 0 3 = 0 ∧
      ypsMat x 1 2 = 0 ∧ ypsMat x 1 3 = 0 ∧ ypsMat x 2 3 = 0 := Iff.rfl

theorem uFiveTwisted_zero : uFiveTwisted (0 : F) = uFiveRow := by
  ext x
  rw [mem_uFiveTwisted, mem_uFiveRow]
  simp only [zero_mul, neg_zero]
  tauto

end Finite

end CFSG.SeitzReduction.LinearPilot
