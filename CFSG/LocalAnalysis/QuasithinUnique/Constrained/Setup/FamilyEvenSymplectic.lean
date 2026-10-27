module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.Assembly.LowTwoRank Matrix

section PlaneDiag

variable {K : Type} [Field K] {n : ℕ}

@[expose] def planeDiag (M : Fin n → Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.fromBlocks (Matrix.diagonal fun j => M j 0 0) (Matrix.diagonal fun j => M j 0 1)
    (Matrix.diagonal fun j => M j 1 0) (Matrix.diagonal fun j => M j 1 1)

theorem planeDiag_mul (M N : Fin n → Matrix (Fin 2) (Fin 2) K) :
    planeDiag M * planeDiag N = planeDiag fun j => M j * N j := by
  unfold planeDiag
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.mul_apply,
    Fin.sum_univ_two]

theorem planeDiag_one : planeDiag (fun _ : Fin n => (1 : Matrix (Fin 2) (Fin 2) K)) = 1 := by
  unfold planeDiag
  simp [Matrix.fromBlocks_one]

theorem planeDiag_transpose (M : Fin n → Matrix (Fin 2) (Fin 2) K) :
    (planeDiag M)ᵀ = planeDiag fun j => (M j)ᵀ := by
  unfold planeDiag
  simp [Matrix.fromBlocks_transpose]

@[expose] def planeGL (g : Fin n → GL (Fin 2) K) : GL (Fin n ⊕ Fin n) K :=
  ⟨planeDiag fun j => (g j : Matrix (Fin 2) (Fin 2) K),
    planeDiag fun j => ((g j)⁻¹ : GL (Fin 2) K), by
      rw [planeDiag_mul]
      simpa using planeDiag_one (K := K) (n := n), by
      rw [planeDiag_mul]
      simpa using planeDiag_one (K := K) (n := n)⟩

theorem planeGL_val (g : Fin n → GL (Fin 2) K) :
    (planeGL g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      planeDiag fun j => (g j : Matrix (Fin 2) (Fin 2) K) := rfl

@[expose] def planeHom : (Fin n → GL (Fin 2) K) →* GL (Fin n ⊕ Fin n) K where
  toFun := planeGL
  map_one' := Units.ext (by
    rw [planeGL_val]
    simpa using planeDiag_one (K := K) (n := n))
  map_mul' g h := Units.ext (by
    rw [Units.val_mul, planeGL_val, planeGL_val, planeGL_val, planeDiag_mul]
    rfl)

end PlaneDiag

section Rotation

variable {K : Type} [Field K] [CharP K 2]

@[expose] def rotR : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 1]

@[expose] def planeJ : Matrix (Fin 2) (Fin 2) K := !![0, 1; -1, 0]

omit [CharP K 2] in
theorem rotR_transpose : (rotR : Matrix (Fin 2) (Fin 2) K)ᵀ = rotR := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem rotR_sq : (rotR : Matrix (Fin 2) (Fin 2) K) * rotR = !![1, 1; 1, 0] := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotR, Matrix.mul_apply, Fin.sum_univ_two, h2]

theorem rotR_cube : (rotR : Matrix (Fin 2) (Fin 2) K) * rotR * rotR = 1 := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rw [rotR_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotR, Matrix.mul_apply, Fin.sum_univ_two, h2]

theorem rotR_symp : (rotR : Matrix (Fin 2) (Fin 2) K)ᵀ * planeJ * rotR = planeJ := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rw [rotR_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotR, planeJ, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq, h2]

theorem rotR_pow_symp (m : ℕ) :
    ((rotR : Matrix (Fin 2) (Fin 2) K) ^ m)ᵀ * planeJ * rotR ^ m = planeJ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : ((rotR : Matrix (Fin 2) (Fin 2) K) ^ (m + 1))ᵀ * planeJ * rotR ^ (m + 1) =
        rotRᵀ * ((rotR ^ m)ᵀ * planeJ * rotR ^ m) * rotR := by
      rw [pow_succ, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    rw [h1, ih, rotR_transpose]
    have := rotR_symp (K := K)
    rwa [rotR_transpose] at this

@[expose] def rotRg : GL (Fin 2) K :=
  ⟨rotR, rotR * rotR, by
    rw [← Matrix.mul_assoc]
    exact rotR_cube, rotR_cube⟩

theorem rotRg_val : (rotRg : GL (Fin 2) K).val = rotR := rfl

theorem rotRg_pow_three : (rotRg : GL (Fin 2) K) ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, rotRg_val, Units.val_one]
  have : (rotR : Matrix (Fin 2) (Fin 2) K) ^ 3 = rotR * rotR * rotR := by
    rw [pow_succ, pow_two]
  rw [this]
  exact rotR_cube

@[expose] def rotHom : Multiplicative (ZMod 3) →* GL (Fin 2) K where
  toFun x := rotRg ^ (Multiplicative.toAdd x).val
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul]
    rw [← pow_add, ZMod.val_add]
    conv_rhs => rw [← Nat.mod_add_div
      ((Multiplicative.toAdd x).val + (Multiplicative.toAdd y).val) 3,
      pow_add, pow_mul, rotRg_pow_three, one_pow, mul_one]

theorem rotHom_apply (x : Multiplicative (ZMod 3)) :
    (rotHom x : GL (Fin 2) K) = rotRg ^ (Multiplicative.toAdd x).val := rfl

theorem rotR_pow_entry (x : ZMod 3) :
    ((rotR : Matrix (Fin 2) (Fin 2) K) ^ x.val) 0 1 = if x = 0 then 0 else 1 := by
  have hx : x = 0 ∨ x = 1 ∨ x = 2 := by
    revert x
    decide
  rcases hx with rfl | rfl | rfl
  · simp
  · have : (1 : ZMod 3).val = 1 := rfl
    simp [this, rotR]
  · have : (2 : ZMod 3).val = 2 := rfl
    rw [this, pow_two, rotR_sq]
    simp
    decide

end Rotation

section ThreeRank

variable {K : Type} [Field K] [CharP K 2] {n : ℕ}

omit [CharP K 2] in
theorem fromBlocks_J_eq :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      planeDiag fun _ => planeJ := by
  unfold planeDiag planeJ
  simp
  rw [← Matrix.diagonal_one, ← Matrix.diagonal_neg]

omit [CharP K 2] in
theorem planeGL_mem_statedSp (g : Fin n → GL (Fin 2) K)
    (hg : ∀ j, ((g j : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ * planeJ *
      (g j : Matrix (Fin 2) (Fin 2) K) = planeJ) : planeGL g ∈ StatedSp n K := by
  apply Subgroup.subset_closure
  show ((planeGL g : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ *
    Matrix.fromBlocks 0 1 (-1) 0 * (planeGL g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
    Matrix.fromBlocks 0 1 (-1) 0
  rw [planeGL_val, fromBlocks_J_eq, planeDiag_transpose, planeDiag_mul, planeDiag_mul]
  congr 1
  funext j
  exact hg j

@[expose] def threeToSp : (Fin n → Multiplicative (ZMod 3)) →* ↥(StatedSp n K) :=
  (planeHom.comp (MonoidHom.compLeft rotHom (Fin n))).codRestrict (StatedSp n K) fun a => by
    refine planeGL_mem_statedSp _ fun j => ?_
    show ((rotRg ^ (Multiplicative.toAdd (a j)).val : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ *
      planeJ * ((rotRg ^ (Multiplicative.toAdd (a j)).val : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = planeJ
    rw [Units.val_pow_eq_pow_val, rotRg_val]
    exact rotR_pow_symp _

theorem threeToSp_val (a : Fin n → Multiplicative (ZMod 3)) :
    ((threeToSp a : ↥(StatedSp n K)) : GL (Fin n ⊕ Fin n) K) =
      planeGL fun j => rotHom (a j) := rfl

@[expose] def threeToProj : (Fin n → Multiplicative (ZMod 3)) →* StatedProj (StatedSp n K) :=
  (QuotientGroup.mk' ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K))).comp threeToSp

theorem threeToProj_injective :
    Function.Injective (threeToProj (K := K) (n := n)) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  rw [threeToProj, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at ha
  obtain ⟨c, hc⟩ := ha
  funext j
  have h1 := congrArg
    (fun A : GL (Fin n ⊕ Fin n) K => (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
      (Sum.inl j) (Sum.inr j)) hc
  rw [threeToSp_val] at h1
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_ne _
    (Sum.inl_ne_inr), planeGL_val] at h1
  simp only [planeDiag, rotHom_apply, Matrix.fromBlocks_apply₁₂, Matrix.diagonal_apply_eq,
    Units.val_pow_eq_pow_val, rotRg_val] at h1
  have h2 := rotR_pow_entry (K := K) (Multiplicative.toAdd (a j))
  rw [← h1] at h2
  have h3 : Multiplicative.toAdd (a j) = 0 := by
    by_contra hne
    simp [hne] at h2
  exact Multiplicative.toAdd.injective h3

theorem card_threePow : Nat.card (Fin n → Multiplicative (ZMod 3)) = 3 ^ n := by
  rw [Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := Fin n)]
  simp [ZMod.card]

theorem threeToProj_comm (a b : Fin n → Multiplicative (ZMod 3)) :
    threeToProj (K := K) a * threeToProj b = threeToProj b * threeToProj a := by
  rw [← map_mul, ← map_mul, mul_comm]

theorem pow_three_domain (a : Fin n → Multiplicative (ZMod 3)) : a ^ 3 = 1 := by
  have h3 : ∀ x : ZMod 3, 3 • x = 0 := by decide
  funext j
  show (a j) ^ 3 = 1
  apply Multiplicative.toAdd.injective
  simp only [toAdd_pow, toAdd_one]
  exact h3 _

theorem threeToProj_pow_three (a : Fin n → Multiplicative (ZMod 3)) :
    threeToProj (K := K) a ^ 3 = 1 := by
  rw [← map_pow, pow_three_domain, map_one]

theorem even_symplectic_three_rank (n : ℕ) :
    ∃ E : Subgroup (StatedProj (StatedSp n K)), CFSG.IsElementaryAbelian 3 ↥E ∧
      Nat.card ↥E = 3 ^ n := by
  refine ⟨(threeToProj (K := K) (n := n)).range, ?_, ?_⟩
  · refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩
             exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_ }
    · obtain ⟨_, a, rfl⟩ := x
      obtain ⟨_, b, rfl⟩ := y
      exact Subtype.ext (threeToProj_comm a b)
    · obtain ⟨_, a, rfl⟩ := x
      exact Subtype.ext (threeToProj_pow_three a)
  · rw [← card_threePow (n := n)]
    exact (Nat.card_congr (MonoidHom.ofInjective threeToProj_injective).toEquiv).symm

end ThreeRank

theorem even_symplectic_sqt_le_two {K : Type} [Field K] [CharP K 2] [Finite K] (n : ℕ)
    (h : CFSG.IsStronglyQuasithin (StatedProj (StatedSp n K))) : n ≤ 2 := by
  have hrank := CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num)
    (fun a b => mul_comm a b) (fun a => pow_three_domain a)
    (card_threePow (n := n)) (threeToProj (K := K) (n := n)) threeToProj_injective
    (H := ⊤) le_top
  have hle := (CFSG.SectionRank.isStronglyQuasithin_iff.1 h) 3 Nat.prime_three (by norm_num)
  omega

end CFSG.QuasithinUnique.Setup.Family
