module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpBlocks
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.Sp

public section

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.Universal
  CFSG.LieType.Universal.Symplectic CFSG.AGLEmbeddingD2.ParabLevi TauCeti.GLSymplecticFin

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

section MulE

variable {n : ℕ} {F : Type} [Field F]

theorem mulE_diff (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (a b : Fin n) (hab : a ≠ b)
    (x y : Fin n ⊕ Fin n) :
    (M * E F (.difference a b hab)) x y =
      (if y = Sum.inl b then M x (Sum.inl a) else 0) -
        (if y = Sum.inr a then M x (Sum.inr b) else 0) := by
  simp only [E, Matrix.mul_sub, Matrix.sub_apply]
  by_cases h1 : y = Sum.inl b
  · subst h1
    simp
  · by_cases h2 : y = Sum.inr a
    · subst h2
      simp
    · simp [h1, h2, Matrix.mul_single_apply_of_ne, Ne.symm h1, Ne.symm h2]

theorem mulE_sum (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (a b : Fin n) (hab : a < b)
    (x y : Fin n ⊕ Fin n) :
    (M * E F (.positiveSum a b hab)) x y =
      (if y = Sum.inr b then M x (Sum.inl a) else 0) +
        (if y = Sum.inr a then M x (Sum.inl b) else 0) := by
  simp only [E, Matrix.mul_add, Matrix.add_apply]
  by_cases h1 : y = Sum.inr b
  · subst h1
    have : (Sum.inr b : Fin n ⊕ Fin n) ≠ Sum.inr a := fun h => hab.ne' (Sum.inr_injective h)
    simp [Matrix.mul_single_apply_of_ne, this]
  · by_cases h2 : y = Sum.inr a
    · subst h2
      simp [Matrix.mul_single_apply_of_ne, h1]
    · simp [h1, h2, Matrix.mul_single_apply_of_ne, Ne.symm h1, Ne.symm h2]

theorem mulE_long (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (a : Fin n)
    (x y : Fin n ⊕ Fin n) :
    (M * E F (.positiveLong a)) x y = if y = Sum.inr a then M x (Sum.inl a) else 0 := by
  simp only [E]
  by_cases h1 : y = Sum.inr a
  · subst h1; simp
  · simp [h1, Matrix.mul_single_apply_of_ne, Ne.symm h1]

end MulE

section Sympl

abbrev Jmat (n : ℕ) (F : Type) [Field F] : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
  CFSG.ClassicalInvolution.Models.SymplecticPairs.gram F n

variable {n : ℕ} {F : Type} [Field F]

theorem gram_form (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (x y : Fin n ⊕ Fin n) :
    (G * Jmat n F * Gᵀ) x y =
      ∑ i, (G x (Sum.inl i) * G y (Sum.inr i) - G x (Sum.inr i) * G y (Sum.inl i)) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Jmat,
    CFSG.ClassicalInvolution.Models.SymplecticPairs.gram, Fintype.sum_sum_type]
  simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.one_apply, Matrix.neg_apply, mul_ite,
    mul_zero, mul_one, mul_neg, ite_mul, zero_mul, one_mul, neg_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_neg_distrib, Finset.sum_const_zero,
    zero_add, add_zero]
  rw [Finset.sum_sub_distrib]
  ring

theorem mat_mul_gram_mul_transpose (g : StatedSp n F) :
    mat n F g * Jmat n F * (mat n F g)ᵀ = Jmat n F := by
  set G := mat n F g with hG
  set J := Jmat n F with hJ
  have hJJ : J * J = -1 := CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_mul_gram
  have h2 : Gᵀ * J * G = J := mat_transpose_mul_gram_mul g
  have hHG : (-(J * Gᵀ * J)) * G = 1 := by
    calc (-(J * Gᵀ * J)) * G = -(J * (Gᵀ * J * G)) := by
          simp only [Matrix.neg_mul, Matrix.mul_assoc]
      _ = 1 := by rw [h2, hJJ, neg_neg]
  have hGH : G * (-(J * Gᵀ * J)) = 1 := mul_eq_one_comm.1 hHG
  calc G * J * Gᵀ = G * J * Gᵀ * (-(J * J)) := by rw [hJJ]; simp
    _ = (G * (-(J * Gᵀ * J))) * J := by
        simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    _ = J := by rw [hGH, Matrix.one_mul]

end Sympl

section Peel

variable {n : ℕ} {F : Type} [Field F] (j : Fin n)

@[expose] def isA : Fin n ⊕ Fin n → Prop
  | .inl a => a ≤ j
  | .inr _ => False

@[expose] def isA' : Fin n ⊕ Fin n → Prop
  | .inl _ => False
  | .inr a => a ≤ j

@[expose] def Allowed (x y : Fin n ⊕ Fin n) : Prop :=
  (isA j x ∧ ¬ isA j y) ∨ (¬ isA j x ∧ ¬ isA' j x ∧ isA' j y)

@[expose] def IsSh (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) : Prop :=
  ∀ x y, ¬ Allowed j x y → M x y = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) x y

variable {j}

theorem IsSh.col_A {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} (h : IsSh j M) {a : Fin n}
    (ha : a ≤ j) (x : Fin n ⊕ Fin n) :
    M x (Sum.inl a) = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) x (Sum.inl a) :=
  h x _ (by simp [Allowed, isA, isA', ha])

theorem IsSh.row_A' {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} (h : IsSh j M) {a : Fin n}
    (ha : a ≤ j) (y : Fin n ⊕ Fin n) :
    M (Sum.inr a) y = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (Sum.inr a) y :=
  h _ y (by simp [Allowed, isA, isA', ha])

theorem IsSh.of_delta {M M' Δ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} (h : IsSh j M) (c : F)
    (hM' : M' = M + c • Δ) (hΔ : ∀ x y, ¬ Allowed j x y → Δ x y = 0) : IsSh j M' := by
  intro x y hxy
  rw [hM', Matrix.add_apply, h x y hxy, Matrix.smul_apply, hΔ x y hxy, smul_zero, add_zero]

theorem IsSh.zero_of_not_isA {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} (h : IsSh j M)
    {a : Fin n} (ha : a ≤ j) {x : Fin n ⊕ Fin n} (hx : ¬ isA j x) : M x (Sum.inl a) = 0 := by
  rw [h.col_A ha]
  refine Matrix.one_apply_ne ?_
  rintro rfl
  exact hx ha

theorem not_allowed_inr {x : Fin n ⊕ Fin n} {a : Fin n} (ha : a ≤ j)
    (h : ¬ Allowed j x (Sum.inr a)) : ∃ a2, a2 ≤ j ∧ x = Sum.inr a2 := by
  rcases x with x | x
  · exfalso
    apply h
    by_cases hx : x ≤ j
    · exact Or.inl ⟨hx, by simp [isA]⟩
    · exact Or.inr ⟨hx, by simp [isA'], ha⟩
  · refine ⟨x, ?_, rfl⟩
    by_contra hx
    apply h; right
    exact ⟨by simp [isA], by simpa [isA'] using hx, by simpa [isA'] using ha⟩

theorem sh_mul_diff {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} (hM : IsSh j M) {a b : Fin n}
    (hab : a ≠ b) (ha : a ≤ j) (hb : j < b) (c : F) :
    IsSh j (M * (1 + c • E F (.difference a b hab))) := by
  refine hM.of_delta c (by rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]) ?_
  intro x y hxy
  rw [mulE_diff]
  have hbj : ¬ b ≤ j := not_le.mpr hb
  by_cases h1 : y = Sum.inl b
  · subst h1
    have hx : ¬ isA j x := fun hx => hxy (Or.inl ⟨hx, by simpa [isA] using hbj⟩)
    have := hM.zero_of_not_isA ha hx
    simp [this]
  · by_cases h2 : y = Sum.inr a
    · subst h2
      obtain ⟨a2, ha2, rfl⟩ := not_allowed_inr ha hxy
      have : M (Sum.inr a2) (Sum.inr b) = 0 := by
        rw [hM.row_A' ha2]
        refine Matrix.one_apply_ne ?_
        intro h
        have := Sum.inr_injective h
        subst this
        exact hbj ha2
      simp [h1, this]
    · simp [h1, h2]

theorem sh_mul_sum {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} (hM : IsSh j M) {a b : Fin n}
    (hab : a < b) (ha : a ≤ j) (hb : j < b) (c : F) :
    IsSh j (M * (1 + c • E F (.positiveSum a b hab))) := by
  refine hM.of_delta c (by rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]) ?_
  intro x y hxy
  rw [mulE_sum]
  have hbj : ¬ b ≤ j := not_le.mpr hb
  by_cases h1 : y = Sum.inr b
  · subst h1
    have hx : ¬ isA j x := fun hx => hxy (Or.inl ⟨hx, by simp [isA]⟩)
    have := hM.zero_of_not_isA ha hx
    have h2 : (Sum.inr b : Fin n ⊕ Fin n) ≠ Sum.inr a := fun h => hab.ne' (Sum.inr_injective h)
    simp [this, h2]
  · by_cases h2 : y = Sum.inr a
    · subst h2
      obtain ⟨a2, ha2, rfl⟩ := not_allowed_inr ha hxy
      have : M (Sum.inr a2) (Sum.inl b) = 0 := by
        rw [hM.row_A' ha2]
        exact Matrix.one_apply_ne (by simp)
      simp [h1, this]
    · simp [h1, h2]

end Peel

section RadElt

open CFSG.AGLEmbedding.LieOut

variable {n : ℕ} {F : Type} [Field F]

theorem elt_mem_radical (r : RootSubgroupIndex n) (c : F) (j : Fin n)
    (h : 0 < cumE (stdVec r) j) : elt r c ∈ radical (rootDatum n F) j := by
  set γ := fundOf (stdVec r) with hγ
  have hr : stdVec r = toStd n γ := (toStd_fundOf _ (even_cumE_last r)).symm
  have hroot : γ ∈ (rootDatum n F).roots := by
    change γ ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanC n) ∅
    rw [roots_eq]
    exact ⟨r, hr⟩
  have hpos : 0 < γ j := by
    simp only [hγ, fundOf]
    by_cases hl : j.val + 1 = n
    · rw [if_pos hl]
      exact Int.ediv_pos_of_pos_of_dvd h (by norm_num) (even_cumE_last r j hl)
    · rw [if_neg hl]; simpa using h
  exact rootGroup_le_radical hroot hpos (elt_mem_rootGroup hr c)

end RadElt

section ShapeSymp

variable {n : ℕ} {F : Type} [Field F] {j : Fin n}

@[expose] def IsSh0 (j : Fin n) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) : Prop :=
  ∀ x y, ¬ (isA j x ∧ isA' j y) → M x y = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) x y

theorem col_A'_zero {g : StatedSp n F} (hsh : IsSh j (mat n F g))
    (h1 : ∀ a b, a ≤ j → j < b → mat n F g (Sum.inl a) (Sum.inl b) = 0)
    (h2 : ∀ a b, a ≤ j → j < b → mat n F g (Sum.inl a) (Sum.inr b) = 0) {a : Fin n} (ha : a ≤ j)
    {x : Fin n ⊕ Fin n} (hxA : ¬ isA j x) (hxA' : ¬ isA' j x) :
    mat n F g x (Sum.inr a) = 0 := by
  have key := gram_form (mat n F g) (Sum.inl a) x
  rw [mat_mul_gram_mul_transpose g] at key
  have hJ : Jmat n F (Sum.inl a) x = 0 := by
    simp only [Jmat, CFSG.ClassicalInvolution.Models.SymplecticPairs.gram]
    rcases x with x | x
    · simp
    · have : x ≠ a := by
        rintro rfl
        exact hxA' ha
      simp [Matrix.one_apply, Ne.symm this]
  rw [hJ] at key
  have hcol : ∀ i, mat n F g (Sum.inl a) (Sum.inl i) = if i = a then 1 else 0 := by
    intro i
    by_cases hi : i ≤ j
    · rw [hsh.col_A hi]; simp [Matrix.one_apply, eq_comm]
    · rw [h1 a i ha (not_le.mp hi)]
      have : i ≠ a := fun h => hi (h ▸ ha)
      simp [this]
  have hterm : ∀ i, mat n F g (Sum.inl a) (Sum.inr i) * mat n F g x (Sum.inl i) = 0 := by
    intro i
    by_cases hi : i ≤ j
    · rw [hsh.zero_of_not_isA hi hxA, mul_zero]
    · rw [h2 a i ha (not_le.mp hi), zero_mul]
  simpa [hterm, hcol] using key.symm

theorem sh0_of_zero {g : StatedSp n F} (hsh : IsSh j (mat n F g))
    (h1 : ∀ a b, a ≤ j → j < b → mat n F g (Sum.inl a) (Sum.inl b) = 0)
    (h2 : ∀ a b, a ≤ j → j < b → mat n F g (Sum.inl a) (Sum.inr b) = 0) :
    IsSh0 j (mat n F g) := by
  intro x y hxy
  by_cases hall : Allowed j x y
  · rcases hall with ⟨hx, hy⟩ | ⟨hx, hx', hy⟩
    · rcases x with a | a
      · have hya : ¬ isA' j y := fun h => hxy ⟨hx, h⟩
        have ha : a ≤ j := hx
        rcases y with b | b
        · have hb : j < b := not_le.mp hy
          rw [h1 a b ha hb]
          exact (Matrix.one_apply_ne (by intro h; have := Sum.inl_injective h; subst this; exact hy hx)).symm
        · have hb : j < b := not_le.mp hya
          rw [h2 a b ha hb]
          exact (Matrix.one_apply_ne (by simp)).symm
      · exact hx.elim
    · rcases y with b | b
      · exact hy.elim
      · have ha : b ≤ j := hy
        rw [col_A'_zero hsh h1 h2 ha hx hx']
        refine (Matrix.one_apply_ne ?_).symm
        rintro rfl
        exact hx' ha
  · exact hsh x y hall

end ShapeSymp

section LeftMul

variable {n : ℕ} {F : Type} [Field F]

theorem Emul_long (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (a : Fin n)
    (x y : Fin n ⊕ Fin n) :
    (E F (.positiveLong a) * M) x y = if x = Sum.inl a then M (Sum.inr a) y else 0 := by
  simp only [E]
  by_cases h1 : x = Sum.inl a
  · subst h1; simp [Matrix.single_mul_apply_same]
  · simp [h1, Matrix.single_mul_apply_of_ne, Ne.symm h1]

theorem Emul_diff (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (a b : Fin n) (hab : a ≠ b)
    (x y : Fin n ⊕ Fin n) :
    (E F (.difference a b hab) * M) x y =
      (if x = Sum.inl a then M (Sum.inl b) y else 0) -
        (if x = Sum.inr b then M (Sum.inr a) y else 0) := by
  simp only [E, Matrix.sub_mul, Matrix.sub_apply]
  by_cases h1 : x = Sum.inl a
  · subst h1; simp [Matrix.single_mul_apply_same]
  · by_cases h2 : x = Sum.inr b
    · subst h2; simp [Matrix.single_mul_apply_same]
    · simp [h1, h2, Matrix.single_mul_apply_of_ne, Ne.symm h1, Ne.symm h2]

theorem Emul_sum (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (a b : Fin n) (hab : a < b)
    (x y : Fin n ⊕ Fin n) :
    (E F (.positiveSum a b hab) * M) x y =
      (if x = Sum.inl a then M (Sum.inr b) y else 0) +
        (if x = Sum.inl b then M (Sum.inr a) y else 0) := by
  simp only [E, Matrix.add_mul, Matrix.add_apply]
  by_cases h1 : x = Sum.inl a
  · subst h1
    have : (Sum.inl a : Fin n ⊕ Fin n) ≠ Sum.inl b := fun h => hab.ne (Sum.inl_injective h)
    simp [Matrix.single_mul_apply_same, Matrix.single_mul_apply_of_ne, this]
  · by_cases h2 : x = Sum.inl b
    · subst h2; simp [Matrix.single_mul_apply_same, Matrix.single_mul_apply_of_ne, h1]
    · simp [h1, h2, Matrix.single_mul_apply_of_ne, Ne.symm h1, Ne.symm h2]

end LeftMul

section Shape

variable {n : ℕ} {F : Type} [Field F] [CharP F 2]

theorem comm_mat_of_comm {g : StatedSp n F} (r : RootSubgroupIndex n)
    (h : g * elt r (1 : F) = elt r 1 * g) : mat n F g * E F r = E F r * mat n F g := by
  have := congrArg (mat n F) h
  rw [map_mul, map_mul, mat_elt] at this
  simpa [Matrix.mul_add, Matrix.add_mul] using this

theorem sq_eq_one_char_two {c : F} (h : c ^ 2 = 1) : c = 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have : (c - 1) ^ 2 = 0 := by linear_combination h + (1 - c) * h2
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this)

theorem col_row_of_comm_long {g : StatedSp n F} (a : Fin n)
    (h : mat n F g * E F (.positiveLong a) = E F (.positiveLong a) * mat n F g) :
    (∀ x, mat n F g x (Sum.inl a) = if x = Sum.inl a then 1 else 0) ∧
      (∀ y, mat n F g (Sum.inr a) y = if y = Sum.inr a then 1 else 0) := by
  have key : ∀ x y, (mat n F g * E F (.positiveLong a)) x y =
      (E F (.positiveLong a) * mat n F g) x y := fun x y => by rw [h]
  simp only [mulE_long, Emul_long] at key
  have hx : ∀ x, x ≠ Sum.inl a → mat n F g x (Sum.inl a) = 0 := fun x hx => by
    have := key x (Sum.inr a)
    simpa [hx] using this
  have hy : ∀ y, y ≠ Sum.inr a → mat n F g (Sum.inr a) y = 0 := fun y hy => by
    have := key (Sum.inl a) y
    simpa [hy] using this.symm
  have hd : mat n F g (Sum.inl a) (Sum.inl a) = mat n F g (Sum.inr a) (Sum.inr a) := by
    simpa using key (Sum.inl a) (Sum.inr a)
  have hsy := gram_form (mat n F g) (Sum.inl a) (Sum.inr a)
  rw [mat_mul_gram_mul_transpose g] at hsy
  have hJ : Jmat n F (Sum.inl a) (Sum.inr a) = 1 := by
    simp [Jmat, CFSG.ClassicalInvolution.Models.SymplecticPairs.gram]
  rw [hJ] at hsy
  have hterm : ∀ i, mat n F g (Sum.inl a) (Sum.inl i) * mat n F g (Sum.inr a) (Sum.inr i) -
      mat n F g (Sum.inl a) (Sum.inr i) * mat n F g (Sum.inr a) (Sum.inl i) =
      if i = a then mat n F g (Sum.inr a) (Sum.inr a) ^ 2 else 0 := by
    intro i
    by_cases hi : i = a
    · subst hi
      rw [hy (Sum.inl i) (by simp), hd]; simp [sq]
    · rw [hy (Sum.inl i) (by simp), hy (Sum.inr i) (fun h => hi (Sum.inr_injective h))]; simp [hi]
  simp only [hterm] at hsy
  simp at hsy
  have hc : mat n F g (Sum.inr a) (Sum.inr a) = 1 := sq_eq_one_char_two hsy.symm
  refine ⟨fun x => ?_, fun y => ?_⟩
  · by_cases hxa : x = Sum.inl a
    · subst hxa; simp [hd, hc]
    · simp [hxa, hx x hxa]
  · by_cases hya : y = Sum.inr a
    · subst hya; simp [hc]
    · simp [hya, hy y hya]

theorem entries_of_comm_diff {g : StatedSp n F} {j b : Fin n} (hb : j < b)
    (hA : ∀ x, mat n F g x (Sum.inl j) = if x = Sum.inl j then 1 else 0)
    (hA' : ∀ y, mat n F g (Sum.inr j) y = if y = Sum.inr j then 1 else 0)
    (h : mat n F g * E F (.difference j b hb.ne) = E F (.difference j b hb.ne) * mat n F g) :
    ∀ x, x ≠ Sum.inl j → mat n F g x (Sum.inr b) = if x = Sum.inr b then 1 else 0 := by
  intro x hx
  have key := congrFun (congrFun h x) (Sum.inr j)
  rw [mulE_diff, Emul_diff] at key
  have h1 : (Sum.inr j : Fin n ⊕ Fin n) ≠ Sum.inl b := by simp
  have h2 : (Sum.inl j : Fin n ⊕ Fin n) ≠ Sum.inr j := by simp
  simp only [if_neg h1, if_pos rfl, hx, if_false, zero_sub, hA'] at key
  by_cases hxb : x = Sum.inr b
  · subst hxb; simpa using key
  · simpa [hxb] using key

theorem entries_of_comm_sum {g : StatedSp n F} {j b : Fin n} (hb : j < b)
    (hA : ∀ x, mat n F g x (Sum.inl j) = if x = Sum.inl j then 1 else 0)
    (hA' : ∀ y, mat n F g (Sum.inr j) y = if y = Sum.inr j then 1 else 0)
    (h : mat n F g * E F (.positiveSum j b hb) = E F (.positiveSum j b hb) * mat n F g) :
    ∀ x, x ≠ Sum.inl j → mat n F g x (Sum.inl b) = if x = Sum.inl b then 1 else 0 := by
  intro x hx
  have key := congrFun (congrFun h x) (Sum.inr j)
  rw [mulE_sum, Emul_sum] at key
  have h1 : (Sum.inr j : Fin n ⊕ Fin n) ≠ Sum.inr b := fun h => hb.ne (Sum.inr_injective h)
  simp only [if_neg h1, if_pos rfl, hx, if_false, zero_add, hA'] at key
  by_cases hxb : x = Sum.inl b
  · subst hxb; simpa using key
  · simpa [hxb] using key

theorem isSh_of_comm {g : StatedSp n F} (j : Fin n)
    (hlong : ∀ a, a ≤ j → mat n F g * E F (.positiveLong a) = E F (.positiveLong a) * mat n F g)
    (hdiff : ∀ b (hb : j < b), mat n F g * E F (.difference j b hb.ne) =
      E F (.difference j b hb.ne) * mat n F g)
    (hsum : ∀ b (hb : j < b), mat n F g * E F (.positiveSum j b hb) =
      E F (.positiveSum j b hb) * mat n F g) : IsSh j (mat n F g) := by
  have hcr := fun a (ha : a ≤ j) => col_row_of_comm_long (g := g) a (hlong a ha)
  intro x y hxy
  rcases y with y | y
  · by_cases hy : y ≤ j
    · rw [(hcr y hy).1 x]; simp [Matrix.one_apply]
    · have hjy : j < y := not_le.mp hy
      have hx : x ≠ Sum.inl j := by
        rintro rfl
        exact hxy (Or.inl ⟨le_rfl, by simpa [isA] using hy⟩)
      have hx' : ¬ isA j x := fun hx2 => hxy (Or.inl ⟨hx2, by simpa [isA] using hy⟩)
      have := entries_of_comm_sum hjy (hcr j le_rfl).1 (hcr j le_rfl).2 (hsum y hjy) x hx
      rw [this]; simp [Matrix.one_apply]
  · by_cases hy : y ≤ j
    · have hx : ¬ isA j x ∧ isA' j x := by
        by_contra hc
        apply hxy
        by_cases hx1 : isA j x
        · exact Or.inl ⟨hx1, by simp [isA]⟩
        · exact Or.inr ⟨hx1, fun h' => hc ⟨hx1, h'⟩, by simpa [isA'] using hy⟩
      rcases x with x | x
      · exact hx.2.elim
      · have hx2 : x ≤ j := hx.2
        rw [(hcr x hx2).2 (Sum.inr y)]; simp [Matrix.one_apply, eq_comm]
    · have hjy : j < y := not_le.mp hy
      have hx : x ≠ Sum.inl j := by
        rintro rfl
        exact hxy (Or.inl ⟨le_rfl, by simp [isA]⟩)
      have := entries_of_comm_diff hjy (hcr j le_rfl).1 (hcr j le_rfl).2 (hdiff y hjy) x hx
      rw [this]; simp [Matrix.one_apply]

end Shape

section Peeling

theorem mem_of_peel {K : Type*} [Group K] (R : Subgroup K) (P : K → Prop) (m : K → ℕ)
    (base : ∀ g, P g → m g = 0 → g ∈ R)
    (step : ∀ g, P g → 0 < m g → ∃ u ∈ R, P (g * u) ∧ m (g * u) < m g) :
    ∀ g, P g → g ∈ R := by
  intro g
  induction' hm : m g using Nat.strong_induction_on with N ih generalizing g
  intro hg
  by_cases h0 : m g = 0
  · exact base g hg h0
  · obtain ⟨u, hu, hP, hlt⟩ := step g hg (Nat.pos_of_ne_zero h0)
    have := ih (m (g * u)) (hm ▸ hlt) (g * u) rfl hP
    simpa using R.mul_mem this (R.inv_mem hu)

theorem card_lt_of_kill {α : Type*} [Fintype α] {F : Type*} [Zero F] (p : α → Prop) (f f' : α → F)
    [DecidablePred fun x => p x ∧ f' x ≠ 0] [DecidablePred fun x => p x ∧ f x ≠ 0]
    (x0 : α) (hx0 : p x0 ∧ f x0 ≠ 0) (h0 : f' x0 = 0)
    (hsame : ∀ x, p x → x ≠ x0 → f' x = f x) :
    (Finset.univ.filter fun x => p x ∧ f' x ≠ 0).card <
      (Finset.univ.filter fun x => p x ∧ f x ≠ 0).card := by
  apply Finset.card_lt_card
  refine ⟨fun x hx => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    refine ⟨hx.1, ?_⟩
    by_cases hxx : x = x0
    · subst hxx; exact absurd h0 hx.2
    · rw [← hsame x hx.1 hxx]; exact hx.2
  · have := hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx0⟩)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this.2 h0

end Peeling

section Stage3

variable {n : ℕ} {F : Type} [Field F] {j : Fin n}

theorem mat_mul_elt (g : StatedSp n F) (r : RootSubgroupIndex n) (c : F) (x y : Fin n ⊕ Fin n) :
    mat n F (g * elt r c) x y = mat n F g x y + c * (mat n F g * E F r) x y := by
  rw [map_mul, mat_elt, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
  simp

theorem IsSh0.col_inl {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} (h : IsSh0 j M) (x : Fin n ⊕ Fin n)
    (i : Fin n) : M x (Sum.inl i) = if x = Sum.inl i then 1 else 0 := by
  rw [h x _ (fun ⟨_, hy⟩ => hy)]; simp [Matrix.one_apply]

theorem IsSh0.symm_of_sp {g : StatedSp n F} (h : IsSh0 j (mat n F g)) (a c : Fin n) :
    mat n F g (Sum.inl a) (Sum.inr c) = mat n F g (Sum.inl c) (Sum.inr a) := by
  have key := gram_form (mat n F g) (Sum.inl a) (Sum.inl c)
  rw [mat_mul_gram_mul_transpose g] at key
  have hJ : Jmat n F (Sum.inl a) (Sum.inl c) = 0 := by
    simp [Jmat, CFSG.ClassicalInvolution.Models.SymplecticPairs.gram]
  rw [hJ] at key
  simp only [h.col_inl] at key
  simp [Finset.sum_sub_distrib] at key
  exact (sub_eq_zero.mp key.symm).symm

theorem elt_long_mem {a : Fin n} (ha : a ≤ j) (c : F) :
    elt (.positiveLong a) c ∈ CFSG.AGLEmbedding.LieOut.radical (rootDatum n F) j := by
  apply elt_mem_radical
  rw [cumE_pl, if_pos ha]; norm_num

theorem elt_sum_mem {a b : Fin n} (hab : a < b) (ha : a ≤ j) (c : F) :
    elt (.positiveSum a b hab) c ∈ CFSG.AGLEmbedding.LieOut.radical (rootDatum n F) j := by
  apply elt_mem_radical
  rw [cumE_ps, if_pos ha]
  split_ifs <;> norm_num

theorem elt_diff_mem {a b : Fin n} (hab : a ≠ b) (ha : a ≤ j) (hb : j < b) (c : F) :
    elt (.difference a b hab) c ∈ CFSG.AGLEmbedding.LieOut.radical (rootDatum n F) j := by
  apply elt_mem_radical
  rw [cumE_df, if_pos ha, if_neg (not_le.mpr hb)]; norm_num

open Classical in
noncomputable def cntY (j : Fin n) (g : StatedSp n F) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n =>
    (p.1 ≤ p.2 ∧ p.2 ≤ j) ∧ mat n F g (Sum.inl p.1) (Sum.inr p.2) ≠ 0).card

theorem step3 (g : StatedSp n F) (hg : IsSh0 j (mat n F g)) (h : 0 < cntY j g) :
    ∃ u ∈ CFSG.AGLEmbedding.LieOut.radical (rootDatum n F) j, IsSh0 j (mat n F (g * u)) ∧ cntY j (g * u) < cntY j g := by
  classical
  obtain ⟨⟨a, c⟩, hac⟩ := Finset.card_pos.mp h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hac
  obtain ⟨⟨hac1, hcj⟩, hne⟩ := hac
  have haj : a ≤ j := hac1.trans hcj
  rcases hac1.eq_or_lt with heq | hlt
  · subst heq
    refine ⟨elt (.positiveLong a) (-mat n F g (Sum.inl a) (Sum.inr a)), elt_long_mem haj _, ?_, ?_⟩
    · intro x y hxy
      rw [mat_mul_elt, mulE_long, hg.col_inl, hg x y hxy]
      have : ¬ (y = Sum.inr a ∧ x = Sum.inl a) := fun ⟨h1, h2⟩ => hxy ⟨by simp [h2, isA, haj], by simp [h1, isA', haj]⟩
      by_cases h1 : y = Sum.inr a
      · have h2 : x ≠ Sum.inl a := fun h2 => this ⟨h1, h2⟩
        simp [h1, h2]
      · simp [h1]
    · unfold cntY
      apply card_lt_of_kill _ (fun x : Fin n × Fin n => mat n F g (Sum.inl x.1) (Sum.inr x.2))
        (fun x : Fin n × Fin n => mat n F (g * elt (.positiveLong a) (-mat n F g (Sum.inl a) (Sum.inr a))) (Sum.inl x.1) (Sum.inr x.2)) (a, a)
      · exact ⟨⟨le_rfl, haj⟩, hne⟩
      · simp [mat_mul_elt, mulE_long, hg.col_inl]
      · rintro ⟨a', c'⟩ ⟨h1, h2⟩ hne'
        simp only [mat_mul_elt, mulE_long, hg.col_inl]
        by_cases hc : c' = a
        · have : a' ≠ a := fun e => hne' (by simp [e, hc])
          simp [hc, this]
        · simp [hc]
  · refine ⟨elt (.positiveSum a c hlt) (-mat n F g (Sum.inl a) (Sum.inr c)), elt_sum_mem hlt haj _, ?_, ?_⟩
    · intro x y hxy
      rw [mat_mul_elt, mulE_sum, hg.col_inl, hg.col_inl, hg x y hxy]
      have h1 : ¬ (y = Sum.inr c ∧ x = Sum.inl a) := fun ⟨h1, h2⟩ =>
        hxy ⟨by simp [h2, isA, haj], by simp [h1, isA', hcj]⟩
      have h2 : ¬ (y = Sum.inr a ∧ x = Sum.inl c) := fun ⟨h1, h2⟩ =>
        hxy ⟨by simp [h2, isA, hcj], by simp [h1, isA', haj]⟩
      have e1 : (if y = Sum.inr c then (if x = Sum.inl a then (1 : F) else 0) else 0) = 0 := by
        by_cases hy : y = Sum.inr c
        · have : x ≠ Sum.inl a := fun hx => h1 ⟨hy, hx⟩
          simp [hy, this]
        · simp [hy]
      have e2 : (if y = Sum.inr a then (if x = Sum.inl c then (1 : F) else 0) else 0) = 0 := by
        by_cases hy : y = Sum.inr a
        · have : x ≠ Sum.inl c := fun hx => h2 ⟨hy, hx⟩
          simp [hy, this]
        · simp [hy]
      rw [e1, e2]; simp
    · unfold cntY
      apply card_lt_of_kill _ (fun x : Fin n × Fin n => mat n F g (Sum.inl x.1) (Sum.inr x.2))
        (fun x : Fin n × Fin n => mat n F (g * elt (.positiveSum a c hlt) (-mat n F g (Sum.inl a) (Sum.inr c))) (Sum.inl x.1) (Sum.inr x.2)) (a, c)
      · exact ⟨⟨hlt.le, hcj⟩, hne⟩
      · have : (Sum.inr c : Fin n ⊕ Fin n) ≠ Sum.inr a := fun h => hlt.ne' (Sum.inr_injective h)
        simp [mat_mul_elt, mulE_sum, hg.col_inl, this]
      · rintro ⟨a', c'⟩ ⟨h1, h2⟩ hne'
        simp only [mat_mul_elt, mulE_sum, hg.col_inl]
        have e1 : (if c' = c then (if a' = a then (1 : F) else 0) else 0) = 0 := by
          by_cases hc : c' = c
          · have : a' ≠ a := fun e => hne' (by simp [e, hc])
            simp [hc, this]
          · simp [hc]
        have e2 : (if c' = a then (if a' = c then (1 : F) else 0) else 0) = 0 := by
          by_cases hc : c' = a
          · have : a' ≠ c := fun e => by
              have := h1; rw [e, hc] at this; exact absurd this (not_le.mpr hlt)
            simp [hc, this]
          · simp [hc]
        simp [e1, e2]

theorem mat_mul_elt_eq (g : StatedSp n F) (r : RootSubgroupIndex n) (c : F) :
    mat n F (g * elt r c) = mat n F g * (1 + c • E F r) := by
  rw [map_mul, mat_elt]

theorem sh0_mem_radical : ∀ g : StatedSp n F, IsSh0 j (mat n F g) →
    g ∈ CFSG.AGLEmbedding.LieOut.radical (rootDatum n F) j := by
  refine mem_of_peel _ (fun g => IsSh0 j (mat n F g)) (cntY j) ?_ ?_
  · intro g hg h0
    have hz : ∀ a c : Fin n, a ≤ c → c ≤ j → mat n F g (Sum.inl a) (Sum.inr c) = 0 := by
      intro a c h1 h2
      by_contra hne
      classical
      unfold cntY at h0
      have h0' := Finset.card_eq_zero.mp h0
      have hmem : (a, c) ∈ (Finset.univ.filter fun p : Fin n × Fin n =>
          (p.1 ≤ p.2 ∧ p.2 ≤ j) ∧ mat n F g (Sum.inl p.1) (Sum.inr p.2) ≠ 0) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨h1, h2⟩, hne⟩
      convert hmem
      · rw [h0']; simp
    have h1 : mat n F g = 1 := by
      ext x y
      by_cases hxy : isA j x ∧ isA' j y
      · obtain ⟨hx, hy⟩ := hxy
        rcases x with a | a
        · rcases y with c | c
          · exact hy.elim
          · have ha : a ≤ j := hx
            have hc : c ≤ j := hy
            rw [Matrix.one_apply_ne (by simp)]
            rcases le_total a c with h | h
            · exact hz a c h hc
            · rw [hg.symm_of_sp]; exact hz c a h ha
        · exact hx.elim
      · exact hg x y hxy
    have : g = 1 := mat_injective (by rw [h1, map_one])
    rw [this]; exact one_mem _
  · intro g hg h
    exact step3 g hg h

open Classical in
noncomputable def cntX2 (j : Fin n) (g : StatedSp n F) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n =>
    (p.1 ≤ j ∧ j < p.2) ∧ mat n F g (Sum.inl p.1) (Sum.inr p.2) ≠ 0).card

open Classical in
noncomputable def cntX1 (j : Fin n) (g : StatedSp n F) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n =>
    (p.1 ≤ j ∧ j < p.2) ∧ mat n F g (Sum.inl p.1) (Sum.inl p.2) ≠ 0).card

theorem card_zero_entries {p : Fin n × Fin n → Prop} {f : Fin n × Fin n → F}
    {inst : DecidablePred fun x => p x ∧ f x ≠ 0}
    (h0 : (Finset.univ.filter fun x => p x ∧ f x ≠ 0).card = 0) (x : Fin n × Fin n) (hx : p x) :
    f x = 0 := by
  by_contra hne
  have h0' := Finset.card_eq_zero.mp h0
  have hmem : x ∈ (Finset.univ.filter fun x => p x ∧ f x ≠ 0) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hx, hne⟩
  rw [h0'] at hmem
  simp at hmem

theorem step2 (g : StatedSp n F) (hg : IsSh j (mat n F g))
    (hX1 : ∀ a b, a ≤ j → j < b → mat n F g (Sum.inl a) (Sum.inl b) = 0) (h : 0 < cntX2 j g) :
    ∃ u ∈ CFSG.AGLEmbedding.LieOut.radical (rootDatum n F) j,
      (IsSh j (mat n F (g * u)) ∧ ∀ a b, a ≤ j → j < b → mat n F (g * u) (Sum.inl a) (Sum.inl b) = 0) ∧
        cntX2 j (g * u) < cntX2 j g := by
  classical
  obtain ⟨⟨a, b⟩, hab⟩ := Finset.card_pos.mp h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab
  obtain ⟨⟨haj, hjb⟩, hne⟩ := hab
  have hlt : a < b := lt_of_le_of_lt haj hjb
  refine ⟨elt (.positiveSum a b hlt) (-mat n F g (Sum.inl a) (Sum.inr b)), elt_sum_mem hlt haj _, ⟨?_, ?_⟩, ?_⟩
  · rw [mat_mul_elt_eq]; exact sh_mul_sum hg hlt haj hjb _
  · intro a' b' _ _
    rw [mat_mul_elt, mulE_sum, hX1 a' b' ‹_› ‹_›]; simp
  · unfold cntX2
    apply card_lt_of_kill _ (fun x : Fin n × Fin n => mat n F g (Sum.inl x.1) (Sum.inr x.2))
      (fun x : Fin n × Fin n => mat n F (g * elt (.positiveSum a b hlt) (-mat n F g (Sum.inl a) (Sum.inr b))) (Sum.inl x.1) (Sum.inr x.2)) (a, b)
    · exact ⟨⟨haj, hjb⟩, hne⟩
    · have : (Sum.inr b : Fin n ⊕ Fin n) ≠ Sum.inr a := fun h => hlt.ne' (Sum.inr_injective h)
      simp [mat_mul_elt, mulE_sum, hg.col_A haj, this, Matrix.one_apply]
    · rintro ⟨a', b'⟩ ⟨h1, h2⟩ hne'
      simp only [mat_mul_elt, mulE_sum, hg.col_A haj]
      have e1 : (if Sum.inr b' = (Sum.inr b : Fin n ⊕ Fin n) then (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (Sum.inl a') (Sum.inl a) else 0) = 0 := by
        by_cases hc : b' = b
        · have : a' ≠ a := fun e => hne' (by simp [e, hc])
          simp [hc, this, Matrix.one_apply]
        · simp [hc]
      have e2 : (if Sum.inr b' = (Sum.inr a : Fin n ⊕ Fin n) then mat n F g (Sum.inl a') (Sum.inl b) else 0) = 0 := by
        have : b' ≠ a := fun e => by rw [e] at h2; exact absurd haj (not_le.mpr h2)
        simp [this]
      rw [e1, e2]; simp

theorem sh2_mem_radical : ∀ g : StatedSp n F, IsSh j (mat n F g) →
    (∀ a b, a ≤ j → j < b → mat n F g (Sum.inl a) (Sum.inl b) = 0) →
    g ∈ CFSG.AGLEmbedding.LieOut.radical (rootDatum n F) j := by
  have := mem_of_peel (CFSG.AGLEmbedding.LieOut.radical (rootDatum n F) j)
    (fun g : StatedSp n F => IsSh j (mat n F g) ∧ ∀ a b, a ≤ j → j < b → mat n F g (Sum.inl a) (Sum.inl b) = 0)
    (cntX2 j) ?_ ?_
  · exact fun g h1 h2 => this g ⟨h1, h2⟩
  · rintro g ⟨hg, hX1⟩ h0
    unfold cntX2 at h0
    exact sh0_mem_radical g (sh0_of_zero hg hX1 (fun a b ha hb =>
      card_zero_entries (p := fun x : Fin n × Fin n => x.1 ≤ j ∧ j < x.2)
        (f := fun x : Fin n × Fin n => mat n F g (Sum.inl x.1) (Sum.inr x.2)) h0 (a, b) ⟨ha, hb⟩))
  · rintro g ⟨hg, hX1⟩ h
    obtain ⟨u, hu, hP, hlt⟩ := step2 g hg hX1 h
    exact ⟨u, hu, hP, hlt⟩

theorem step1 (g : StatedSp n F) (hg : IsSh j (mat n F g)) (h : 0 < cntX1 j g) :
    ∃ u ∈ CFSG.AGLEmbedding.LieOut.radical (rootDatum n F) j,
      IsSh j (mat n F (g * u)) ∧ cntX1 j (g * u) < cntX1 j g := by
  classical
  obtain ⟨⟨a, b⟩, hab⟩ := Finset.card_pos.mp h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab
  obtain ⟨⟨haj, hjb⟩, hne⟩ := hab
  have hlt : a ≠ b := (lt_of_le_of_lt haj hjb).ne
  refine ⟨elt (.difference a b hlt) (-mat n F g (Sum.inl a) (Sum.inl b)), elt_diff_mem hlt haj hjb _, ?_, ?_⟩
  · rw [mat_mul_elt_eq]; exact sh_mul_diff hg hlt haj hjb _
  · unfold cntX1
    apply card_lt_of_kill _ (fun x : Fin n × Fin n => mat n F g (Sum.inl x.1) (Sum.inl x.2))
      (fun x : Fin n × Fin n => mat n F (g * elt (.difference a b hlt) (-mat n F g (Sum.inl a) (Sum.inl b))) (Sum.inl x.1) (Sum.inl x.2)) (a, b)
    · exact ⟨⟨haj, hjb⟩, hne⟩
    · have : (Sum.inl b : Fin n ⊕ Fin n) ≠ Sum.inr a := by simp
      simp [mat_mul_elt, mulE_diff, hg.col_A haj, this, Matrix.one_apply]
    · rintro ⟨a', b'⟩ ⟨h1, h2⟩ hne'
      simp only [mat_mul_elt, mulE_diff, hg.col_A haj]
      have e1 : (if Sum.inl b' = (Sum.inl b : Fin n ⊕ Fin n) then (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (Sum.inl a') (Sum.inl a) else 0) = 0 := by
        by_cases hc : b' = b
        · have : a' ≠ a := fun e => hne' (by simp [e, hc])
          simp [hc, this, Matrix.one_apply]
        · simp [hc]
      have e2 : (if Sum.inl b' = (Sum.inr a : Fin n ⊕ Fin n) then mat n F g (Sum.inl a') (Sum.inr b) else 0) = 0 := by
        simp
      rw [e1, e2]; simp

theorem sh_mem_radical : ∀ g : StatedSp n F, IsSh j (mat n F g) →
    g ∈ CFSG.AGLEmbedding.LieOut.radical (rootDatum n F) j := by
  refine mem_of_peel _ (fun g => IsSh j (mat n F g)) (cntX1 j) ?_ ?_
  · intro g hg h0
    unfold cntX1 at h0
    exact sh2_mem_radical g hg (fun a b ha hb =>
      card_zero_entries (p := fun x : Fin n × Fin n => x.1 ≤ j ∧ j < x.2)
        (f := fun x : Fin n × Fin n => mat n F g (Sum.inl x.1) (Sum.inl x.2)) h0 (a, b) ⟨ha, hb⟩)
  · intro g hg h
    exact step1 g hg h

end Stage3

section Final

variable {n : ℕ} {F : Type} [Field F] [CharP F 2]

theorem centOb_sp {I : Set (Fin n)} (hI : I ≠ Set.univ) : CentOb (rootDatum n F) I := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : Fin n, j ∉ I := by
    by_contra h
    push Not at h
    exact hI (Set.eq_univ_of_forall h)
  intro k hk
  have hkr : ∀ u ∈ CFSG.AGLEmbedding.LieOut.radical (rootDatum n F) j, k * u = u * k :=
    fun u hu => hk u (radical_le_leviRad hj hu)
  have hsh : IsSh j (mat n F k) := by
    refine isSh_of_comm j (fun a ha => comm_mat_of_comm _ (hkr _ (elt_long_mem ha 1))) ?_ ?_
    · intro b hb
      exact comm_mat_of_comm _ (hkr _ (elt_diff_mem hb.ne le_rfl hb 1))
    · intro b hb
      exact comm_mat_of_comm _ (hkr _ (elt_sum_mem hb le_rfl 1))
  exact Subgroup.mem_sup_left (radical_le_leviRad hj (sh_mem_radical k hsh))

theorem spCentOb : SpCentOb := fun _ _ _ _ _ _ _ _ I hI => centOb_sp hI

end Final

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
