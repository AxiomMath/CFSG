module

public import Mathlib

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

open scoped MatrixGroups

theorem fin2_cases (a : Fin 2) : a = 0 ∨ a = 1 := by fin_cases a <;> simp

section Rep

variable {G k V : Type*} [Monoid G] [Field k] [AddCommGroup V] [Module k V]

theorem isIrreducible_iff (ρ : Representation k G V) : ρ.IsIrreducible ↔ Nontrivial V ∧
    ∀ U : Submodule k V, (∀ g, ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
  constructor
  · intro h
    refine ⟨?_, fun U hU => ?_⟩
    · by_contra hv
      rw [not_nontrivial_iff_subsingleton] at hv
      exact bot_ne_top (α := Subrepresentation ρ)
        (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
    · rcases h.eq_bot_or_eq_top (⟨U, fun g _ hv => hU g _ hv⟩ : Subrepresentation ρ) with h1 | h1
      · exact Or.inl (congrArg Subrepresentation.toSubmodule h1)
      · exact Or.inr (congrArg Subrepresentation.toSubmodule h1)
  · rintro ⟨hv, h⟩
    have hnt : Nontrivial (Subrepresentation ρ) := by
      refine ⟨⊥, ⊤, fun h' => ?_⟩
      obtain ⟨x, y, hxy⟩ := hv
      have h1 : (⊥ : Subrepresentation ρ).toSubmodule = (⊤ : Subrepresentation ρ).toSubmodule :=
        congrArg Subrepresentation.toSubmodule h'
      have h2 : (⊥ : Submodule k V) = ⊤ := h1
      have h3 : x - y ∈ (⊥ : Submodule k V) := h2 ▸ Submodule.mem_top
      exact hxy (sub_eq_zero.mp ((Submodule.mem_bot k).mp h3))
    refine ⟨fun Z => ?_⟩
    rcases h Z.toSubmodule (fun g u hu => Z.apply_mem_toSubmodule g hu) with h1 | h1
    · exact Or.inl (Subrepresentation.toSubmodule_injective h1)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h1)

end Rep

section Fixed

theorem add_self_eq_zero_of_charTwo (k : Type*) {V : Type*} [Field k] [CharP k 2] [AddCommGroup V]
    [Module k V] (w : V) : w + w = 0 := by
  have h2 : (2 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 2
  rw [← two_smul k w, h2, zero_smul]

theorem neg_eq_self_of_charTwo (k : Type*) {V : Type*} [Field k] [CharP k 2] [AddCommGroup V]
    [Module k V] (w : V) : -w = w :=
  neg_eq_of_add_eq_zero_right (add_self_eq_zero_of_charTwo k w)

variable {G k V : Type*} [Group G] [Field k] [CharP k 2] [AddCommGroup V] [Module k V]

theorem exists_fixed_of_commuting_involutions (ρ : Representation k G V) (s : Finset G)
    (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) (hinv : ∀ x ∈ s, x * x = 1)
    (Z : Submodule k V) (hZ : ∀ x ∈ s, ∀ v ∈ Z, ρ x v ∈ Z) (hZne : Z ≠ ⊥) :
    ∃ v ∈ Z, v ≠ 0 ∧ ∀ x ∈ s, ρ x v = v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZne
    exact ⟨v, hv, hv0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨v, hvZ, hv0, hvfix⟩ := ih (fun x hx y hy => hcomm x (Finset.mem_insert_of_mem hx) y
      (Finset.mem_insert_of_mem hy)) (fun x hx => hinv x (Finset.mem_insert_of_mem hx))
      (fun x hx => hZ x (Finset.mem_insert_of_mem hx))
    have haa : ρ a (ρ a v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, hinv a (Finset.mem_insert_self a s), map_one]
      rfl
    by_cases hw : ρ a v - v = 0
    · refine ⟨v, hvZ, hv0, fun x hx => ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact sub_eq_zero.mp hw
      · exact hvfix x hx
    · refine ⟨ρ a v - v, ?_, hw, fun x hx => ?_⟩
      · exact Z.sub_mem (hZ a (Finset.mem_insert_self a s) v hvZ) hvZ
      · rcases Finset.mem_insert.mp hx with rfl | hx
        · rw [map_sub, haa]
          have := neg_eq_self_of_charTwo k (ρ x v - v)
          rw [neg_sub] at this
          exact this
        · rw [map_sub, hvfix x hx]
          have hc : ρ x (ρ a v) = ρ a (ρ x v) := by
            rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
              hcomm x (Finset.mem_insert_of_mem hx) a (Finset.mem_insert_self a s)]
          rw [hc, hvfix x hx]

end Fixed

open Polynomial in
theorem eq_zero_of_sum_pow_eq_zero {F k ι : Type*} [Field F] [Fintype F] [Field k] [Algebra F k]
    [Fintype ι] (a : ι → ℕ) (ha : Function.Injective a) (hlt : ∀ i, a i < Fintype.card F)
    (c : ι → k) (h : ∀ t : F, ∑ i, c i * (algebraMap F k t) ^ a i = 0) : ∀ i, c i = 0 := by
  classical
  set p : k[X] := ∑ i, C (c i) * X ^ a i with hp
  have hdeg : p.natDegree < Fintype.card F := by
    refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _
      (n := Finset.univ.sup a) ?_) ?_
    · intro i _
      exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
        (Finset.le_sup (f := a) (Finset.mem_univ i))
    · by_cases hι : Nonempty ι
      · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty a
        rw [hi]; exact hlt i
      · have : IsEmpty ι := not_nonempty_iff.mp hι
        simp
        exact Fintype.card_pos
  have hzero : p = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
      (f := fun t : F => algebraMap F k t) (algebraMap F k).injective (fun t => ?_) hdeg
    simp only [hp, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    exact h t
  intro i
  have := congrArg (fun q : Polynomial k => q.coeff (a i)) hzero
  simp only [hp, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
  rw [Finset.sum_eq_single i] at this
  · simpa using this
  · intro j _ hj
    simp [ha.ne hj.symm]
  · simp

section Twist

variable {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [CharP k 2]

@[expose] def twistMat (m : ℕ) (g : SL(2, F)) : Matrix (Fin 2) (Fin 2) k :=
  (iterateFrobenius k 2 m).mapMatrix ((algebraMap F k).mapMatrix (g : Matrix (Fin 2) (Fin 2) F))

variable {k}

theorem twistMat_apply (m : ℕ) (g : SL(2, F)) (i j : Fin 2) :
    twistMat k m g i j = (algebraMap F k (g i j)) ^ (2 ^ m) := by
  simp [twistMat, iterateFrobenius_def]

theorem twistMat_mul (m : ℕ) (g h : SL(2, F)) :
    twistMat k m (g * h) = twistMat k m g * twistMat k m h := by
  simp [twistMat, Matrix.SpecialLinearGroup.coe_mul, map_mul]

theorem twistMat_one (m : ℕ) : twistMat k m (1 : SL(2, F)) = 1 := by
  simp [twistMat]

theorem twistMat_add_card [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n) (m : ℕ)
    (g : SL(2, F)) : twistMat k (m + n) g = twistMat k m g := by
  ext i j
  rw [twistMat_apply, twistMat_apply, pow_add, mul_comm, pow_mul, ← map_pow, ← hF,
    FiniteField.pow_card]

theorem twistMat_mod [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n) (m : ℕ) (g : SL(2, F)) :
    twistMat k (m % n) g = twistMat k m g := by
  have h : ∀ q : ℕ, twistMat k (m % n + n * q) g = twistMat k (m % n) g := by
    intro q
    induction q with
    | zero => simp
    | succ q ih => rw [Nat.mul_succ, ← add_assoc, twistMat_add_card hF, ih]
  rw [← h (m / n), Nat.mod_add_div]

theorem twistMat_det (m : ℕ) (g : SL(2, F)) :
    twistMat k m g 0 0 * twistMat k m g 1 1 + twistMat k m g 0 1 * twistMat k m g 1 0 = 1 := by
  have h : (g : Matrix (Fin 2) (Fin 2) F).det = 1 := g.2
  rw [Matrix.det_fin_two] at h
  simp only [twistMat_apply]
  have h2 : (algebraMap F k (g 0 0)) ^ (2 ^ m) * (algebraMap F k (g 1 1)) ^ (2 ^ m) -
      (algebraMap F k (g 0 1)) ^ (2 ^ m) * (algebraMap F k (g 1 0)) ^ (2 ^ m) = 1 := by
    have := congrArg (fun x : F => (algebraMap F k x) ^ (2 ^ m)) h
    simpa [← mul_pow, sub_pow_char_pow, map_sub, map_mul] using this
  have h3 : ∀ x y : k, x - y = x + y := fun x y => by
    rw [sub_eq_add_neg, CharTwo.neg_eq]
  rw [h3] at h2
  exact h2

@[expose] def uElt (t : F) : SL(2, F) := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def lElt (t : F) : SL(2, F) := ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def dElt (z : Fˣ) : SL(2, F) :=
  ⟨!![(z : F), 0; 0, ((z⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two]⟩

theorem uElt_add (s t : F) : uElt (s + t) = uElt s * uElt t := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [uElt, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem uElt_zero : uElt (0 : F) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [uElt]

theorem twistMat_uElt (m : ℕ) (t : F) :
    twistMat k m (uElt t) = !![1, (algebraMap F k t) ^ (2 ^ m); 0, 1] := by
  ext i j
  rw [twistMat_apply]
  fin_cases i <;> fin_cases j <;> simp [uElt]

theorem twistMat_lElt (m : ℕ) (t : F) :
    twistMat k m (lElt t) = !![1, 0; (algebraMap F k t) ^ (2 ^ m), 1] := by
  ext i j
  rw [twistMat_apply]
  fin_cases i <;> fin_cases j <;> simp [lElt]

theorem twistMat_dElt (m : ℕ) (z : Fˣ) :
    twistMat k m (dElt z) =
      !![(algebraMap F k z) ^ (2 ^ m), 0; 0, (algebraMap F k ((z⁻¹ : Fˣ) : F)) ^ (2 ^ m)] := by
  ext i j
  rw [twistMat_apply]
  fin_cases i <;> fin_cases j <;> simp [dElt]

end Twist

section Tensor

variable {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [CharP k 2]
variable {ι : Type*} [Fintype ι]

@[expose] def tmatE (e : ι → ℕ) (g : SL(2, F)) : Matrix (ι → Fin 2) (ι → Fin 2) k :=
  fun x' x => ∏ i, twistMat k (e i) g (x' i) (x i)

variable {k}

theorem tmatE_one (e : ι → ℕ) : tmatE k e (1 : SL(2, F)) = 1 := by
  ext x' x
  simp only [tmatE, twistMat_one, Matrix.one_apply]
  by_cases h : x' = x
  · subst h; simp
  · obtain ⟨i, hi⟩ : ∃ i, x' i ≠ x i := by
      by_contra hc
      exact h (funext fun i => by by_contra hne; exact hc ⟨i, hne⟩)
    simp only [h, ↓reduceIte]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

variable [DecidableEq ι]

theorem tmatE_mul (e : ι → ℕ) (g h : SL(2, F)) :
    tmatE k e (g * h) = tmatE k e g * tmatE k e h := by
  ext x'' x
  simp only [tmatE, Matrix.mul_apply, twistMat_mul]
  have := Finset.prod_univ_sum (fun _ => (Finset.univ : Finset (Fin 2)))
    (fun i b => twistMat k (e i) g (x'' i) b * twistMat k (e i) h b (x i))
  simp only [Fintype.piFinset_univ] at this
  rw [this]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.prod_mul_distrib]

variable (F k)

@[expose] def tensorRep (e : ι → ℕ) : Representation k SL(2, F) ((ι → Fin 2) → k) where
  toFun g := Matrix.toLin' (tmatE k e g)
  map_one' := by rw [tmatE_one]; exact Matrix.toLin'_one
  map_mul' g h := by rw [tmatE_mul, Matrix.toLin'_mul]; rfl

variable {F k}

theorem tensorRep_apply (e : ι → ℕ) (g : SL(2, F)) (v : (ι → Fin 2) → k) (x' : ι → Fin 2) :
    tensorRep F k e g v x' = ∑ x, tmatE k e g x' x * v x := by
  simp [tensorRep, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

omit [DecidableEq ι] in
@[expose] def aexp (e : ι → ℕ) (y : ι → Fin 2) : ℕ := ∑ i, (y i : ℕ) * 2 ^ e i

omit [DecidableEq ι] in
theorem tmatE_uElt_base_row (e : ι → ℕ) (t : F) (y : ι → Fin 2) :
    tmatE k e (uElt t) (fun _ => 0) y = (algebraMap F k t) ^ aexp e y := by
  unfold tmatE aexp
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [twistMat_uElt]
  rcases fin2_cases (y i) with h | h <;> simp [h]

omit [DecidableEq ι] in
theorem tmatE_lElt_base_col (e : ι → ℕ) (t : F) (y : ι → Fin 2) :
    tmatE k e (lElt t) y (fun _ => 0) = (algebraMap F k t) ^ aexp e y := by
  unfold tmatE aexp
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [twistMat_lElt]
  rcases fin2_cases (y i) with h | h <;> simp [h]

omit [DecidableEq ι] in
theorem tmatE_uElt_base_col (e : ι → ℕ) (t : F) (y : ι → Fin 2) :
    tmatE k e (uElt t) y (fun _ => 0) = if y = (fun _ => 0) then 1 else 0 := by
  unfold tmatE
  by_cases hy : y = fun _ => 0
  · subst hy; simp [twistMat_uElt]
  · obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
      by_contra hc
      exact hy (funext fun i => by by_contra hne; exact hc ⟨i, hne⟩)
    simp only [hy, ↓reduceIte]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rcases fin2_cases (y i) with h | h
    · exact absurd h hi
    · simp [twistMat_uElt, h]

omit [DecidableEq ι] in
theorem tmatE_dElt_base_col (e : ι → ℕ) (z : Fˣ) (y : ι → Fin 2) :
    tmatE k e (dElt z) y (fun _ => 0) =
      if y = (fun _ => 0) then (algebraMap F k z) ^ (∑ i, 2 ^ e i) else 0 := by
  unfold tmatE
  by_cases hy : y = fun _ => 0
  · subst hy
    simp only [↓reduceIte]
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [twistMat_dElt]
  · obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
      by_contra hc
      exact hy (funext fun i => by by_contra hne; exact hc ⟨i, hne⟩)
    simp only [hy, ↓reduceIte]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rcases fin2_cases (y i) with h | h
    · exact absurd h hi
    · simp [twistMat_dElt, h]

end Tensor

section Aexp

variable {ι : Type*} [Fintype ι]

theorem aexp_eq_sum_support (e : ι → ℕ) (he : Function.Injective e) (y : ι → Fin 2) :
    aexp e y = ∑ j ∈ (Finset.univ.filter (fun i => y i = 1)).image e, 2 ^ j := by
  rw [Finset.sum_image (fun a _ b _ h => he h), Finset.sum_filter]
  unfold aexp
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases fin2_cases (y i) with h | h <;> simp [h]

theorem aexp_injective (e : ι → ℕ) (he : Function.Injective e) : Function.Injective (aexp e) := by
  intro y y' h
  rw [aexp_eq_sum_support e he, aexp_eq_sum_support e he] at h
  have h2 := Finset.equivBitIndices.symm.injective
    (a₁ := (Finset.univ.filter (fun i => y i = 1)).image e)
    (a₂ := (Finset.univ.filter (fun i => y' i = 1)).image e) (by simpa using h)
  funext i
  have h3 : e i ∈ (Finset.univ.filter (fun i => y i = 1)).image e ↔
      e i ∈ (Finset.univ.filter (fun i => y' i = 1)).image e := by rw [h2]
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at h3
  have h4 : y i = 1 ↔ y' i = 1 := by
    constructor
    · intro hy; obtain ⟨j, hj, hje⟩ := h3.mp ⟨i, hy, rfl⟩; rwa [he hje] at hj
    · intro hy; obtain ⟨j, hj, hje⟩ := h3.mpr ⟨i, hy, rfl⟩; rwa [he hje] at hj
  rcases fin2_cases (y i) with h5 | h5 <;> rcases fin2_cases (y' i) with h6 | h6 <;> simp_all

theorem aexp_lt (e : ι → ℕ) (he : Function.Injective e) {n : ℕ} (hn : ∀ i, e i < n)
    (y : ι → Fin 2) : aexp e y < 2 ^ n := by
  rw [aexp_eq_sum_support e he]
  exact Nat.geomSum_lt le_rfl (by simpa using fun i _ => hn i)

end Aexp

section BaseVec

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι]

@[expose] def baseVec : (ι → Fin 2) → k := Pi.single (fun _ => 0) 1

theorem baseVec_apply (y : ι → Fin 2) :
    (baseVec y : k) = if y = (fun _ => 0) then 1 else 0 := by
  unfold baseVec
  by_cases h : y = fun _ => 0
  · subst h; simp
  · simp [h]

end BaseVec

section Basics

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k] [CharP k 2]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem tensorRep_uElt_baseVec (e : ι → ℕ) (t : F) :
    tensorRep F k e (uElt t) baseVec = baseVec := by
  funext y
  rw [tensorRep_apply, Finset.sum_eq_single (fun _ => 0)]
  · rw [baseVec_apply, ite_eq_left rfl, mul_one, tmatE_uElt_base_col, baseVec_apply]
  · intro x _ hx
    rw [baseVec_apply, ite_eq_right hx, mul_zero]
  · simp

theorem tensorRep_lElt_baseVec (e : ι → ℕ) (t : F) (y : ι → Fin 2) :
    tensorRep F k e (lElt t) baseVec y = (algebraMap F k t) ^ aexp e y := by
  rw [tensorRep_apply, Finset.sum_eq_single (fun _ => 0)]
  · rw [baseVec_apply, ite_eq_left rfl, mul_one, tmatE_lElt_base_col]
  · intro x _ hx
    rw [baseVec_apply, ite_eq_right hx, mul_zero]
  · simp

theorem tensorRep_dElt_baseVec (e : ι → ℕ) (z : Fˣ) :
    tensorRep F k e (dElt z) baseVec = (algebraMap F k z) ^ (∑ i, 2 ^ e i) • baseVec := by
  funext y
  rw [tensorRep_apply, Finset.sum_eq_single (fun _ => 0)]
  · rw [baseVec_apply, ite_eq_left rfl, mul_one, tmatE_dElt_base_col, Pi.smul_apply, baseVec_apply]
    by_cases hy : y = fun _ => 0 <;> simp [hy]
  · intro x _ hx
    rw [baseVec_apply, ite_eq_right hx, mul_zero]
  · simp

end Basics

section Irreducible

variable {F : Type*} [Field F] [Fintype F] {k : Type*} [Field k] [Algebra F k] [CharP k 2]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem fixed_of_uElt {n : ℕ} (hF : Fintype.card F = 2 ^ n) (e : ι → ℕ)
    (he : Function.Injective e) (hlt : ∀ i, e i < n) (v : (ι → Fin 2) → k)
    (h : ∀ t : F, tensorRep F k e (uElt t) v = v) (y : ι → Fin 2) (hy : y ≠ fun _ => 0) :
    v y = 0 := by
  let c : (ι → Fin 2) → k := fun y => if y = (fun _ => 0) then 0 else v y
  have hc : ∀ t : F, ∑ y, c y * (algebraMap F k t) ^ aexp e y = 0 := by
    intro t
    have h1 := congrFun (h t) (fun _ => 0)
    rw [tensorRep_apply] at h1
    simp only [tmatE_uElt_base_row] at h1
    have h0 : aexp e (fun _ => (0 : Fin 2)) = 0 := by simp [aexp]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (fun _ : ι => (0 : Fin 2)))] at h1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (fun _ : ι => (0 : Fin 2)))]
    simp only [c, h0, ite_true, zero_mul, pow_zero, one_mul, zero_add] at h1 ⊢
    have h2 : ∑ x ∈ Finset.univ.erase (fun _ : ι => (0 : Fin 2)),
        (if x = (fun _ => 0) then 0 else v x) * (algebraMap F k t) ^ aexp e x =
        ∑ x ∈ Finset.univ.erase (fun _ : ι => (0 : Fin 2)),
          (algebraMap F k t) ^ aexp e x * v x := by
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [ite_eq_right (Finset.ne_of_mem_erase hx), mul_comm]
    rw [h2]
    linear_combination h1
  have := eq_zero_of_sum_pow_eq_zero (F := F) (k := k) (aexp e) (aexp_injective e he)
    (fun y => by rw [hF]; exact aexp_lt e he hlt y) c hc y
  simpa [c, hy] using this

theorem span_lElt_baseVec {n : ℕ} (hF : Fintype.card F = 2 ^ n) (e : ι → ℕ)
    (he : Function.Injective e) (hlt : ∀ i, e i < n) :
    Submodule.span k (Set.range fun t : F => tensorRep F k e (lElt t) baseVec) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hfW⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  have hf : ∀ t : F, f (tensorRep F k e (lElt t) baseVec) = 0 := fun t =>
    hfW (Submodule.subset_span ⟨t, rfl⟩)
  have hcoef : ∀ y, f (fun j => if y = j then (1 : k) else 0) = 0 := by
    refine eq_zero_of_sum_pow_eq_zero (F := F) (k := k) (aexp e) (aexp_injective e he)
      (fun y => by rw [hF]; exact aexp_lt e he hlt y)
      (fun y => f (fun j => if y = j then (1 : k) else 0)) (fun t => ?_)
    have h1 := hf t
    rw [LinearMap.pi_apply_eq_sum_univ f] at h1
    refine Eq.trans (Finset.sum_congr rfl fun y _ => ?_) h1
    rw [tensorRep_lElt_baseVec, smul_eq_mul, mul_comm]
  apply hf0
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.pi_apply_eq_sum_univ f]
  simp [hcoef]

omit [Fintype F] in
theorem two_eq_zero_of_algebra (F k : Type*) [Field F] [Field k] [Algebra F k] [CharP k 2] :
    (2 : F) = 0 := by
  apply (algebraMap F k).injective
  rw [map_zero, map_ofNat]
  exact_mod_cast CharP.cast_eq_zero k 2

theorem tensorRep_isIrreducible {n : ℕ} (hF : Fintype.card F = 2 ^ n) (e : ι → ℕ)
    (he : Function.Injective e) (hlt : ∀ i, e i < n) :
    (tensorRep F k e).IsIrreducible := by
  classical
  rw [isIrreducible_iff]
  refine ⟨inferInstance, fun Z hZ => ?_⟩
  by_cases hbot : Z = ⊥
  · exact Or.inl hbot
  right
  have h2F : (2 : F) = 0 := two_eq_zero_of_algebra F k
  have hss : ∀ s : F, s + s = 0 := fun s => by rw [← two_mul, h2F, zero_mul]
  obtain ⟨v, hvZ, hv0, hvfix⟩ := exists_fixed_of_commuting_involutions (tensorRep F k e)
    (Finset.univ.image (fun t : F => uElt t))
    (by
      intro x hx y hy
      obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hy
      rw [← uElt_add, ← uElt_add, add_comm])
    (by
      intro x hx
      obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hx
      rw [← uElt_add, hss, uElt_zero])
    Z (fun x _ => hZ x) hbot
  have hvbase : v = v (fun _ => 0) • baseVec := by
    funext y
    by_cases hy : y = fun _ => 0
    · subst hy; simp [baseVec_apply]
    · rw [fixed_of_uElt hF e he hlt v
        (fun t => hvfix _ (Finset.mem_image_of_mem _ (Finset.mem_univ t))) y hy]
      simp [baseVec_apply, hy]
  have hc : v (fun _ => 0) ≠ 0 := by
    intro hc
    apply hv0
    rw [hvbase, hc, zero_smul]
  have hbase : (baseVec : (ι → Fin 2) → k) ∈ Z := by
    have h1 : (v (fun _ => 0))⁻¹ • v ∈ Z := Z.smul_mem _ hvZ
    have h2 : (v (fun _ => 0))⁻¹ • v = baseVec :=
      calc (v (fun _ => 0))⁻¹ • v = (v (fun _ => 0))⁻¹ • (v (fun _ => 0) • baseVec) :=
            congrArg (fun w => (v (fun _ => 0))⁻¹ • w) hvbase
        _ = baseVec := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    rwa [h2] at h1
  rw [eq_top_iff, ← span_lElt_baseVec hF e he hlt, Submodule.span_le]
  rintro _ ⟨t, rfl⟩
  exact hZ _ _ hbase

theorem tensorRep_fixed_iff {n : ℕ} (hF : Fintype.card F = 2 ^ n) (e : ι → ℕ)
    (he : Function.Injective e) (hlt : ∀ i, e i < n) (v : (ι → Fin 2) → k) :
    (∀ t : F, tensorRep F k e (uElt t) v = v) ↔ ∃ c : k, v = c • baseVec := by
  constructor
  · intro h
    refine ⟨v (fun _ => 0), ?_⟩
    funext y
    by_cases hy : y = fun _ => 0
    · subst hy; simp [baseVec_apply]
    · rw [fixed_of_uElt hF e he hlt v h y hy]
      simp [baseVec_apply, hy]
  · rintro ⟨c, rfl⟩ t
    rw [map_smul, tensorRep_uElt_baseVec]

end Irreducible

theorem torus_weight_eq {F : Type*} [Field F] [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n)
    {a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (h : ∀ z : Fˣ, z ^ a = z ^ b) :
    a = b ∨ (a = 0 ∧ b = 2 ^ n - 1) ∨ (b = 0 ∧ a = 2 ^ n - 1) := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = 2 ^ n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, Nat.card_eq_fintype_card, hF]
  have hmod : a ≡ b [MOD 2 ^ n - 1] := by
    rw [← hord]; exact pow_eq_pow_iff_modEq.mp (h g)
  unfold Nat.ModEq at hmod
  have key : ∀ x : ℕ, x < 2 ^ n → (x < 2 ^ n - 1 ∧ x % (2 ^ n - 1) = x) ∨
      (x = 2 ^ n - 1 ∧ x % (2 ^ n - 1) = 0) := by
    intro x hx
    by_cases hxN : x < 2 ^ n - 1
    · exact Or.inl ⟨hxN, Nat.mod_eq_of_lt hxN⟩
    · right
      have : x = 2 ^ n - 1 := by omega
      exact ⟨this, by rw [this, Nat.mod_self]⟩
  rcases key a ha with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ <;> rcases key b hb with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
  · left; rw [← ha2, ← hb2]; exact hmod
  · right; left; exact ⟨by rw [← ha2, hmod, hb2], hb1⟩
  · right; right; exact ⟨by rw [← hb2, ← hmod, ha2], ha1⟩
  · left; omega

section FrobTensor

variable (F : Type*) [Field F] (k : Type*) [Field k] [Algebra F k] [CharP k 2]

@[expose] def frobTensor (J : Finset ℕ) : Representation k SL(2, F) ((J → Fin 2) → k) :=
  tensorRep F k (fun i : J => (i : ℕ))

variable {F k}

omit [CharP k 2] in
theorem finrank_frobTensor (J : Finset ℕ) :
    Module.finrank k ((J → Fin 2) → k) = 2 ^ J.card := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fun]
  simp

theorem frobTensor_isIrreducible [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n) {J : Finset ℕ}
    (hJ : ∀ i ∈ J, i < n) : (frobTensor F k J).IsIrreducible :=
  tensorRep_isIrreducible hF _ Subtype.val_injective (fun i => hJ i i.2)

theorem frobTensor_dElt_baseVec (z : Fˣ) (J : Finset ℕ) :
    frobTensor F k J (dElt z) baseVec = (algebraMap F k z) ^ (∑ i ∈ J, 2 ^ i) • baseVec := by
  unfold frobTensor
  rw [tensorRep_dElt_baseVec, Finset.univ_eq_attach, Finset.sum_attach J (fun i => 2 ^ i)]

end FrobTensor

section Noniso

variable {F : Type*} [Field F] [Fintype F] {k : Type*} [Field k] [Algebra F k] [CharP k 2]

theorem equiv_apply {G A V W : Type*} [Semiring A] [Monoid G] [AddCommMonoid V] [AddCommMonoid W]
    [Module A V] [Module A W] {ρ : Representation A G V} {σ : Representation A G W}
    (φ : ρ.Equiv σ) (g : G) (v : V) : φ (ρ g v) = σ g (φ v) :=
  Representation.IntertwiningMap.isIntertwining ρ σ φ.toIntertwiningMap g v

theorem frobTensor_nonisomorphic {n : ℕ} (hF : Fintype.card F = 2 ^ n) {J K : Finset ℕ}
    (hJ : ∀ i ∈ J, i < n) (hK : ∀ i ∈ K, i < n) (φ : (frobTensor F k J).Equiv (frobTensor F k K)) :
    J = K := by
  classical
  have hJinj : Function.Injective (fun i : J => (i : ℕ)) := Subtype.val_injective
  have hKinj : Function.Injective (fun i : K => (i : ℕ)) := Subtype.val_injective
  have hfix : ∀ t : F, tensorRep F k (fun i : K => (i : ℕ)) (uElt t) (φ baseVec) = φ baseVec := by
    intro t
    have h1 := equiv_apply φ (uElt t) baseVec
    have h2 : frobTensor F k J (uElt t) baseVec = baseVec := tensorRep_uElt_baseVec _ t
    rw [h2] at h1
    exact h1.symm
  obtain ⟨c, hc⟩ := (tensorRep_fixed_iff hF _ hKinj (fun i => hK i i.2) (φ baseVec)).mp hfix
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc
    have : (baseVec : (J → Fin 2) → k) = 0 := φ.toLinearEquiv.injective (by simpa using hc)
    have h3 := congrFun this (fun _ => 0)
    simp [baseVec_apply] at h3
  have hm : ∀ z : Fˣ, z ^ (∑ i ∈ J, 2 ^ i) = z ^ (∑ i ∈ K, 2 ^ i) := by
    intro z
    have h1 := equiv_apply φ (dElt z) baseVec
    rw [frobTensor_dElt_baseVec, map_smul, hc, map_smul] at h1
    have h2 : frobTensor F k K (dElt z) (baseVec : (K → Fin 2) → k) =
        (algebraMap F k z) ^ (∑ i ∈ K, 2 ^ i) • baseVec := frobTensor_dElt_baseVec z K
    rw [h2] at h1
    have h3 := congrFun h1 (fun _ => 0)
    simp only [Pi.smul_apply, baseVec_apply, ite_true, smul_eq_mul, mul_one] at h3
    have h4 : (algebraMap F k z) ^ (∑ i ∈ J, 2 ^ i) = (algebraMap F k z) ^ (∑ i ∈ K, 2 ^ i) :=
      mul_left_cancel₀ hc0 (by linear_combination h3)
    apply Units.ext
    apply (algebraMap F k).injective
    simpa [map_pow] using h4
  have hn : 1 < 2 ^ n := hF ▸ Fintype.one_lt_card
  have hJlt : ∑ i ∈ J, 2 ^ i < 2 ^ n := Nat.geomSum_lt le_rfl hJ
  have hKlt : ∑ i ∈ K, 2 ^ i < 2 ^ n := Nat.geomSum_lt le_rfl hK
  have hdim := φ.toLinearEquiv.finrank_eq
  rw [finrank_frobTensor, finrank_frobTensor] at hdim
  have hcard : J.card = K.card := Nat.pow_right_injective le_rfl hdim
  have hempty : ∀ L : Finset ℕ, ∑ i ∈ L, 2 ^ i = 0 → L = ∅ := by
    intro L hL
    refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
    have := (Finset.sum_eq_zero_iff.mp hL) i hi
    exact absurd this (by positivity)
  rcases torus_weight_eq hF hJlt hKlt hm with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Finset.equivBitIndices.symm.injective h
  · exfalso
    have hJe := hempty J h1
    have hKe : K = ∅ := by
      rw [hJe, Finset.card_empty] at hcard
      exact Finset.card_eq_zero.mp hcard.symm
    rw [hKe, Finset.sum_empty] at h2
    omega
  · exfalso
    have hKe := hempty K h1
    have hJe : J = ∅ := by
      rw [hKe, Finset.card_empty] at hcard
      exact Finset.card_eq_zero.mp hcard
    rw [hJe, Finset.sum_empty] at h2
    omega

end Noniso

end CFSG.QuasithinUnique.Setup.SL2Modules
