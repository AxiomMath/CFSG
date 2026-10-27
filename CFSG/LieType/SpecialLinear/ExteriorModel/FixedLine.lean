module

public import CFSG.LieType.SpecialLinear.ExteriorModel.Binary
public import CFSG.Quasithin.Background.SmithCurtisBasic

public section

namespace CFSG.LieType.SpecialLinear.ExteriorModel

open Matrix

variable {k : Type} [Field k] {n : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ]

theorem prod_laurent_T {α : Type*} (S : Finset α) (f : α → ℤ) :
    (∏ x ∈ S, LaurentPolynomial.T (R := k) (f x)) =
      LaurentPolynomial.T (R := k) (∑ x ∈ S, f x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ← LaurentPolynomial.T_add]

theorem laurent_T_injective : Function.Injective (LaurentPolynomial.T (R := k)) := by
  intro m n hmn
  have h := congrArg (fun z : LaurentPolynomial k => z.coeff m) hmn
  simp only [LaurentPolynomial.T_apply] at h
  by_cases hnm : n = m
  · exact hnm.symm
  · rw [if_neg hnm] at h
    simp at h

theorem bDer_kdeg_mem (ε : τ → Finset (Fin n)) (x : τ × Fin n × Fin n)
    (i j : BIdx ε) (h : bDer (k := k) ε x i j ≠ 0) :
    (kdeg i : ℤ) = (kdeg j : ℤ) + ((x.2.1 : ℤ) - (x.2.2 : ℤ)) := by
  obtain ⟨r, a, b⟩ := x
  let L := LaurentPolynomial k
  let T : ℤ → L := LaurentPolynomial.T
  let g : τ × Fin n → Matrix (Fin n) (Fin n) L :=
    fun _ => Matrix.diagonal fun c : Fin n => T (c : ℤ)
  let g' : τ × Fin n → Matrix (Fin n) (Fin n) L :=
    fun _ => Matrix.diagonal fun c : Fin n => T (-(c : ℤ))
  have hgg' : ∀ p, g p * g' p = 1 := by
    intro p
    dsimp only [g, g']
    rw [Matrix.diagonal_mul_diagonal']
    apply Matrix.ext
    intro u v
    by_cases huv : u = v
    · subst huv
      simp only [Matrix.diagonal_apply, Matrix.one_apply]
      change LaurentPolynomial.T (u : ℤ) * LaurentPolynomial.T (-(u : ℤ)) = 1
      rw [← LaurentPolynomial.T_add]
      simp
    · simp [huv]
  have hkdeg : ∀ s : BIdx ε, (kdeg s : ℤ) =
      ∑ p : τ × Fin n, ∑ c ∈ ((s p : Set.powersetCard (Fin n) (bdeg ε p)) :
        Finset (Fin n)), (c : ℤ) := by
    intro s
    rw [kdeg, Nat.cast_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Nat.cast_sum]
  have hdiag : kronMinor (d := bdeg ε) g =
      Matrix.diagonal (fun s : BIdx ε => T (kdeg s : ℤ)) := by
    rw [kronMinor_diagonal (R := L) (d := bdeg ε)
      (e := fun (_ : τ × Fin n) (c : Fin n) => LaurentPolynomial.T (c : ℤ))]
    congr 1
    funext s
    rw [hkdeg s]
    dsimp only [T]
    rw [show (∏ p : τ × Fin n,
          ∏ c ∈ ((s p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)),
            LaurentPolynomial.T (c : ℤ)) =
        ∏ p : τ × Fin n, LaurentPolynomial.T
          (∑ c ∈ ((s p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)), (c : ℤ)) from
      Finset.prod_congr rfl fun p _ => prod_laurent_T _ _]
    rw [show (∏ p : τ × Fin n, LaurentPolynomial.T
          (∑ c ∈ ((s p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)), (c : ℤ))) =
        LaurentPolynomial.T (∑ p : τ × Fin n,
          ∑ c ∈ ((s p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)), (c : ℤ)) from
      prod_laurent_T _ _]
  have hdiag' : kronMinor (d := bdeg ε) g' =
      Matrix.diagonal (fun s : BIdx ε => T (-(kdeg s : ℤ))) := by
    rw [kronMinor_diagonal (R := L) (d := bdeg ε)
      (e := fun (_ : τ × Fin n) (c : Fin n) => LaurentPolynomial.T (-(c : ℤ)))]
    congr 1
    funext s
    rw [hkdeg s]
    dsimp only [T]
    rw [show (∏ p : τ × Fin n,
          ∏ c ∈ ((s p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)), T (-(c : ℤ))) =
        ∏ p : τ × Fin n, T (∑ c ∈ ((s p : Set.powersetCard (Fin n) (bdeg ε p)) :
          Finset (Fin n)), (-(c : ℤ))) from
      Finset.prod_congr rfl fun p _ => prod_laurent_T _ _]
    rw [show (∏ p : τ × Fin n, T (∑ c ∈ ((s p : Set.powersetCard (Fin n) (bdeg ε p)) :
          Finset (Fin n)), (-(c : ℤ)))) =
        T (∑ p : τ × Fin n, ∑ c ∈ ((s p : Set.powersetCard (Fin n) (bdeg ε p)) :
          Finset (Fin n)), (-(c : ℤ))) from prod_laurent_T _ _]
    congr 1
    rw [← Finset.sum_neg_distrib]
    congr 1
    funext p
    rw [← Finset.sum_neg_distrib]
  have hsingle : (Matrix.diagonal fun c : Fin n => T (c : ℤ)) * Matrix.single a b 1 *
      (Matrix.diagonal fun c : Fin n => T (-(c : ℤ))) =
      T ((a : ℤ) - (b : ℤ)) • Matrix.single a b 1 := by
    apply Matrix.ext
    intro u v
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
    by_cases h : u = a ∧ v = b
    · obtain ⟨rfl, rfl⟩ := h
      simp only [Matrix.single_apply, if_true, and_self,
        mul_one]
      dsimp only [T]
      change LaurentPolynomial.T (u : ℤ) * LaurentPolynomial.T (-(v : ℤ)) =
        LaurentPolynomial.T ((u : ℤ) - (v : ℤ))
      rw [← LaurentPolynomial.T_add (R := k)]
      congr 1
    · have h' : ¬(a = u ∧ b = v) := by
        rintro ⟨rfl, rfl⟩
        exact h ⟨rfl, rfl⟩
      simp [h']
  have hconj := kronMinor_mul_kronDer_mul_kronMinor (d := bdeg ε)
    (P := fun p : τ × Fin n => p.1 = r) (g := g) (g' := g')
    (g₀ := Matrix.diagonal fun c : Fin n => T (c : ℤ))
    (g₀' := Matrix.diagonal fun c : Fin n => T (-(c : ℤ)))
    hgg' (fun _ _ => rfl) (fun _ _ => rfl) (Matrix.single a b (1 : L))
  have hmain : Matrix.diagonal (fun s : BIdx ε => T (kdeg s : ℤ)) *
        kronDer (d := bdeg ε) (fun p : τ × Fin n => p.1 = r) (Matrix.single a b (1 : L)) *
        Matrix.diagonal (fun s : BIdx ε => T (-(kdeg s : ℤ))) =
      T ((a : ℤ) - (b : ℤ)) •
        kronDer (d := bdeg ε) (fun p : τ × Fin n => p.1 = r) (Matrix.single a b (1 : L)) := by
    rw [hdiag, hdiag', hsingle, kronDer_smul] at hconj
    exact hconj
  have hentry := congrFun (congrFun hmain i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul] at hentry
  have hsingle_map : (Matrix.single a b (1 : k)).map (algebraMap k L) =
      Matrix.single a b (1 : L) := by
    ext x y
    by_cases hx : x = a <;> by_cases hy : y = b <;>
      simp [Matrix.single_apply, hx, hy]
  have hD : kronDer (d := bdeg ε) (fun p : τ × Fin n => p.1 = r)
      (Matrix.single a b (1 : L)) i j ≠ 0 := by
    have hmap : kronDer (d := bdeg ε) (fun p : τ × Fin n => p.1 = r)
        (Matrix.single a b (1 : L)) =
        (kronDer (d := bdeg ε) (fun p : τ × Fin n => p.1 = r)
          (Matrix.single a b (1 : k))).map (algebraMap k L) := by
      rw [← hsingle_map, kronDer_map]
    rw [hmap]
    intro h0
    apply h
    have hC_inj : Function.Injective (algebraMap k L) := by
      intro x y hxy
      have h' := congrArg (fun z : L => z.coeff 0) hxy
      change (LaurentPolynomial.C x).coeff 0 = (LaurentPolynomial.C y).coeff 0 at h'
      simpa using h'
    apply hC_inj
    simpa [Matrix.map_apply, bDer] using h0
  have hT : T ((kdeg i : ℤ) - (kdeg j : ℤ)) = T ((a : ℤ) - (b : ℤ)) := by
    apply mul_right_cancel₀ hD
    calc T ((kdeg i : ℤ) - (kdeg j : ℤ)) *
          kronDer (d := bdeg ε) (fun p : τ × Fin n => p.1 = r) (Matrix.single a b (1 : L)) i j
        = (T (kdeg i : ℤ) * T (-(kdeg j : ℤ))) *
          kronDer (d := bdeg ε) (fun p : τ × Fin n => p.1 = r) (Matrix.single a b (1 : L)) i j := by
          rw [← LaurentPolynomial.T_add (R := k)]
          congr 1
      _ = T (kdeg i : ℤ) *
          kronDer (d := bdeg ε) (fun p : τ × Fin n => p.1 = r) (Matrix.single a b (1 : L)) i j *
          T (-(kdeg j : ℤ)) := by ring
      _ = T ((a : ℤ) - (b : ℤ)) *
          kronDer (d := bdeg ε) (fun p : τ × Fin n => p.1 = r) (Matrix.single a b (1 : L)) i j :=
          hentry
  have hexp := laurent_T_injective (k := k) hT
  simp only at hexp ⊢
  omega

omit [DecidableEq τ] in
theorem bvec_kdeg_mem (ε : τ → Finset (Fin n)) (i : BIdx ε) (h : bvec (k := k) ε i ≠ 0) :
    (kdeg i : ℤ) = (kdeg (btop ε) : ℤ) := by
  have hi : i = btop ε := by
    by_contra hne
    exact h (by simp [bvec, Pi.single_eq_of_ne hne])
  rw [hi]

theorem homComp_kdeg_mem_bCyc (ε : τ → Finset (Fin n)) {w : BIdx ε → k} (hw : w ∈ bCyc ε) (e : ℤ) :
    homComp (fun s : BIdx ε => (kdeg s : ℤ)) e w ∈ bCyc ε :=
  homComp_mem_cyclicSub (Γ := ℤ) (deg := fun s : BIdx ε => (kdeg s : ℤ))
    (δ := fun x : τ × Fin n × Fin n => (x.2.1 : ℤ) - (x.2.2 : ℤ))
    (fun x => bDer_kdeg_mem (k := k) ε x) (e₀ := (kdeg (btop ε) : ℤ))
    (fun i hi => bvec_kdeg_mem (k := k) ε i hi) hw e

theorem homComp_kdeg_mem_bRad (ε : τ → Finset (Fin n)) {w : BIdx ε → k} (hw : w ∈ bRad ε) (e : ℤ) :
    homComp (fun s : BIdx ε => (kdeg s : ℤ)) e w ∈ bRad ε :=
  homComp_mem_dotRad (deg := fun s : BIdx ε => (kdeg s : ℤ))
    (C := bCyc (k := k) ε) (fun _ _ hy => homComp_kdeg_mem_bCyc ε hy _) hw e

theorem bDer_mul_sub_mul_bDer (ε : τ → Finset (Fin n)) (r : τ) {a b c : Fin n} (hac : a ≠ c) :
    bDer (k := k) ε (r, a, b) * bDer ε (r, b, c) - bDer ε (r, b, c) * bDer ε (r, a, b) = bDer ε (r, a, c) := by
  change kronDer (d := bdeg ε) (fun p : τ × Fin n => p.1 = r) (Matrix.single a b 1) *
      kronDer (d := bdeg ε) (fun p : τ × Fin n => p.1 = r) (Matrix.single b c 1) -
      kronDer (d := bdeg ε) (fun p : τ × Fin n => p.1 = r) (Matrix.single b c 1) *
      kronDer (d := bdeg ε) (fun p : τ × Fin n => p.1 = r) (Matrix.single a b 1) =
    kronDer (d := bdeg ε) (fun p : τ × Fin n => p.1 = r) (Matrix.single a c 1)
  rw [kronDer_mul_sub_mul]
  congr 1
  rw [Matrix.single_mul_single_same]
  rw [Matrix.single_mul_single_of_ne (h := hac.symm)]
  simp

theorem bDer_mulVec_mem_bRad_of_simple (ε : τ → Finset (Fin n)) {w : BIdx ε → k}
    (h : ∀ (r : τ) (a b : Fin n), (b : ℕ) = a + 1 → bDer ε (r, a, b) *ᵥ w ∈ bRad ε)
    (r : τ) {a b : Fin n} (hab : a < b) : bDer ε (r, a, b) *ᵥ w ∈ bRad ε := by
  have H : ∀ m : ℕ, ∀ a b : Fin n, (b : ℕ) - (a : ℕ) = m → a < b →
      bDer ε (r, a, b) *ᵥ w ∈ bRad ε := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro a b hk hab
      rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hab) with hlt | heq
      · let a' : Fin n := ⟨(a : ℕ) + 1, by omega⟩
        have ha'val : (a' : ℕ) = (a : ℕ) + 1 := rfl
        have ha'lt : a' < b := by
          change (a' : ℕ) < (b : ℕ)
          rw [ha'val]
          exact hlt
        have hk' : (b : ℕ) - (a' : ℕ) < m := by
          rw [← hk]
          omega
        have hbr : bDer (k := k) ε (r, a, a') * bDer (k := k) ε (r, a', b) -
            bDer (k := k) ε (r, a', b) * bDer (k := k) ε (r, a, a') =
            bDer (k := k) ε (r, a, b) :=
          bDer_mul_sub_mul_bDer ε r (ne_of_lt hab)
        rw [← hbr, Matrix.sub_mulVec]
        simp only [← Matrix.mulVec_mulVec]
        exact Submodule.sub_mem _
          (bDer_mulVec_mem_bRad (k := k) ε (r, a, a')
            (ih ((b : ℕ) - (a' : ℕ)) hk' a' b rfl ha'lt))
          (bDer_mulVec_mem_bRad (k := k) ε (r, a', b)
            (h r a a' ha'val))
      · exact h r a b heq.symm
  exact H ((b : ℕ) - (a : ℕ)) a b rfl hab

@[expose] noncomputable def bFirst (ε : τ → Finset (Fin n)) (g : τ → Matrix (Fin n) (Fin n) k) :
    Matrix (BIdx ε) (BIdx ε) k :=
  ∑ r, ∑ a : Fin n, ∑ b : Fin n, if (b : ℕ) = a + 1 then g r a b • bDer ε (r, a, b) else 0

@[expose] noncomputable def bSuper (_ε : τ → Finset (Fin n)) (g : τ → Matrix (Fin n) (Fin n) k)
    (r : τ) : Matrix (Fin n) (Fin n) k :=
  ∑ a : Fin n, ∑ b : Fin n, if (b : ℕ) = a + 1 then g r a b • Matrix.single a b 1 else 0

theorem bFirst_eq_sum_kronDer (ε : τ → Finset (Fin n)) (g : τ → Matrix (Fin n) (Fin n) k) :
    bFirst ε g = ∑ r, kronDer (d := bdeg ε) (fun p : τ × Fin n => p.1 = r) (bSuper ε g r) := by
  simp only [bFirst, bSuper]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← kronDerLin_apply (d := bdeg ε) (P := fun p : τ × Fin n => p.1 = r)]
  simp only [map_sum, kronDerLin_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : (b : ℕ) = a + 1
  · rw [if_pos h, if_pos h, kronDer_smul]
    rfl
  · rw [if_neg h, if_neg h, kronDer_zero]

theorem bFirst_apply_ne_zero [CharP k 2] (ε : τ → Finset (Fin n)) (g : τ → Matrix (Fin n) (Fin n) k)
    {s t : BIdx ε} (h : bFirst ε g s t ≠ 0) : kdeg s + 1 = kdeg t := by
  simp only [bFirst, Matrix.sum_apply] at h
  obtain ⟨r, -, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hr
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  by_cases hb1 : (b : ℕ) = a + 1
  · have hder : bDer (k := k) ε (r, a, b) s t ≠ 0 := by
      intro h0
      rw [if_pos hb1] at hb
      have hb' : g r a b * bDer (k := k) ε (r, a, b) s t ≠ 0 := by
        simpa [Matrix.smul_apply, smul_eq_mul] using hb
      exact (mul_ne_zero_iff.mp hb').2 h0
    have hdeg := bDer_kdeg_mem (k := k) ε (r, a, b) s t hder
    have hcast : (b : ℤ) = (a : ℤ) + 1 := by exact_mod_cast hb1
    simp only at hdeg ⊢
    omega
  · simp [hb1] at hb

section HeightOne

open Polynomial TrivSqZeroExt

@[expose] noncomputable def polyGrade (g : Matrix (Fin n) (Fin n) k) : Matrix (Fin n) (Fin n) k[X] :=
  Matrix.of fun a b => if a ≤ b then monomial ((b : ℕ) - a) (g a b) else 0

omit [Fintype τ] [DecidableEq τ] in
theorem diagonal_X_pow_mul_polyGrade {g : Matrix (Fin n) (Fin n) k} (hg : ∀ a b, b < a → g a b = 0) :
    diagonal (fun c : Fin n => (X : k[X]) ^ (c : ℕ)) * polyGrade g =
      g.map C * diagonal (fun c : Fin n => (X : k[X]) ^ (c : ℕ)) := by
  ext a b
  rw [diagonal_mul, mul_diagonal, Matrix.map_apply, polyGrade, Matrix.of_apply]
  split_ifs with hab
  · rw [← C_mul_X_pow_eq_monomial, mul_left_comm, ← pow_add, Nat.add_sub_cancel' hab]
  · rw [hg a b (lt_of_not_ge hab), C_0, zero_mul, mul_zero]

omit [DecidableEq τ] in
theorem kronMinor_diagonal_X_pow (ε : τ → Finset (Fin n)) :
    kronMinor (d := bdeg ε) (fun _ : τ × Fin n => diagonal (fun c : Fin n => (X : k[X]) ^ (c : ℕ))) =
      diagonal (fun s : BIdx ε => (X : k[X]) ^ kdeg s) := by
  rw [kronMinor_diagonal]
  congr 1
  funext s
  rw [kdeg, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun p _ => Finset.prod_pow_eq_pow_sum _ _ _

theorem kronMinor_polyGrade_apply_of_succ (ε : τ → Finset (Fin n)) {g : τ → Matrix (Fin n) (Fin n) k}
    (hg : ∀ r a b, b < a → g r a b = 0) {s t : BIdx ε} (hst : kdeg s + 1 = kdeg t) :
    kronMinor (d := bdeg ε) (fun p : τ × Fin n => polyGrade (g p.1)) s t = C (bMat ε g s t) * X := by
  have hmat : kronMinor (d := bdeg ε)
        (fun _ : τ × Fin n => diagonal (fun c : Fin n => (X : k[X]) ^ (c : ℕ))) *
        kronMinor (d := bdeg ε) (fun p : τ × Fin n => polyGrade (g p.1)) =
      kronMinor (d := bdeg ε) (fun p : τ × Fin n => (g p.1).map C) *
        kronMinor (d := bdeg ε)
          (fun _ : τ × Fin n => diagonal (fun c : Fin n => (X : k[X]) ^ (c : ℕ))) := by
    rw [← kronMinor_mul, ← kronMinor_mul]
    congr 1
    funext p
    exact diagonal_X_pow_mul_polyGrade (hg p.1)
  have h := congrFun (congrFun hmat s) t
  simp only [kronMinor_diagonal_X_pow, diagonal_mul, mul_diagonal] at h
  rw [kronMinor_map (φ := C)] at h
  change X ^ kdeg s * _ = C (bMat ε g s t) * X ^ kdeg t at h
  rw [← hst, pow_succ] at h
  exact mul_left_cancel₀ (pow_ne_zero _ X_ne_zero) (h.trans (by ring))

omit [Fintype τ] [DecidableEq τ] in
theorem bSuper_apply (ε : τ → Finset (Fin n)) (g : τ → Matrix (Fin n) (Fin n) k) (r : τ) (a b : Fin n) :
    bSuper ε g r a b = if (b : ℕ) = a + 1 then g r a b else 0 := by
  rw [bSuper, Matrix.sum_apply, Finset.sum_eq_single a]
  · rw [Matrix.sum_apply, Finset.sum_eq_single b]
    · split_ifs with h <;> simp
    · intro b' _ hb'
      split_ifs <;> simp [hb']
    · simp
  · intro a' _ ha'
    rw [Matrix.sum_apply]
    refine Finset.sum_eq_zero fun b' _ => ?_
    split_ifs <;> simp [ha']
  · simp

omit [Fintype τ] [DecidableEq τ] in
theorem map_polyGrade_eval₂_eps {g : Matrix (Fin n) (Fin n) k} (hg1 : ∀ a, g a a = 1) :
    (polyGrade g).map (eval₂RingHom (algebraMap k (DualNumber k)) (DualNumber.eps : DualNumber k)) =
      1 + (DualNumber.eps : DualNumber k) •
        (Matrix.of fun a b : Fin n => if (b : ℕ) = a + 1 then g a b else 0).map (inl (M := k)) := by
  refine Matrix.ext fun a b => ?_
  rw [Matrix.map_apply, polyGrade, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.map_apply, Matrix.of_apply, smul_eq_mul]
  by_cases hab : a = b
  · subst hab
    simp [hg1, Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne hab, zero_add]
    split_ifs with h1 h2 h2
    · rw [coe_eval₂RingHom, eval₂_monomial, h2, Nat.add_sub_cancel_left, pow_one,
        TrivSqZeroExt.algebraMap_eq_inl, mul_comm]
    · obtain ⟨m, hm⟩ : ∃ m, (b : ℕ) - a = m + 2 := ⟨(b : ℕ) - a - 2, by
        have : (a : ℕ) < b := lt_of_le_of_ne h1 (fun h => hab (Fin.ext h))
        omega⟩
      rw [coe_eval₂RingHom, eval₂_monomial, hm, pow_add, sq, DualNumber.eps_mul_eps, mul_zero,
        mul_zero, TrivSqZeroExt.inl_zero, mul_zero]
    · exact absurd (Fin.le_iff_val_le_val.mpr (by omega)) h1
    · simp

theorem kronMinor_one_add_eps_smul_twists {d : τ × Fin n → ℕ} (N : τ → Matrix (Fin n) (Fin n) k) :
    kronMinor (d := d) (fun p : τ × Fin n => 1 + (DualNumber.eps : DualNumber k) • (N p.1).map (inl (M := k))) =
      1 + (DualNumber.eps : DualNumber k) •
        (∑ r, kronDer (d := d) (fun p : τ × Fin n => p.1 = r) (N r)).map (inl (M := k)) := by
  have key : ∀ J : Finset τ, kronMinor (d := d) (fun p : τ × Fin n =>
      if p.1 ∈ J then 1 + (DualNumber.eps : DualNumber k) • (N p.1).map (inl (M := k)) else 1) =
      1 + (DualNumber.eps : DualNumber k) •
        (∑ r ∈ J, kronDer (d := d) (fun p : τ × Fin n => p.1 = r) (N r)).map (inl (M := k)) := by
    intro J
    induction J using Finset.induction_on with
    | empty =>
      simp only [Finset.notMem_empty, if_false, Finset.sum_empty, kronMinor_one]
      rw [Matrix.map_zero _ (TrivSqZeroExt.inl_zero k), smul_zero, add_zero]
    | insert r J hrJ ih =>
      have hfac : (fun p : τ × Fin n =>
          if p.1 ∈ insert r J then 1 + (DualNumber.eps : DualNumber k) • (N p.1).map (inl (M := k)) else 1) =
          fun p => (if p.1 = r then 1 + (DualNumber.eps : DualNumber k) • (N r).map (inl (M := k)) else 1) *
            (if p.1 ∈ J then 1 + (DualNumber.eps : DualNumber k) • (N p.1).map (inl (M := k)) else 1) := by
        funext p
        by_cases hp : p.1 = r
        · have hpJ : p.1 ∉ J := hp ▸ hrJ
          rw [if_pos (Finset.mem_insert.mpr (Or.inl hp)), if_pos hp, if_neg hpJ, mul_one, hp]
        · by_cases hpJ : p.1 ∈ J
          · rw [if_pos (Finset.mem_insert.mpr (Or.inr hpJ)), if_neg hp, if_pos hpJ, one_mul]
          · rw [if_neg (by simp [hp, hpJ]), if_neg hp, if_neg hpJ, one_mul]
      rw [hfac, kronMinor_mul, ih, kronMinor_one_add_eps_smul, Finset.sum_insert hrJ,
        one_add_smul_mul_one_add_smul DualNumber.eps_mul_eps]
      rw [Matrix.map_add _ (fun x y => TrivSqZeroExt.inl_add k x y)]
  simpa using key Finset.univ

theorem bMat_apply_eq_bFirst_apply [CharP k 2] (ε : τ → Finset (Fin n)) {g : τ → Matrix (Fin n) (Fin n) k}
    (hg : ∀ r a b, b < a → g r a b = 0) (hg1 : ∀ r a, g r a a = 1) {s t : BIdx ε} (hst : kdeg s + 1 = kdeg t) :
    bMat ε g s t = bFirst ε g s t := by
  set φ : k[X] →+* DualNumber k := eval₂RingHom (algebraMap k (DualNumber k)) (DualNumber.eps : DualNumber k) with hφ
  have h1 : kronMinor (d := bdeg ε) (fun p : τ × Fin n => (polyGrade (g p.1)).map φ) s t =
      TrivSqZeroExt.inl (bMat ε g s t) * (DualNumber.eps : DualNumber k) := by
    rw [kronMinor_map, Matrix.map_apply, kronMinor_polyGrade_apply_of_succ ε hg hst, map_mul, hφ,
      coe_eval₂RingHom, eval₂_C, eval₂_X, TrivSqZeroExt.algebraMap_eq_inl]
  have hsup : ∀ r, (Matrix.of fun a b : Fin n => if (b : ℕ) = a + 1 then g r a b else 0) = bSuper ε g r :=
    fun r => by ext a b; rw [Matrix.of_apply, bSuper_apply]
  have h2 : kronMinor (d := bdeg ε) (fun p : τ × Fin n => (polyGrade (g p.1)).map φ) =
      1 + (DualNumber.eps : DualNumber k) • (bFirst ε g).map (TrivSqZeroExt.inl (M := k)) := by
    simp only [hφ, map_polyGrade_eval₂_eps (hg1 _), hsup]
    rw [kronMinor_one_add_eps_smul_twists, bFirst_eq_sum_kronDer]
  rw [h2] at h1
  have hne : s ≠ t := by
    rintro rfl
    omega
  rw [Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul] at h1
  have h3 := congrArg TrivSqZeroExt.snd h1
  rw [← inr_eq_eps_mul_inl, mul_comm, ← inr_eq_eps_mul_inl, TrivSqZeroExt.snd_inr,
    TrivSqZeroExt.snd_inr] at h3
  exact h3.symm

theorem bMat_sub_one_sub_bFirst_apply_ne_zero [CharP k 2] (ε : τ → Finset (Fin n))
    {g : τ → Matrix (Fin n) (Fin n) k} (hg : ∀ r a b, b < a → g r a b = 0) (hg1 : ∀ r a, g r a a = 1)
    {s t : BIdx ε} (h : (bMat ε g - 1 - bFirst ε g) s t ≠ 0) : kdeg s + 1 < kdeg t := by
  by_contra hlt
  apply h
  rw [Matrix.sub_apply, Matrix.sub_apply]
  rcases lt_trichotomy (kdeg t) (kdeg s + 1) with hlt' | heq | hgt
  · have hF : bFirst ε g s t = 0 := by
      by_contra h0
      have := bFirst_apply_ne_zero ε g h0
      omega
    by_cases hst : s = t
    · subst hst
      rw [hF, Matrix.one_apply_eq]
      simp only [bMat]
      rw [kronMinor_self_of_unitriangular (d := bdeg ε) (g := fun p : τ × Fin n => g p.1)
        (fun p => hg p.1) (fun p => hg1 p.1), sub_self, sub_zero]
    · rw [hF, Matrix.one_apply_ne hst]
      simp only [bMat]
      rw [kronMinor_eq_zero_of_upper_of_ne (d := bdeg ε) (g := fun p : τ × Fin n => g p.1)
        (fun p => hg p.1) hst (by omega), sub_zero, sub_zero]
  · have hst : s ≠ t := by
      rintro rfl
      omega
    rw [bMat_apply_eq_bFirst_apply ε hg hg1 heq.symm, Matrix.one_apply_ne hst, sub_zero, sub_self]
  · exact absurd hgt hlt

end HeightOne

theorem bFirst_mulVec_homComp_mem_bRad [CharP k 2] (ε : τ → Finset (Fin n))
    {h : τ → SpecialLinearGroup (Fin n) k}
    (hg : ∀ r a b, b < a → (h r : Matrix (Fin n) (Fin n) k) a b = 0)
    (hg1 : ∀ r a, (h r : Matrix (Fin n) (Fin n) k) a a = 1)
    {w : BIdx ε → k} (hw : bMat ε (fun r => (h r : Matrix (Fin n) (Fin n) k)) *ᵥ w - w ∈ bRad ε) (e : ℤ)
    (htop : ∀ e', e < e' → homComp (fun s : BIdx ε => (kdeg s : ℤ)) e' w ∈ bRad ε) :
    bFirst ε (fun r => (h r : Matrix (Fin n) (Fin n) k)) *ᵥ homComp (fun s : BIdx ε => (kdeg s : ℤ)) e w ∈ bRad ε := by
  let A : Matrix (BIdx ε) (BIdx ε) k := bMat ε (fun r => (h r : Matrix (Fin n) (Fin n) k))
  let A₁ : Matrix (BIdx ε) (BIdx ε) k := bFirst ε (fun r => (h r : Matrix (Fin n) (Fin n) k))
  let A₂ : Matrix (BIdx ε) (BIdx ε) k := A - 1 - A₁
  have hA : A = 1 + A₁ + A₂ := by
    dsimp [A₂]
    abel
  have hC : ∀ e, ∀ y ∈ bCyc (k := k) ε,
      homComp (fun s : BIdx ε => (kdeg s : ℤ)) e y ∈ bCyc (k := k) ε :=
    fun e y hy => homComp_kdeg_mem_bCyc ε hy e
  have hAR : ∀ x ∈ dotRad (bCyc (k := k) ε), A *ᵥ x ∈ dotRad (bCyc (k := k) ε) := by
    intro x hx
    exact bMat_mulVec_mem_bRad ε h hx
  have hA1 : ∀ i j, A₁ i j ≠ 0 → (kdeg i : ℤ) + 1 = (kdeg j : ℤ) := by
    intro i j hij
    have := bFirst_apply_ne_zero (k := k) ε (fun r => (h r : Matrix (Fin n) (Fin n) k)) hij
    exact_mod_cast this
  have hA2 : ∀ i j, A₂ i j ≠ 0 → (kdeg i : ℤ) + 1 < (kdeg j : ℤ) := by
    intro i j hij
    have := bMat_sub_one_sub_bFirst_apply_ne_zero (k := k) ε hg hg1 hij
    omega
  have := mulVec_homComp_mem_dotRad (deg := fun s : BIdx ε => (kdeg s : ℤ))
    (C := bCyc (k := k) ε) hC (A := A) (A₁ := A₁) (A₂ := A₂) hA hAR
    (h := 1) hA1 hA2 hw e htop
  simpa [A₁, bRad] using this

theorem sum_homComp_kdeg (ε : τ → Finset (Fin n)) (v : BIdx ε → k) :
    ∑ e ∈ Finset.univ.image (fun s : BIdx ε => (kdeg s : ℤ)),
      homComp (fun s : BIdx ε => (kdeg s : ℤ)) e v = v := by
  funext s
  rw [Finset.sum_apply]
  simp only [homComp]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_image_of_mem _ (Finset.mem_univ s))]

theorem sub_smul_bvec_mem_bRad_of_homComp (ε : τ → Finset (Fin n)) {w : BIdx ε → k} (hw : w ∈ bCyc ε)
    (h : ∀ e : ℤ, (∀ e', e < e' → homComp (fun s : BIdx ε => (kdeg s : ℤ)) e' w ∈ bRad ε) →
      ∀ (r : τ) (a b : Fin n), (b : ℕ) = a + 1 →
        bDer ε (r, a, b) *ᵥ homComp (fun s : BIdx ε => (kdeg s : ℤ)) e w ∈ bRad ε) :
    w - (w ⬝ᵥ bvec ε) • bvec ε ∈ bRad ε := by
  set deg : BIdx ε → ℤ := fun s => (kdeg s : ℤ) with hdeg
  set N : ℤ := ((Finset.univ.sup fun s : BIdx ε => kdeg s : ℕ) : ℤ) with hN
  have hle : ∀ s : BIdx ε, deg s ≤ N := fun s => by
    simp only [hdeg, hN]
    exact_mod_cast Finset.le_sup (f := fun s : BIdx ε => kdeg s) (Finset.mem_univ s)
  have hge : ∀ s : BIdx ε, (kdeg (btop ε) : ℤ) ≤ deg s := fun s => by
    simp only [hdeg]
    exact_mod_cast kdeg_ktop_le (bdeg_le ε) s
  have hzero : ∀ e, N < e → homComp deg e w = 0 := by
    intro e he
    funext s
    simp only [homComp, Pi.zero_apply]
    rw [if_neg]
    have := hle s
    omega
  have hbvec : ∀ e, e ≠ (kdeg (btop ε) : ℤ) → homComp deg e (bvec (k := k) ε) = 0 := by
    intro e he
    funext s
    simp only [homComp, Pi.zero_apply]
    split_ifs with hs
    · rw [bvec, Pi.single_apply, if_neg]
      rintro rfl
      exact he hs.symm
    · rfl
  have hhigh : ∀ m : ℕ, ∀ e : ℤ, (kdeg (btop ε) : ℤ) < e → N - e < m → homComp deg e w ∈ bRad ε := by
    intro m
    induction m with
    | zero =>
      intro e _ he
      rw [hzero e (by omega)]
      exact Submodule.zero_mem _
    | succ m ih =>
      intro e he₀e hm
      by_cases hNe : N < e
      · rw [hzero e hNe]
        exact Submodule.zero_mem _
      have htop : ∀ e', e < e' → homComp deg e' w ∈ bRad ε := fun e' he' =>
        ih e' (by omega) (by omega)
      have hraise : ∀ r a b, a < b → bDer ε (r, a, b) *ᵥ homComp deg e w ∈ bRad ε :=
        fun r a b hab => bDer_mulVec_mem_bRad_of_simple ε (h e htop) r hab
      have hsub := sub_smul_bvec_mem_bRad ε (homComp_kdeg_mem_bCyc ε hw e) hraise
      have hdot : homComp deg e w ⬝ᵥ bvec ε = 0 := by
        rw [bvec, dotProduct_single, mul_one]
        simp only [homComp]
        rw [if_neg (by simp only [hdeg]; omega)]
      rwa [hdot, zero_smul, sub_zero] at hsub
  have hcomp : ∀ e ∈ Finset.univ.image deg,
      homComp deg e (w - (w ⬝ᵥ bvec ε) • bvec ε) ∈ bRad ε := by
    intro e _
    rcases lt_trichotomy e (kdeg (btop ε) : ℤ) with hlt | heq | hgt
    · have h0 : homComp deg e (w - (w ⬝ᵥ bvec ε) • bvec ε) = 0 := by
        funext s
        simp only [homComp, Pi.zero_apply]
        rw [if_neg]
        have := hge s
        omega
      rw [h0]
      exact Submodule.zero_mem _
    · have h0 : homComp deg e (w - (w ⬝ᵥ bvec ε) • bvec ε) = 0 := by
        funext s
        simp only [homComp, Pi.zero_apply]
        split_ifs with hs
        · have hs' : s = btop ε := eq_ktop_of_kdeg_le (bdeg_le ε) (by
            change kdeg s ≤ kdeg (btop ε)
            simp only [hdeg] at hs
            omega)
          subst hs'
          rw [Pi.sub_apply, Pi.smul_apply, bvec, dotProduct_single, mul_one, Pi.single_eq_same,
            smul_eq_mul, mul_one, sub_self]
        · rfl
      rw [h0]
      exact Submodule.zero_mem _
    · have h1 : homComp deg e (w - (w ⬝ᵥ bvec ε) • bvec ε) = homComp deg e w := by
        rw [← homCompLin_apply, map_sub, map_smul, homCompLin_apply, homCompLin_apply,
          hbvec e (ne_of_gt hgt), smul_zero, sub_zero]
      rw [h1]
      exact hhigh ((N - e).toNat + 1) e hgt (by omega)
  rw [← sum_homComp_kdeg ε (w - (w ⬝ᵥ bvec ε) • bvec ε)]
  exact Submodule.sum_mem _ hcomp

@[expose] noncomputable def bTop (ε : τ → Finset (Fin n)) : BModel k ε :=
  Submodule.Quotient.mk ⟨bvec ε, bvec_mem_bCyc ε⟩

theorem bTop_ne_zero (ε : τ → Finset (Fin n)) : bTop (k := k) ε ≠ 0 := by
  intro h
  apply bvec_notMem_bRad (k := k) ε
  have h' : (⟨bvec (k := k) ε, bvec_mem_bCyc ε⟩ : bCyc (k := k) ε) ∈
      (bRad (k := k) ε).comap (bCyc (k := k) ε).subtype := by
    rw [← Submodule.Quotient.mk_eq_zero
      (p := (bRad (k := k) ε).comap (bCyc (k := k) ε).subtype)]
    simpa [bTop] using h
  simpa [Submodule.mem_comap] using h' 

@[expose] noncomputable def bForm (ε : τ → Finset (Fin n)) : LinearMap.BilinForm k (BModel k ε) := by
  let C : Submodule k (BIdx ε → k) := bCyc (k := k) ε
  let R' : Submodule k C := (bRad (k := k) ε).comap C.subtype
  let B₀ : C →ₗ[k] C →ₗ[k] k :=
    LinearMap.mk₂ k (fun x y => (x : BIdx ε → k) ⬝ᵥ (y : BIdx ε → k))
      (fun x y z => by simp [add_dotProduct])
      (fun a x y => by simp [smul_dotProduct])
      (fun x y z => by simp [dotProduct_add])
      (fun a x y => by simp [dotProduct_smul])
  let B₁ : C ⧸ R' →ₗ[k] C →ₗ[k] k :=
    R'.liftQ B₀ (by
      intro x hx
      apply LinearMap.ext
      intro y
      exact (mem_dotRad.mp hx).2 y y.2)
  let B₂ : (C ⧸ R') →ₗ[k] (C ⧸ R') →ₗ[k] k :=
    R'.liftQ B₁.flip (by
      intro y hy
      apply LinearMap.ext
      intro x
      exact Submodule.Quotient.induction_on (p := R')
        (C := fun x => B₁.flip y x = 0) x fun z => by
        rw [LinearMap.flip_apply, Submodule.liftQ_apply, LinearMap.mk₂_apply]
        exact (dotProduct_comm (z : BIdx ε → k) (y : BIdx ε → k)).trans
          ((mem_dotRad.mp hy).2 z z.2))
  exact B₂.flip

theorem bForm_mk (ε : τ → Finset (Fin n)) (x y : bCyc (k := k) ε) :
    bForm (k := k) ε (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = (x : BIdx ε → k) ⬝ᵥ (y : BIdx ε → k) := by
  simp only [bForm, LinearMap.flip_apply, Submodule.liftQ_apply, LinearMap.mk₂_apply]

theorem bForm_bTop (ε : τ → Finset (Fin n)) : bForm (k := k) ε (bTop ε) (bTop ε) = 1 := by
  rw [bTop, bForm_mk]
  exact bvec_dotProduct_bvec ε

theorem bForm_nondegenerate (ε : τ → Finset (Fin n)) : (bForm (k := k) ε).Nondegenerate := by
  constructor
  · intro m hm
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective
      (p := (bRad (k := k) ε).comap (bCyc (k := k) ε).subtype) m
    rw [Submodule.Quotient.mk_eq_zero]
    refine mem_dotRad.mpr ⟨x.2, fun y hy => ?_⟩
    have h := hm (Submodule.Quotient.mk ⟨y, hy⟩)
    rwa [bForm_mk] at h
  · intro m hm
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective
      (p := (bRad (k := k) ε).comap (bCyc (k := k) ε).subtype) m
    rw [Submodule.Quotient.mk_eq_zero]
    refine mem_dotRad.mpr ⟨x.2, fun y hy => ?_⟩
    have h := hm (Submodule.Quotient.mk ⟨y, hy⟩)
    rw [bForm_mk, dotProduct_comm] at h
    exact h

theorem bForm_bRep [CharP k 2] (ε : τ → Finset (Fin n)) (h h' : τ → SpecialLinearGroup (Fin n) k)
    (hh' : ∀ r, (h' r : Matrix (Fin n) (Fin n) k) = (h r : Matrix (Fin n) (Fin n) k)ᵀ) (x y : BModel k ε) :
    bForm (k := k) ε (bRep ε h x) y = bForm (k := k) ε x (bRep ε h' y) := by
  obtain ⟨x₀, rfl⟩ := Submodule.Quotient.mk_surjective
    (p := (bRad (k := k) ε).comap (bCyc (k := k) ε).subtype) x
  obtain ⟨y₀, rfl⟩ := Submodule.Quotient.mk_surjective
    (p := (bRad (k := k) ε).comap (bCyc (k := k) ε).subtype) y
  simp only [bRep_mk, bForm_mk]
  have hA : bMat ε (fun r => (h' r : Matrix (Fin n) (Fin n) k)) =
      (bMat ε (fun r => (h r : Matrix (Fin n) (Fin n) k)))ᵀ := by
    rw [← bMat_transpose]
    congr 1
    funext r
    exact hh' r
  rw [hA]
  calc (bMat ε (fun r => (h r : Matrix (Fin n) (Fin n) k)) *ᵥ (x₀ : BIdx ε → k)) ⬝ᵥ
        (y₀ : BIdx ε → k)
      = (y₀ : BIdx ε → k) ⬝ᵥ
        (bMat ε (fun r => (h r : Matrix (Fin n) (Fin n) k)) *ᵥ (x₀ : BIdx ε → k)) :=
        dotProduct_comm _ _
    _ = ((y₀ : BIdx ε → k) ᵥ* bMat ε (fun r => (h r : Matrix (Fin n) (Fin n) k))) ⬝ᵥ
        (x₀ : BIdx ε → k) := Matrix.dotProduct_mulVec _ _ _
    _ = ((bMat ε (fun r => (h r : Matrix (Fin n) (Fin n) k)))ᵀ *ᵥ
        (y₀ : BIdx ε → k)) ⬝ᵥ (x₀ : BIdx ε → k) := by
        rw [Matrix.mulVec_transpose]
    _ = (x₀ : BIdx ε → k) ⬝ᵥ
        ((bMat ε (fun r => (h r : Matrix (Fin n) (Fin n) k)))ᵀ *ᵥ (y₀ : BIdx ε → k)) :=
        dotProduct_comm _ _

theorem orbitSpan_bTop_eq_top [CharP k 2] (ε : τ → Finset (Fin n)) {G : Type*} [Group G]
    (π : G →* (τ → SpecialLinearGroup (Fin n) k))
    (hT : ∀ g, ∃ g', ∀ r, (π g' r : Matrix (Fin n) (Fin n) k) = (π g r : Matrix (Fin n) (Fin n) k)ᵀ)
    {U : Subgroup G} [Finite U] (hU : IsPGroup 2 U)
    (hfix : ∀ x : BModel k ε, (∀ u ∈ U, bRep ε (π u) x = x) → ∃ c : k, x = c • bTop ε) :
    CFSG.Quasithin.SmithCurtis.orbitSpan ((bRep ε).comp π) (bTop ε) = ⊤ := by
  let ρ : Representation k G (BModel k ε) := (bRep ε).comp π
  let N : Submodule k (BModel k ε) := CFSG.Quasithin.SmithCurtis.orbitSpan ρ (bTop ε)
  have hstable : ∀ g : G, ∀ m ∈ (bForm (k := k) ε).orthogonal N,
      ρ g m ∈ (bForm (k := k) ε).orthogonal N := by
    intro g m hm
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hm ⊢
    intro x hx
    obtain ⟨g', hg'⟩ := hT g
    have hh' : ∀ r, (π g r : Matrix (Fin n) (Fin n) k) =
        ((π g' r : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k)ᵀ := by
      intro r
      rw [hg' r, Matrix.transpose_transpose]
    change bForm (k := k) ε x (bRep ε (π g) m) = 0
    rw [← bForm_bRep ε (π g') (π g) hh' x m]
    exact hm _ (CFSG.Quasithin.SmithCurtis.orbitSpan_stable ρ (bTop ε) g' hx)
  have hbot : (bForm (k := k) ε).orthogonal N = ⊥ := by
    by_contra hne
    obtain ⟨x, hxW, hxne, hxfix⟩ := CFSG.Quasithin.SmithCurtis.exists_fixed_mem ρ (p := 2) hU
      (W := (bForm (k := k) ε).orthogonal N) (fun g _ hw => hstable g _ hw) hne
    obtain ⟨c, hc⟩ := hfix x (fun u hu => hxfix u hu)
    have hbTop_mem : bTop ε ∈ N :=
      CFSG.Quasithin.SmithCurtis.mem_orbitSpan_self ρ (bTop ε)
    have h0 : bForm (k := k) ε (bTop ε) x = 0 :=
      (LinearMap.BilinForm.mem_orthogonal_iff.mp hxW) (bTop ε) hbTop_mem
    rw [hc, map_smul, bForm_bTop, smul_eq_mul, mul_one] at h0
    exact hxne (by rw [hc, h0, zero_smul])
  have htop : N = ⊤ := by
    have hfin := LinearMap.BilinForm.finrank_orthogonal (B := bForm (k := k) ε)
      (bForm_nondegenerate (k := k) ε) N
    rw [hbot, finrank_bot] at hfin
    have hle : Module.finrank k (BModel k ε) ≤ Module.finrank k N :=
      Nat.sub_eq_zero_iff_le.mp hfin.symm
    exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le N) hle)
  exact htop

end CFSG.LieType.SpecialLinear.ExteriorModel

end
