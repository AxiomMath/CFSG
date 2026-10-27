module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aLocal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aBits

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open scoped MatrixGroups Matrix

open CFSG.QuasithinUnique.Setup.X7

section Kron

variable {k : Type*} [CommRing k] {ι : Type*} [Fintype ι] {κ κ' : ι → Type*}

@[expose] def kron (M : ∀ i, Matrix (κ' i) (κ i) k) : Matrix (∀ i, κ' i) (∀ i, κ i) k :=
  Matrix.of fun x' x => ∏ i, M i (x' i) (x i)

theorem kron_apply (M : ∀ i, Matrix (κ' i) (κ i) k) (x' : ∀ i, κ' i) (x : ∀ i, κ i) :
    kron M x' x = ∏ i, M i (x' i) (x i) := rfl

theorem kron_transpose (M : ∀ i, Matrix (κ' i) (κ i) k) :
    (kron M)ᵀ = kron (fun i => (M i)ᵀ) := by
  ext x' x
  simp [kron, Matrix.transpose_apply]

theorem kron_mul [DecidableEq ι] {κ'' : ι → Type*} [∀ i, Fintype (κ' i)]
    (M : ∀ i, Matrix (κ'' i) (κ' i) k) (N : ∀ i, Matrix (κ' i) (κ i) k) :
    kron (fun i => M i * N i) = kron M * kron N := by
  ext x'' x
  simp only [kron, Matrix.of_apply, Matrix.mul_apply]
  have := Finset.prod_univ_sum (fun i => (Finset.univ : Finset (κ' i)))
    (fun i b => M i (x'' i) b * N i b (x i))
  simp only [Fintype.piFinset_univ] at this
  rw [this]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.prod_mul_distrib]

theorem kron_one [∀ i, DecidableEq (κ i)] : kron (fun i => (1 : Matrix (κ i) (κ i) k)) = 1 := by
  ext x' x
  simp only [kron, Matrix.of_apply, Matrix.one_apply]
  by_cases h : x' = x
  · subst h
    simp
  · obtain ⟨i, hi⟩ : ∃ i, x' i ≠ x i := by
      by_contra hc
      push Not at hc
      exact h (funext hc)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])]
    simp [h]

end Kron

section Tensor

variable {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [CharP k 2]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def tensorRepGen (τ : ι → Bool × Bool) (e : ι → ℕ) :
    SL(3, F) →* Matrix (∀ i, Fin (locDim (τ i).1 (τ i).2)) (∀ i, Fin (locDim (τ i).1 (τ i).2)) k where
  toFun g := kron (fun i => locRep k (τ i).1 (τ i).2 (e i) g)
  map_one' := by
    simp only [map_one]
    exact kron_one
  map_mul' g h := by
    simp only [map_mul]
    exact kron_mul _ _

theorem tensorRepGen_apply (τ : ι → Bool × Bool) (e : ι → ℕ) (g : SL(3, F))
    (x' x : ∀ i, Fin (locDim (τ i).1 (τ i).2)) :
    tensorRepGen k τ e g x' x = ∏ i, locRep k (τ i).1 (τ i).2 (e i) g (x' i) (x i) := rfl

@[expose] def hwVec (τ : ι → Bool × Bool) : (∀ i, Fin (locDim (τ i).1 (τ i).2)) → k :=
  Pi.single (fun i => locDist (τ i).1 (τ i).2) 1

theorem tensorRepGen_u3_orbit [CharP F 2] (τ : ι → Bool × Bool) (e : ι → ℕ) (x y z : F)
    (x' : ∀ i, Fin (locDim (τ i).1 (τ i).2)) :
    (tensorRepGen k τ e (u3 x y z)).mulVec (hwVec k τ) x' =
      ∏ i, frK k (e i) (locCoord (τ i).1 (τ i).2 (x' i) x y z) := by
  rw [hwVec, Matrix.mulVec_single_one, Matrix.col_apply, tensorRepGen_apply]
  exact Finset.prod_congr rfl (fun i _ => locRep_u3_col k _ _ _ _ _ _ _)

theorem tensorRepGen_up3_fixed [CharP F 2] (τ : ι → Bool × Bool) (e : ι → ℕ) (x y z : F) :
    (tensorRepGen k τ e (up3 x y z)).mulVec (hwVec k τ) = hwVec k τ := by
  funext x'
  rw [hwVec, Matrix.mulVec_single_one, Matrix.col_apply, tensorRepGen_apply]
  have : ∀ i, locRep k (τ i).1 (τ i).2 (e i) (up3 x y z) (x' i) (locDist (τ i).1 (τ i).2) =
      if x' i = locDist (τ i).1 (τ i).2 then 1 else 0 :=
    fun i => locRep_up3_col k _ _ _ _ _ _ _
  rw [Finset.prod_congr rfl (fun i _ => this i)]
  by_cases h : x' = fun i => locDist (τ i).1 (τ i).2
  · subst h
    simp [Pi.single_eq_same]
  · obtain ⟨i, hi⟩ : ∃ i, x' i ≠ locDist (τ i).1 (τ i).2 := by
      by_contra hc
      push Not at hc
      exact h (funext hc)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])]
    simp [h]

end Tensor

section FieldSums

variable (F : Type*) [Field F] [Fintype F]

theorem sum_pow_card_sub_one [DecidableEq F] : ∑ x : F, x ^ (Fintype.card F - 1) = -1 := by
  have hn : 0 < Fintype.card F - 1 := by
    have := Fintype.one_lt_card (α := F)
    omega
  let φ : Fˣ ↪ F := ⟨fun x => x, Units.val_injective⟩
  have hmap : Finset.univ.map φ = Finset.univ \ {0} := by
    ext x
    simpa only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and,
      Finset.mem_sdiff, Finset.mem_singleton, φ] using! isUnit_iff_ne_zero
  calc ∑ x : F, x ^ (Fintype.card F - 1)
      = ∑ x ∈ Finset.univ \ {(0 : F)}, x ^ (Fintype.card F - 1) := by
        rw [← Finset.sum_sdiff ({0} : Finset F).subset_univ, Finset.sum_singleton,
          zero_pow hn.ne', add_zero]
    _ = ∑ x : Fˣ, ((x : F) ^ (Fintype.card F - 1)) := by
        simp [φ, ← hmap, Finset.univ.sum_map φ]
    _ = -1 := by
        rw [FiniteField.sum_pow_units F (Fintype.card F - 1)]
        simp

theorem sum_add_mul_pow [DecidableEq F] (a b : F) :
    ∑ x : F, (a + b * x) ^ (Fintype.card F - 1) = -b ^ (Fintype.card F - 1) := by
  set n := Fintype.card F - 1 with hn
  have h1 : ∀ x : F, (a + b * x) ^ n =
      ∑ j ∈ Finset.range (n + 1), (b * x) ^ j * a ^ (n - j) * (n.choose j : F) := by
    intro x
    rw [add_comm, add_pow]
  simp_rw [h1]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single n]
  · simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, mul_pow]
    rw [← Finset.mul_sum, sum_pow_card_sub_one F]
    ring
  · intro j hj hjn
    have hjlt : j < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hjn
    have hs : ∑ x : F, x ^ j = 0 := FiniteField.sum_pow_lt_card_sub_one F j hjlt
    calc ∑ x : F, (b * x) ^ j * a ^ (n - j) * (n.choose j : F)
        = (b ^ j * a ^ (n - j) * (n.choose j : F)) * ∑ x : F, x ^ j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [mul_pow]
          ring
      _ = 0 := by rw [hs, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) h

theorem sum_sq_norm [DecidableEq F] :
    ∑ p : F × F × F, (p.2.1 ^ 2 + p.1 * p.2.1 * p.2.2) ^ (Fintype.card F - 1) = -1 := by
  set n := Fintype.card F - 1 with hn
  have h1 : ∀ y z : F, ∑ x : F, (y ^ 2 + x * y * z) ^ n = -(y * z) ^ n := by
    intro y z
    have e : ∀ x : F, y ^ 2 + x * y * z = y ^ 2 + (y * z) * x := fun x => by ring
    simp_rw [e]
    exact sum_add_mul_pow F (y ^ 2) (y * z)
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  have h2 : ∀ y : F, ∑ x : F, ∑ z : F, (y ^ 2 + x * y * z) ^ n = ∑ z : F, ∑ x : F, (y ^ 2 + x * y * z) ^ n :=
    fun y => Finset.sum_comm
  simp_rw [h2, h1]
  simp only [mul_pow, Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [show ∑ x : F, x ^ n = -1 from sum_pow_card_sub_one F]
  ring

end FieldSums

section Mixed

variable {F : Type*} [Field F] [CharP F 2] (k : Type*) [Field k] [Algebra F k]
  [CharP k 2] {f : ℕ}

abbrev TIdx (f : ℕ) (a b : Fin f → Bool) : Type := ∀ i : Fin f, Fin (locDim (a i) (b i))

@[expose] def tensorRep (a b : Fin f → Bool) :
    SL(3, F) →* Matrix (TIdx f a b) (TIdx f a b) k :=
  tensorRepGen k (fun i : Fin f => (a i, b i)) (fun i => (i : ℕ))

@[expose] def hw (a b : Fin f → Bool) : TIdx f a b → k :=
  hwVec k (fun i : Fin f => (a i, b i))

theorem tensorRep_u3_orbit (a b : Fin f → Bool) (x y z : F) (x' : TIdx f a b) :
    (tensorRep k a b (u3 x y z)).mulVec (hw k a b) x' =
      ∏ i : Fin f, frK k (i : ℕ) (locCoord (a i) (b i) (x' i) x y z) :=
  tensorRepGen_u3_orbit k (fun i : Fin f => (a i, b i)) (fun i => (i : ℕ)) x y z x'

theorem tensorRep_up3_fixed (a b : Fin f → Bool) (x y z : F) :
    (tensorRep k a b (up3 x y z)).mulVec (hw k a b) = hw k a b :=
  tensorRepGen_up3_fixed k (fun i : Fin f => (a i, b i)) (fun i => (i : ℕ)) x y z

omit [CharP k 2] in
theorem hw_ne_zero (a b : Fin f → Bool) : hw k a b ≠ 0 := by
  intro h
  have := congrFun h (fun i => locDist (a i) (b i))
  simp [hw, hwVec] at this

theorem card_TIdx (a b : Fin f → Bool) : Fintype.card (TIdx f a b) = ∏ i, locDim (a i) (b i) := by
  simp [Fintype.card_pi]

theorem card_TIdx_ones : Fintype.card (TIdx f (ones f) (ones f)) = 8 ^ f := by
  rw [card_TIdx]
  simp [ones, locDim]

def w7 (f : ℕ) : TIdx f (ones f) (ones f) := fun _ => (⟨7, by decide⟩ : Fin (locDim true true))

omit [CharP F 2] in
theorem prod_frK_eq [Fintype F] (hF : Fintype.card F = 2 ^ f) (P : F) :
    ∏ i : Fin f, frK k (i : ℕ) P = frK k 0 (P ^ (Fintype.card F - 1)) := by
  simp only [frK_apply, pow_zero, pow_one, map_pow]
  rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i => 2 ^ i) f,
    Nat.geomSum_eq (le_refl 2), hF]
  simp

theorem norm_coeff_full [Fintype F] (hF : Fintype.card F = 2 ^ f) :
    ∑ g : lowerUni F, ((tensorRep (F := F) k (ones f) (ones f) (g : SL(3, F))).mulVec
      (hw k (ones f) (ones f))) (w7 f) = 1 := by
  classical
  rw [← (lowerUniEquiv F).sum_comp]
  have h1 : ∀ p : F × F × F, ((tensorRep (F := F) k (ones f) (ones f)
      ((lowerUniEquiv F p : lowerUni F) : SL(3, F))).mulVec (hw k (ones f) (ones f))) (w7 f) =
      frK k 0 ((p.2.1 ^ 2 + p.1 * p.2.1 * p.2.2) ^ (Fintype.card F - 1)) := by
    intro p
    rw [lowerUniEquiv_apply, tensorRep_u3_orbit]
    rw [← prod_frK_eq k hF]
    exact Finset.prod_congr rfl (fun i _ => rfl)
  simp_rw [h1]
  rw [← map_sum, sum_sq_norm F, map_neg, map_one, CharTwo.neg_eq]

end Mixed

section Orbit

variable {F : Type*} [Field F] [CharP F 2] [Fintype F] (k : Type*) [Field k] [Algebra F k]
  [CharP k 2] {f : ℕ}

theorem fullOrbit_basis (hF : Fintype.card F = 2 ^ f) :
    ∃ b : Module.Basis (lowerUni F) k (TIdx f (ones f) (ones f) → k), ∀ u : lowerUni F,
      b u = (tensorRep (F := F) k (ones f) (ones f) (u : SL(3, F))).mulVec
        (hw k (ones f) (ones f)) := by
  classical
  let T := tensorRep (F := F) k (ones f) (ones f)
  let ρ : lowerUni F →* ((TIdx f (ones f) (ones f) → k) →ₗ[k] (TIdx f (ones f) (ones f) → k)) :=
    (matRep T).comp (lowerUni F).subtype
  have hcard : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  have hP : IsPGroup 2 (lowerUni F) := isPGroup_lowerUni hcard
  have hv : ∑ g : lowerUni F, ρ g (hw k (ones f) (ones f)) ≠ 0 := by
    intro h
    have h2 := norm_coeff_full (F := F) k hF
    have h3 : ∑ g : lowerUni F, ((tensorRep (F := F) k (ones f) (ones f) (g : SL(3, F))).mulVec
        (hw k (ones f) (ones f))) (w7 f) = 0 := by
      have := congrFun h (w7 f)
      rw [Finset.sum_apply] at this
      exact this
    exact zero_ne_one (h3.symm.trans h2)
  have hdim : Module.finrank k (TIdx f (ones f) (ones f) → k) = Fintype.card (lowerUni F) := by
    rw [Module.finrank_fintype_fun_eq_card, card_TIdx_ones, card_lowerUni_eq, hF,
      ← pow_mul, mul_comm, pow_mul]
    norm_num
  obtain ⟨b, hb, -, -⟩ := orbit_regular_of_norm_ne_zero k Nat.prime_two hP ρ
    (hw k (ones f) (ones f)) hv hdim
  exact ⟨b, fun u => by rw [hb]; rfl⟩

theorem fullOrbit_span (hF : Fintype.card F = 2 ^ f) :
    Submodule.span k (Set.range fun u : lowerUni F =>
      matRep (tensorRep (F := F) k (ones f) (ones f)) (u : SL(3, F)) (hw k (ones f) (ones f))) = ⊤ := by
  obtain ⟨b, hb⟩ := fullOrbit_basis k hF
  have : (fun u : lowerUni F => matRep (tensorRep (F := F) k (ones f) (ones f)) (u : SL(3, F))
      (hw k (ones f) (ones f))) = ⇑b := funext fun u => (hb u).symm
  rw [this]
  exact b.span_eq

theorem fullCoords_li (hF : Fintype.card F = 2 ^ f) :
    LinearIndependent k (fun x : TIdx f (ones f) (ones f) => fun u : lowerUni F =>
      ((tensorRep (F := F) k (ones f) (ones f) (u : SL(3, F))).mulVec
        (hw k (ones f) (ones f))) x) :=
  coords_linearIndependent_of_span (tensorRep (F := F) k (ones f) (ones f)) (lowerUni F)
    (hw k (ones f) (ones f)) (fullOrbit_span k hF)

@[expose] def locEmb : (a b : Bool) → Fin (locDim a b) → Fin 8
  | false, false => fun _ => 0
  | true, false => fun j => Fin.castLE (by decide) j
  | false, true => fun j => ![4, 3, 0] j
  | true, true => fun j => j

omit [Fintype F] [CharP F 2] in
theorem locCoord_emb (a b : Bool) (j : Fin (locDim a b)) (x y z : F) :
    locCoord a b j x y z = locCoord true true (locEmb a b j) x y z := by
  cases a <;> cases b
  · simp [locEmb, locCoord]
  · obtain ⟨j, hj⟩ := j
    have hj' : j < 3 := hj
    interval_cases j <;> rfl
  · obtain ⟨j, hj⟩ := j
    have hj' : j < 3 := hj
    interval_cases j <;> rfl
  · rfl

theorem locEmb_injective (a b : Bool) : Function.Injective (locEmb a b) := by
  cases a <;> cases b
  · intro i j _
    exact fin_locDim_ff i j
  · have hinj : Function.Injective (![4, 3, 0] : Fin 3 → Fin 8) := by decide
    exact hinj
  · intro i j h
    exact Fin.castLE_injective (by decide) h
  · intro i j h
    exact h

@[expose] def embIdx (a b : Fin f → Bool) : TIdx f a b → TIdx f (ones f) (ones f) :=
  fun x' i => locEmb (a i) (b i) (x' i)

theorem embIdx_injective (a b : Fin f → Bool) : Function.Injective (embIdx a b) := by
  intro x y h
  funext i
  exact locEmb_injective (a i) (b i) (congrFun h i)

omit [Fintype F] in
theorem coord_eq_emb (a b : Fin f → Bool) (x' : TIdx f a b) (u : lowerUni F) :
    ((tensorRep (F := F) k a b (u : SL(3, F))).mulVec (hw k a b)) x' =
      ((tensorRep (F := F) k (ones f) (ones f) (u : SL(3, F))).mulVec
        (hw k (ones f) (ones f))) (embIdx a b x') := by
  obtain ⟨x, y, z, hu⟩ := mem_lowerUni.mp u.2
  rw [hu, tensorRep_u3_orbit, tensorRep_u3_orbit]
  exact Finset.prod_congr rfl (fun i _ => by rw [locCoord_emb]; rfl)

theorem mixed_span (hF : Fintype.card F = 2 ^ f) (a b : Fin f → Bool) :
    Submodule.span k (Set.range fun u : lowerUni F =>
      matRep (tensorRep (F := F) k a b) (u : SL(3, F)) (hw k a b)) = ⊤ := by
  refine span_orbit_eq_top_of_coords _ _ _ ?_
  have h := (fullCoords_li k hF).comp (embIdx a b) (embIdx_injective a b)
  convert h using 1
  funext x' u
  exact coord_eq_emb k a b x' u

end Orbit

end CFSG.QuasithinUnique.Setup.X7a
