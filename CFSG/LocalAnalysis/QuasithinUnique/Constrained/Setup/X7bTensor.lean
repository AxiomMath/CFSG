module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aTensor
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bLower
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpOuter

public section

namespace CFSG.QuasithinUnique.Setup.X7b

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.QuasithinUnique.Setup.X7
open CFSG.QuasithinUnique.Setup.X7a (kron kron_apply kron_mul kron_one kron_transpose
  sum_pow_card_sub_one sum_add_mul_pow)

section Defs

variable {F : Type} [Field F] [CharP F 2] [Finite F] (k : Type*) [Field k] [Algebra F k]

@[expose] noncomputable def natRepS (i : ℕ) : antiSp F →* Matrix (Fin 4) (Fin 4) k where
  toFun g := (glMat (((minorAut F ^ i) g : antiSp F) : GL (Fin 4) F)).map (algebraMap F k)
  map_one' := by
    ext a b
    simp [Matrix.one_apply, apply_ite (algebraMap F k)]
  map_mul' g h := by
    rw [map_mul, ← Matrix.map_mul]
    rfl

theorem natRepS_apply (i : ℕ) (g : antiSp F) :
    natRepS k i g = (glMat (((minorAut F ^ i) g : antiSp F) : GL (Fin 4) F)).map (algebraMap F k) :=
  rfl

@[expose] noncomputable def tensorRepS (A : Finset ℕ) :
    antiSp F →* Matrix (A → Fin 4) (A → Fin 4) k where
  toFun g := kron (fun i : A => natRepS k (i : ℕ) g)
  map_one' := by
    simp only [map_one]
    exact kron_one
  map_mul' g h := by
    simp only [map_mul]
    exact kron_mul _ _

theorem tensorRepS_apply (A : Finset ℕ) (g : antiSp F) (x' x : A → Fin 4) :
    tensorRepS k A g x' x = ∏ i : A, natRepS k (i : ℕ) g (x' i) (x i) := rfl

@[expose] def hwS (A : Finset ℕ) : (A → Fin 4) → k := Pi.single (fun _ => 0) 1

theorem hwS_ne_zero (A : Finset ℕ) : hwS k A ≠ 0 := by
  intro h
  have := congrFun h (fun _ => 0)
  simp [hwS] at this

theorem tensorRepS_mulVec_hwS (A : Finset ℕ) (g : antiSp F) (x : A → Fin 4) :
    ((tensorRepS k A g).mulVec (hwS k A)) x = ∏ i : A, natRepS k (i : ℕ) g (x i) 0 := by
  rw [hwS, Matrix.mulVec_single_one, Matrix.col_apply, tensorRepS_apply]

end Defs

section Powers

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem minorAut_apply (g : antiSp K) : minorAut K g = minorHom K g := rfl

theorem minorAut_pow_succ (i : ℕ) (g : antiSp K) :
    (minorAut K ^ (i + 1)) g = (minorAut K ^ i) (minorHom K g) := by
  rw [pow_succ, MulAut.mul_apply, minorAut_apply]

theorem minorAut_pow_two (g : antiSp K) : (minorAut K ^ 2) g = frobHom K g := by
  rw [pow_two, MulAut.mul_apply, minorAut_apply, minorAut_apply, minorHom_minorHom]

theorem minorAut_pow_two_mul_lowUSp (j : ℕ) (a b c d : K) :
    (minorAut K ^ (2 * j)) (lowUSp a b c d) =
      lowUSp (a ^ 2 ^ j) (b ^ 2 ^ j) (c ^ 2 ^ j) (d ^ 2 ^ j) := by
  induction j generalizing a b c d with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, minorAut_pow_succ, minorAut_pow_succ,
      minorHom_minorHom_lowUSp, ih]
    simp only [← pow_mul, pow_succ 2 j, mul_comm (2 ^ j) 2]

theorem minorAut_pow_two_mul_add_one_lowUSp (j : ℕ) (a b c d : K) :
    (minorAut K ^ (2 * j + 1)) (lowUSp a b c d) =
      lowUSp (c ^ 2 ^ j) ((d + a * b + a ^ 2 * c) ^ 2 ^ j) ((a ^ 2) ^ 2 ^ j)
        ((b ^ 2 + a * b * c + c * d) ^ 2 ^ j) := by
  rw [minorAut_pow_succ, minorHom_lowUSp, minorAut_pow_two_mul_lowUSp]

theorem minorAut_pow_two_mul_dSp (j : ℕ) (s t : Kˣ) :
    (minorAut K ^ (2 * j)) (dSp s t) = dSp (s ^ 2 ^ j) (t ^ 2 ^ j) := by
  induction j generalizing s t with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, minorAut_pow_succ, minorAut_pow_succ,
      minorHom_minorHom_dSp, ih]
    simp only [← pow_mul, pow_succ 2 j, mul_comm (2 ^ j) 2]

theorem minorAut_pow_two_mul_add_one_dSp (j : ℕ) (s t : Kˣ) :
    (minorAut K ^ (2 * j + 1)) (dSp s t) = dSp ((s * t) ^ 2 ^ j) ((s * t⁻¹) ^ 2 ^ j) := by
  rw [minorAut_pow_succ, minorHom_dSp, minorAut_pow_two_mul_dSp]

theorem minorAut_pow_mem_upperUniSp (i : ℕ) {g : antiSp K} (hg : g ∈ upperUniSp K) :
    (minorAut K ^ i) g ∈ upperUniSp K := by
  induction i generalizing g with
  | zero => simpa using hg
  | succ i ih =>
    rw [minorAut_pow_succ]
    exact ih (minorHom_upperUniSp_le ⟨g, hg, rfl⟩)

end Powers

section Coordinates

variable {F : Type} [Field F] [CharP F 2] [Finite F] (k : Type*) [Field k] [Algebra F k]

@[expose] def colS (i : ℕ) (a b c d : F) : Fin 4 → F :=
  if i % 2 = 0 then ![1, a ^ 2 ^ (i / 2), b ^ 2 ^ (i / 2), d ^ 2 ^ (i / 2)]
  else ![1, c ^ 2 ^ (i / 2), (d + a * b + a ^ 2 * c) ^ 2 ^ (i / 2),
    (b ^ 2 + a * b * c + c * d) ^ 2 ^ (i / 2)]

theorem natRepS_lowUSp_col (i : ℕ) (a b c d : F) (x : Fin 4) :
    natRepS k i (lowUSp a b c d) x 0 = algebraMap F k (colS i a b c d x) := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
  · rw [natRepS_apply, minorAut_pow_two_mul_lowUSp]
    simp only [colS, Nat.mul_mod_right, ite_true, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    fin_cases x <;> simp [Matrix.map_apply, glMat_lowUSp, lowU]
  · rw [natRepS_apply, minorAut_pow_two_mul_add_one_lowUSp]
    have h1 : (2 * j + 1) % 2 = 1 := by omega
    have h2 : (2 * j + 1) / 2 = j := by omega
    simp only [colS, h1, h2, one_ne_zero, ite_false]
    fin_cases x <;> simp [Matrix.map_apply, glMat_lowUSp, lowU]

omit [CharP F 2] [Finite F] in
theorem colS_zero (i : ℕ) (a b c d : F) : colS i a b c d 0 = 1 := by
  unfold colS
  split_ifs <;> rfl

omit [CharP F 2] [Finite F] in
theorem colS_even_three (j : ℕ) (a b c d : F) : colS (2 * j) a b c d 3 = d ^ 2 ^ j := by
  simp [colS, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

omit [CharP F 2] [Finite F] in
theorem colS_odd_three (j : ℕ) (a b c d : F) :
    colS (2 * j + 1) a b c d 3 = (b ^ 2 + a * b * c + c * d) ^ 2 ^ j := by
  have h1 : (2 * j + 1) % 2 = 1 := by omega
  have h2 : (2 * j + 1) / 2 = j := by omega
  simp [colS, h1, h2]

end Coordinates

section Sums

@[to_additive]
theorem prod_range_two_mul {M : Type*} [CommMonoid M] (g : ℕ → M) (n : ℕ) :
    ∏ i ∈ Finset.range (2 * n), g i = ∏ j ∈ Finset.range n, (g (2 * j) * g (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ,
      Finset.prod_range_succ, ih, mul_assoc]

theorem prod_pow_two_pow {M : Type*} [CommMonoid M] (f : ℕ) (x : M) :
    ∏ j ∈ Finset.range f, x ^ 2 ^ j = x ^ (2 ^ f - 1) := by
  rw [Finset.prod_pow_eq_pow_sum, Nat.geomSum_eq (le_refl 2)]
  simp

theorem prod_ite_pow {M : Type*} [CommMonoid M] (f : ℕ) (P : ℕ → Prop) [DecidablePred P] (x : M) :
    ∏ j ∈ Finset.range f, (if P j then x ^ 2 ^ j else 1) =
      x ^ ∑ j ∈ Finset.range f, (if P j then 2 ^ j else 0) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  split_ifs <;> simp

variable (F : Type) [Field F] [Fintype F]

theorem sum_norm_poly :
    ∑ p : F × F × F × F,
      (p.2.2.2 * (p.2.1 ^ 2 + p.1 * p.2.1 * p.2.2.1 + p.2.2.1 * p.2.2.2)) ^
        (Fintype.card F - 1) = 1 := by
  classical
  have key : ∀ b c d : F, ∑ a : F, (d * (b ^ 2 + a * b * c + c * d)) ^ (Fintype.card F - 1) =
      -(d ^ (Fintype.card F - 1) * (b * c) ^ (Fintype.card F - 1)) := by
    intro b c d
    have e : ∀ a : F, (d * (b ^ 2 + a * b * c + c * d)) ^ (Fintype.card F - 1) =
        d ^ (Fintype.card F - 1) * ((b ^ 2 + c * d) + (b * c) * a) ^ (Fintype.card F - 1) :=
      fun a => by rw [← mul_pow]; congr 1; ring
    simp_rw [e]
    rw [← Finset.mul_sum, X7a.sum_add_mul_pow F (b ^ 2 + c * d) (b * c)]
    ring
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun q _ => key q.1 q.2.1 q.2.2)]
  simp only [Fintype.sum_prod_type, Finset.sum_neg_distrib, mul_pow, ← Finset.mul_sum,
    ← Finset.sum_mul, X7a.sum_pow_card_sub_one F]
  ring

end Sums

section Orbit

variable {F : Type} [Field F] [CharP F 2] [Fintype F] (k : Type*) [Field k] [Algebra F k]
  [CharP k 2] {f : ℕ}

noncomputable instance instFintypeLowerUniSp : Fintype (lowerUniSp F) := Fintype.ofFinite _

omit [CharP k 2] in
theorem coeff_lowUSp (hF : Fintype.card F = 2 ^ f) (a b c d : F) :
    ((tensorRepS k (Finset.range (2 * f)) (lowUSp a b c d)).mulVec
        (hwS k (Finset.range (2 * f)))) (fun _ => 3) =
      algebraMap F k ((d * (b ^ 2 + a * b * c + c * d)) ^ (Fintype.card F - 1)) := by
  rw [tensorRepS_mulVec_hwS]
  simp_rw [natRepS_lowUSp_col]
  rw [Finset.prod_coe_sort (Finset.range (2 * f)) (fun i => algebraMap F k (colS i a b c d 3)),
    ← map_prod, prod_range_two_mul]
  congr 1
  have h1 : ∀ j : ℕ, colS (2 * j) a b c d 3 * colS (2 * j + 1) a b c d 3 =
      (d * (b ^ 2 + a * b * c + c * d)) ^ 2 ^ j := fun j => by
    rw [colS_even_three, colS_odd_three, ← mul_pow]
  rw [Finset.prod_congr rfl (fun j _ => h1 j), prod_pow_two_pow, hF]

omit [CharP k 2] in
theorem norm_coeff_full (hF : Fintype.card F = 2 ^ f) :
    ∑ g : lowerUniSp F, ((tensorRepS k (Finset.range (2 * f)) (g : antiSp F)).mulVec
      (hwS k (Finset.range (2 * f)))) (fun _ => 3) = 1 := by
  classical
  rw [← (Equiv.ofBijective _ (lowUMap_bijective (K := F))).sum_comp]
  have h1 : ∀ p : F × F × F × F,
      ((tensorRepS k (Finset.range (2 * f))
        (((Equiv.ofBijective _ (lowUMap_bijective (K := F))) p : lowerUniSp F) : antiSp F)).mulVec
        (hwS k (Finset.range (2 * f)))) (fun _ => 3) =
      algebraMap F k ((p.2.2.2 * (p.2.1 ^ 2 + p.1 * p.2.1 * p.2.2.1 + p.2.2.1 * p.2.2.2)) ^
        (Fintype.card F - 1)) := fun p => coeff_lowUSp k hF p.1 p.2.1 p.2.2.1 p.2.2.2
  simp_rw [h1]
  rw [← map_sum, sum_norm_poly F, map_one]

omit [Algebra F k] [CharP k 2] in
theorem finrank_full (hF : Fintype.card F = 2 ^ f) :
    Module.finrank k ((Finset.range (2 * f) → Fin 4) → k) = Fintype.card (lowerUniSp F) := by
  have hcard : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fun, Fintype.card_coe, Finset.card_range,
    Fintype.card_fin, ← Nat.card_eq_fintype_card, card_lowerUniSp, hcard, ← pow_mul,
    show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  ring_nf

theorem fullOrbit_basis (hF : Fintype.card F = 2 ^ f) :
    ∃ b : Module.Basis (lowerUniSp F) k ((Finset.range (2 * f) → Fin 4) → k), ∀ u : lowerUniSp F,
      b u = (tensorRepS k (Finset.range (2 * f)) (u : antiSp F)).mulVec
        (hwS k (Finset.range (2 * f))) := by
  classical
  let T := tensorRepS (F := F) k (Finset.range (2 * f))
  let ρ : lowerUniSp F →* (((Finset.range (2 * f) → Fin 4) → k) →ₗ[k] ((Finset.range (2 * f) → Fin 4) → k)) :=
    (matRep T).comp (lowerUniSp F).subtype
  have hcard : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  have hP : IsPGroup 2 (lowerUniSp F) := isPGroup_lowerUniSp hcard
  have hv : ∑ g : lowerUniSp F, ρ g (hwS k (Finset.range (2 * f))) ≠ 0 := by
    intro h
    have h2 := norm_coeff_full k hF
    have h3 : ∑ g : lowerUniSp F, ((tensorRepS k (Finset.range (2 * f)) (g : antiSp F)).mulVec
        (hwS k (Finset.range (2 * f)))) (fun _ => 3) = 0 := by
      have := congrFun h (fun _ => 3)
      rw [Finset.sum_apply] at this
      exact this
    exact zero_ne_one (h3.symm.trans h2)
  obtain ⟨b, hb, -, -⟩ := orbit_regular_of_norm_ne_zero k Nat.prime_two hP ρ
    (hwS k (Finset.range (2 * f))) hv (finrank_full k hF)
  exact ⟨b, fun u => by rw [hb]; rfl⟩

theorem fullOrbit_span (hF : Fintype.card F = 2 ^ f) :
    Submodule.span k (Set.range fun u : lowerUniSp F =>
      matRep (tensorRepS k (Finset.range (2 * f))) (u : antiSp F)
        (hwS k (Finset.range (2 * f)))) = ⊤ := by
  obtain ⟨b, hb⟩ := fullOrbit_basis k hF
  have : (fun u : lowerUniSp F => matRep (tensorRepS k (Finset.range (2 * f))) (u : antiSp F)
      (hwS k (Finset.range (2 * f)))) = ⇑b := funext fun u => (hb u).symm
  rw [this]
  exact b.span_eq

theorem fullCoords_li (hF : Fintype.card F = 2 ^ f) :
    LinearIndependent k (fun x : (Finset.range (2 * f) → Fin 4) => fun u : lowerUniSp F =>
      ((tensorRepS k (Finset.range (2 * f)) (u : antiSp F)).mulVec
        (hwS k (Finset.range (2 * f)))) x) :=
  coords_linearIndependent_of_span (tensorRepS k (Finset.range (2 * f))) (lowerUniSp F)
    (hwS k (Finset.range (2 * f))) (fullOrbit_span k hF)

@[expose] def extIdx (A : Finset ℕ) (x : A → Fin 4) : ℕ → Fin 4 :=
  fun i => if h : i ∈ A then x ⟨i, h⟩ else 0

@[expose] def embIdx (A Ω : Finset ℕ) (x : A → Fin 4) : Ω → Fin 4 := fun i => extIdx A x i

theorem embIdx_injective {A Ω : Finset ℕ} (hA : A ⊆ Ω) : Function.Injective (embIdx A Ω) := by
  intro x y h
  funext i
  have := congrFun h ⟨i, hA i.2⟩
  simpa [embIdx, extIdx, i.2] using this

omit [CharP k 2] in
theorem coord_eq_emb {A Ω : Finset ℕ} (hA : A ⊆ Ω) (x : A → Fin 4) (u : lowerUniSp F) :
    ((tensorRepS k A (u : antiSp F)).mulVec (hwS k A)) x =
      ((tensorRepS k Ω (u : antiSp F)).mulVec (hwS k Ω)) (embIdx A Ω x) := by
  obtain ⟨a, b, c, d, hu⟩ := u.2
  rw [tensorRepS_mulVec_hwS, tensorRepS_mulVec_hwS]
  have h1 : ∏ i : A, natRepS k (i : ℕ) (u : antiSp F) (x i) 0 =
      ∏ i ∈ A, natRepS k i (u : antiSp F) (extIdx A x i) 0 := by
    rw [← Finset.prod_coe_sort A (fun i => natRepS k i (u : antiSp F) (extIdx A x i) 0)]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [extIdx, i.2]
  have h2 : ∏ i : Ω, natRepS k (i : ℕ) (u : antiSp F) (embIdx A Ω x i) 0 =
      ∏ i ∈ Ω, natRepS k i (u : antiSp F) (extIdx A x i) 0 :=
    Finset.prod_coe_sort Ω (fun i => natRepS k i (u : antiSp F) (extIdx A x i) 0)
  rw [h1, h2]
  refine Finset.prod_subset hA fun i _ hiA => ?_
  have hu' : (u : antiSp F) = lowUSp a b c d := hu
  rw [hu', natRepS_lowUSp_col]
  simp [extIdx, hiA, colS_zero]

theorem mixed_span (hF : Fintype.card F = 2 ^ f) {A : Finset ℕ} (hA : A ⊆ Finset.range (2 * f)) :
    Submodule.span k (Set.range fun u : lowerUniSp F =>
      matRep (tensorRepS (F := F) k A) (u : antiSp F) (hwS k A)) = ⊤ := by
  refine span_orbit_eq_top_of_coords _ _ _ ?_
  have h := (fullCoords_li k hF).comp (embIdx A (Finset.range (2 * f))) (embIdx_injective hA)
  convert h using 1
  funext x u
  exact coord_eq_emb k hA x u

end Orbit

section Dual

variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem glMat_inv_transpose (h : antiSp K) :
    (glMat (((h⁻¹ : antiSp K)) : GL (Fin 4) K))ᵀ =
      minorJ K * glMat (h : GL (Fin 4) K) * minorJ K := by
  have hJ : (glMat (h : GL (Fin 4) K))ᵀ * minorJ K * glMat (h : GL (Fin 4) K) = minorJ K :=
    mem_antiSp.mp h.2
  have hN' : glMat (h : GL (Fin 4) K) * glMat (((h⁻¹ : antiSp K)) : GL (Fin 4) K) = 1 :=
    (h : GL (Fin 4) K).mul_inv
  have hN2 : glMat (((h⁻¹ : antiSp K)) : GL (Fin 4) K) =
      minorJ K * (glMat (h : GL (Fin 4) K))ᵀ * minorJ K := by
    calc glMat (((h⁻¹ : antiSp K)) : GL (Fin 4) K)
        = (minorJ K * minorJ K) * glMat (((h⁻¹ : antiSp K)) : GL (Fin 4) K) := by
          rw [minorJ_mul_self, Matrix.one_mul]
      _ = minorJ K * ((glMat (h : GL (Fin 4) K))ᵀ * minorJ K * glMat (h : GL (Fin 4) K)) *
            glMat (((h⁻¹ : antiSp K)) : GL (Fin 4) K) := by
          rw [hJ, Matrix.mul_assoc]
      _ = minorJ K * (glMat (h : GL (Fin 4) K))ᵀ * minorJ K *
            (glMat (h : GL (Fin 4) K) * glMat (((h⁻¹ : antiSp K)) : GL (Fin 4) K)) := by
          simp only [Matrix.mul_assoc]
      _ = minorJ K * (glMat (h : GL (Fin 4) K))ᵀ * minorJ K := by rw [hN', Matrix.mul_one]
  rw [hN2]
  simp [Matrix.transpose_mul, minorJ_transpose, Matrix.mul_assoc]

end Dual

section Dual2

variable {F : Type} [Field F] [CharP F 2] [Finite F] (k : Type*) [Field k] [Algebra F k]

variable (F) in
@[expose] def JkS : Matrix (Fin 4) (Fin 4) k := (minorJ F).map (algebraMap F k)

omit [CharP F 2] [Finite F] in
theorem JkS_mul_self : JkS F k * JkS F k = 1 := by
  rw [JkS, ← Matrix.map_mul, minorJ_mul_self]
  ext a b
  simp [Matrix.one_apply, apply_ite (algebraMap F k)]

theorem natRepS_inv_transpose (i : ℕ) (g : antiSp F) :
    (natRepS k i g⁻¹)ᵀ = JkS F k * natRepS k i g * JkS F k := by
  rw [natRepS_apply, natRepS_apply, map_inv, ← Matrix.transpose_map, glMat_inv_transpose,
    JkS, Matrix.map_mul, Matrix.map_mul]

variable (F) in
@[expose] def JtS (A : Finset ℕ) : Matrix (A → Fin 4) (A → Fin 4) k :=
  kron (fun _ : A => JkS F k)

omit [CharP F 2] [Finite F] in
theorem JtS_mul_self (A : Finset ℕ) : JtS F k A * JtS F k A = 1 := by
  rw [JtS, ← kron_mul]
  simp only [JkS_mul_self]
  exact kron_one

theorem tensorRepS_inv_transpose (A : Finset ℕ) (g : antiSp F) :
    (tensorRepS k A g⁻¹)ᵀ = JtS F k A * tensorRepS k A g * JtS F k A := by
  change (kron (fun i : A => natRepS k (i : ℕ) g⁻¹))ᵀ =
    kron (fun _ : A => JkS F k) * kron (fun i : A => natRepS k (i : ℕ) g) *
      kron (fun _ : A => JkS F k)
  rw [kron_transpose, ← kron_mul, ← kron_mul]
  congr 1
  funext i
  exact natRepS_inv_transpose k _ g

end Dual2

theorem hline_of_selfdual {G κ k : Type*} [Group G] [Field k] [Fintype κ] [DecidableEq κ]
    (R : G →* Matrix κ κ k) (Pm : Subgroup G) (Jm : Matrix κ κ k) (hJ : Jm * Jm = 1)
    (hdual : ∀ g, (R g⁻¹)ᵀ = Jm * R g * Jm) (v : κ → k)
    (hspan : Submodule.span k (Set.range fun u : Pm => matRep R u v) = ⊤) :
    ∃ n ∈ fixedSub (matRep R) Pm, ∀ w ∈ fixedSub (matRep R) Pm, ∃ c : k, w = c • n := by
  refine hline_of_cocyclic R Pm (Jm.mulVec v) ?_
  have h1 : ∀ u : Pm, (R ((u : G)⁻¹))ᵀ.mulVec (Jm.mulVec v) = Jm.mulVec ((R u).mulVec v) := by
    intro u
    rw [hdual, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hJ,
      Matrix.mul_one, ← Matrix.mulVec_mulVec]
  have hsurj : Function.Surjective (Matrix.mulVecLin Jm) := fun y =>
    ⟨Jm.mulVec y, by simp [Matrix.mulVec_mulVec, hJ]⟩
  have h2 := congrArg (Submodule.map (Matrix.mulVecLin Jm)) hspan
  rw [Submodule.map_span, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj] at h2
  convert h2 using 2
  ext y
  simp only [Set.mem_range, Set.mem_image, h1]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨matRep R u v, ⟨u, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, by rw [matRep_apply]; rfl⟩

section Irred

variable {F : Type} [Field F] [CharP F 2] [Fintype F] (k : Type*) [Field k] [Algebra F k]
  [CharP k 2] {f : ℕ}

omit [CharP k 2] in
theorem natRepS_upper_col {h : antiSp F} (hh : h ∈ upperUniSp F) (i : ℕ) (y : Fin 4) :
    natRepS k i h y 0 = if y = 0 then 1 else 0 := by
  have hm := (mem_upperUniSp_iff _).mp (minorAut_pow_mem_upperUniSp i hh)
  rw [natRepS_apply, Matrix.map_apply]
  by_cases hy : y = 0
  · subst hy
    simp [hm.2 0]
  · have hpos : 0 < y := Fin.pos_iff_ne_zero.mpr hy
    simp [hy, hm.1 y 0 hpos]

omit [CharP k 2] in
theorem tensorRepS_upper_fixed (A : Finset ℕ) {h : antiSp F} (hh : h ∈ upperUniSp F) :
    (tensorRepS k A h).mulVec (hwS k A) = hwS k A := by
  funext x
  rw [tensorRepS_mulVec_hwS]
  simp_rw [natRepS_upper_col k hh]
  rw [Finset.prod_boole]
  simp [hwS, Pi.single_apply, funext_iff]

@[expose] def dChar (i : ℕ) (s t : Fˣ) : Fˣ :=
  if i % 2 = 0 then s ^ 2 ^ (i / 2) else (s * t) ^ 2 ^ (i / 2)

theorem glMat_dSp {K : Type} [Field K] [CharP K 2] (s t : Kˣ) :
    glMat ((dSp s t : antiSp K) : GL (Fin 4) K) = dmat (s : K) (t : K) := rfl

omit [CharP k 2] in
theorem natRepS_dSp_col (i : ℕ) (s t : Fˣ) (y : Fin 4) :
    natRepS k i (dSp s t) y 0 =
      if y = 0 then algebraMap F k ((dChar i s t : Fˣ) : F) else 0 := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
  · rw [natRepS_apply, minorAut_pow_two_mul_dSp]
    simp only [dChar, Nat.mul_mod_right, ite_true, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    fin_cases y <;> simp [Matrix.map_apply, glMat_dSp, dmat]
  · rw [natRepS_apply, minorAut_pow_two_mul_add_one_dSp]
    have h1 : (2 * j + 1) % 2 = 1 := by omega
    have h2 : (2 * j + 1) / 2 = j := by omega
    simp only [dChar, h1, h2, one_ne_zero, ite_false]
    fin_cases y <;> simp [Matrix.map_apply, glMat_dSp, dmat]

omit [CharP k 2] in
theorem tensorRepS_dSp_hwS (A : Finset ℕ) (s t : Fˣ) :
    (tensorRepS k A (dSp s t)).mulVec (hwS k A) =
      (∏ i : A, algebraMap F k ((dChar (i : ℕ) s t : Fˣ) : F)) • hwS k A := by
  funext x
  rw [tensorRepS_mulVec_hwS]
  simp_rw [natRepS_dSp_col]
  rw [Finset.prod_ite_zero]
  by_cases hx : x = fun _ => 0
  · subst hx
    simp [hwS]
  · have h' : ¬ ∀ i ∈ (Finset.univ : Finset A), x i = 0 := fun h =>
      hx (funext fun i => h i (Finset.mem_univ i))
    simp only [h', ite_false]
    simp [hwS, hx]

@[expose] def mIdx (f : ℕ) (A : Finset ℕ) : ℕ :=
  ∑ j ∈ Finset.range f, if 2 * j ∈ A then 2 ^ j else 0

@[expose] def nIdx (f : ℕ) (A : Finset ℕ) : ℕ :=
  ∑ j ∈ Finset.range f, if 2 * j + 1 ∈ A then 2 ^ j else 0

omit [CharP k 2] [Fintype F] [CharP F 2] in
theorem prod_dChar {A : Finset ℕ} (hA : A ⊆ Finset.range (2 * f)) (s t : Fˣ) :
    ∏ i : A, algebraMap F k ((dChar (i : ℕ) s t : Fˣ) : F) =
      algebraMap F k (s : F) ^ (mIdx f A + nIdx f A) * algebraMap F k (t : F) ^ nIdx f A := by
  classical
  rw [Finset.prod_coe_sort A (fun i => algebraMap F k ((dChar i s t : Fˣ) : F))]
  have e1 : ∏ i ∈ A, algebraMap F k ((dChar i s t : Fˣ) : F) =
      ∏ i ∈ Finset.range (2 * f),
        (if i ∈ A then algebraMap F k ((dChar i s t : Fˣ) : F) else 1) := by
    rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hA]
  rw [e1, prod_range_two_mul]
  have h1 : ∀ j : ℕ, ((if 2 * j ∈ A then algebraMap F k ((dChar (2 * j) s t : Fˣ) : F) else 1) *
      if 2 * j + 1 ∈ A then algebraMap F k ((dChar (2 * j + 1) s t : Fˣ) : F) else 1) =
      (if 2 * j ∈ A then (algebraMap F k (s : F)) ^ 2 ^ j else 1) *
        if 2 * j + 1 ∈ A then (algebraMap F k ((s : F) * (t : F))) ^ 2 ^ j else 1 := by
    intro j
    have e0 : (dChar (2 * j) s t : Fˣ) = s ^ 2 ^ j := by
      simp [dChar, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    have e1 : (dChar (2 * j + 1) s t : Fˣ) = (s * t) ^ 2 ^ j := by
      have h1 : (2 * j + 1) % 2 = 1 := by omega
      have h2 : (2 * j + 1) / 2 = j := by omega
      simp [dChar, h1, h2]
    simp [e0, e1, map_pow, map_mul]
  rw [Finset.prod_congr rfl (fun j _ => h1 j), Finset.prod_mul_distrib, prod_ite_pow f (fun j => 2 * j ∈ A),
    prod_ite_pow f (fun j => 2 * j + 1 ∈ A), mIdx, nIdx, map_mul, mul_pow]
  ring

omit [CharP k 2] in
theorem finrank_tensorRepS (A : Finset ℕ) :
    Module.finrank k ((A → Fin 4) → k) = 4 ^ A.card := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]

omit [CharP k 2] in
theorem finrank_tensorRepS_empty :
    Module.finrank k (((∅ : Finset ℕ) → Fin 4) → k) = 1 := by
  rw [finrank_tensorRepS]
  simp

theorem tensorRepS_fixed_irreducible (hF : Fintype.card F = 2 ^ f) {A : Finset ℕ}
    (hA : A ⊆ Finset.range (2 * f)) :
    fixedSub (matRep (tensorRepS (F := F) k A)) (upperUniSp F) = Submodule.span k {hwS k A} ∧
      (matRep (tensorRepS (F := F) k A)).IsIrreducible := by
  have hcard : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  have hPp : IsPGroup 2 (upperUniSp F) := isPGroup_upperUniSp hcard
  have hspan := mixed_span k hF hA
  refine fixedSub_eq_span_and_irreducible k Nat.prime_two (matRep (tensorRepS (F := F) k A))
    (lowerUniSp F) (upperUniSp F) hPp Jsp (fun u hu => ⟨u, hu, rfl⟩) (hwS k A) (hwS_ne_zero k A)
    ?_ hspan ?_
  · intro h hh
    exact tensorRepS_upper_fixed k A hh
  · exact hline_of_selfdual (tensorRepS (F := F) k A) (lowerUniSp F) (JtS F k A) (JtS_mul_self k A)
      (tensorRepS_inv_transpose k A) (hwS k A) hspan

omit [CharP k 2] in
theorem natRepS_add_two (i : ℕ) (g : antiSp F) :
    natRepS k (i + 2) g = (natRepS k i g).map fun x => x ^ 2 := by
  rw [natRepS_apply, natRepS_apply, add_comm, pow_add, MulAut.mul_apply, minorAut_pow_two,
    glMat_frobHom]
  ext a b
  simp [Matrix.map_apply, map_pow]

omit [CharP k 2] in
theorem natRepS_add_two_mul (hF : Fintype.card F = 2 ^ f) (i : ℕ) (g : antiSp F) :
    natRepS k (i + 2 * f) g = natRepS k i g := by
  have hcard : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  have hf : 1 ≤ f := by
    by_contra h
    have h0 : f = 0 := by omega
    have := Fintype.one_lt_card (α := F)
    rw [hF, h0] at this
    simp at this
  have h1 : minorAut F ^ (2 * f) = 1 := by
    have := pow_orderOf_eq_one (minorAut F)
    rwa [orderOf_minorAut hf hcard] at this
  rw [natRepS_apply, natRepS_apply, pow_add, h1, mul_one]

omit [CharP k 2] in
theorem tensorRepS_empty (g : antiSp F) : tensorRepS k (∅ : Finset ℕ) g = 1 := by
  ext x' x
  have hx : x' = x := funext fun i => (Finset.notMem_empty _ i.2).elim
  subst hx
  simp [tensorRepS_apply]

omit [CharP k 2] in
theorem fundamental_tensor_data (hF : Fintype.card F = 2 ^ f) :
    (∀ (i : ℕ) (g h : antiSp F), natRepS k i (g * h) = natRepS k i g * natRepS k i h) ∧
      (∀ i : ℕ, natRepS (F := F) k i 1 = 1) ∧
      (∀ g : antiSp F, natRepS k 0 g = (glMat (g : GL (Fin 4) F)).map (algebraMap F k)) ∧
      (∀ (i : ℕ) (g : antiSp F), natRepS k (i + 2 * f) g = natRepS k i g) ∧
      (∀ (i : ℕ) (g : antiSp F), natRepS k (i + 2) g = (natRepS k i g).map fun x => x ^ 2) ∧
      (∀ (A : Finset ℕ) (g h : antiSp F),
        tensorRepS k A (g * h) = tensorRepS k A g * tensorRepS k A h) ∧
      (∀ g : antiSp F, tensorRepS k (∅ : Finset ℕ) g = 1) ∧
      (∀ A : Finset ℕ, Module.finrank k ((A → Fin 4) → k) = 4 ^ A.card) :=
  ⟨fun i g h => map_mul _ g h, fun i => map_one _, fun g => by simp [natRepS_apply],
    natRepS_add_two_mul k hF, natRepS_add_two k, fun A g h => map_mul _ g h,
    tensorRepS_empty k, finrank_tensorRepS k⟩

theorem full_squarefree_tensor_absolutely_irreducible (hF : Fintype.card F = 2 ^ f) :
    Module.finrank k ((Finset.range (2 * f) → Fin 4) → k) = Nat.card F ^ 4 ∧
      ∑ g : lowerUniSp F, ((tensorRepS k (Finset.range (2 * f)) (g : antiSp F)).mulVec
        (hwS k (Finset.range (2 * f)))) (fun _ => 3) = 1 ∧
      (∃ b : Module.Basis (lowerUniSp F) k ((Finset.range (2 * f) → Fin 4) → k), ∀ u : lowerUniSp F,
        b u = (tensorRepS k (Finset.range (2 * f)) (u : antiSp F)).mulVec
          (hwS k (Finset.range (2 * f)))) ∧
      fixedSub (matRep (tensorRepS (F := F) k (Finset.range (2 * f)))) (upperUniSp F) =
        Submodule.span k {hwS k (Finset.range (2 * f))} ∧
      (matRep (tensorRepS (F := F) k (Finset.range (2 * f)))).IsIrreducible := by
  have hcard : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  have h4 : Module.finrank k ((Finset.range (2 * f) → Fin 4) → k) = Nat.card F ^ 4 := by
    rw [finrank_tensorRepS, Finset.card_range, hcard, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num,
      ← pow_mul]
    ring_nf
  exact ⟨h4, norm_coeff_full k hF, fullOrbit_basis k hF,
    (tensorRepS_fixed_irreducible k hF (subset_refl _)).1,
    (tensorRepS_fixed_irreducible k hF (subset_refl _)).2⟩

theorem squarefree_tensor_fixed_line_and_character (hF : Fintype.card F = 2 ^ f) {A : Finset ℕ}
    (hA : A ⊆ Finset.range (2 * f)) :
    Module.finrank k ((A → Fin 4) → k) = 4 ^ A.card ∧
      (matRep (tensorRepS (F := F) k A)).IsIrreducible ∧
      fixedSub (matRep (tensorRepS (F := F) k A)) (upperUniSp F) = Submodule.span k {hwS k A} ∧
      ∀ s t : Fˣ, (tensorRepS (F := F) k A (dSp s t)).mulVec (hwS k A) =
        (algebraMap F k (s : F) ^ (mIdx f A + nIdx f A) * algebraMap F k (t : F) ^ nIdx f A) •
          hwS k A := by
  refine ⟨finrank_tensorRepS k A, (tensorRepS_fixed_irreducible k hF hA).2,
    (tensorRepS_fixed_irreducible k hF hA).1, fun s t => ?_⟩
  rw [tensorRepS_dSp_hwS, prod_dChar k hA]

end Irred

end CFSG.QuasithinUnique.Setup.X7b
