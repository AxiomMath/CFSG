module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsBridge
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataQuotient

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open scoped commutatorElement

section Refl

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [DecidableEq ι]

noncomputable def orthReflProd (Q : QuadraticForm K V) (e : ι → V) (s : Finset ι) : V →ₗ[K] V :=
  LinearMap.id - ∑ i ∈ s, LinearMap.smulRight ((Q (e i))⁻¹ • polarBilin Q (e i)) (e i)

theorem orthReflProd_apply (Q : QuadraticForm K V) (e : ι → V) (s : Finset ι) (v : V) :
    orthReflProd Q e s v = v - ∑ i ∈ s, ((Q (e i))⁻¹ * polar Q (e i) v) • e i := by
  simp [orthReflProd, LinearMap.sum_apply, smul_eq_mul]

variable {Q : QuadraticForm K V} {e : ι → V}

private theorem polar_orthReflProd (horth : ∀ i j, i ≠ j → polar Q (e i) (e j) = 0)
    (s : Finset ι) (i : ι) (v : V) :
    polar Q (e i) (orthReflProd Q e s v) = polar Q (e i) v -
      if i ∈ s then (Q (e i))⁻¹ * polar Q (e i) v * polar Q (e i) (e i) else 0 := by
  rw [orthReflProd_apply, polar_sub_right]
  congr 1
  rw [← polarBilin_apply_apply, map_sum]
  simp only [map_smul, polarBilin_apply_apply, smul_eq_mul]
  split_ifs with hi
  · rw [Finset.sum_eq_single_of_mem i hi fun j _ hji => by
      rw [horth i j (Ne.symm hji), mul_zero]]
  · exact Finset.sum_eq_zero fun j hj => by
      rw [horth i j (fun h => hi (h ▸ hj)), mul_zero]

theorem orthReflProd_comp (horth : ∀ i j, i ≠ j → polar Q (e i) (e j) = 0) {s t : Finset ι}
    (hst : Disjoint s t) :
    (orthReflProd Q e s).comp (orthReflProd Q e t) = orthReflProd Q e (s ∪ t) := by
  ext v
  rw [LinearMap.comp_apply, orthReflProd_apply Q e s, orthReflProd_apply Q e (s ∪ t),
    Finset.sum_union hst]
  have hs : ∀ i ∈ s, polar Q (e i) (orthReflProd Q e t v) = polar Q (e i) v := fun i hi => by
    rw [polar_orthReflProd horth, if_neg (Finset.disjoint_left.1 hst hi), sub_zero]
  rw [Finset.sum_congr rfl fun i hi => by rw [hs i hi], orthReflProd_apply]
  abel

theorem orthReflProd_comp_self (he : ∀ i, Q (e i) ≠ 0)
    (horth : ∀ i j, i ≠ j → polar Q (e i) (e j) = 0) (s : Finset ι) :
    (orthReflProd Q e s).comp (orthReflProd Q e s) = LinearMap.id := by
  ext v
  rw [LinearMap.comp_apply, LinearMap.id_apply, orthReflProd_apply Q e s (orthReflProd Q e s v)]
  have hs : ∀ i ∈ s, (Q (e i))⁻¹ * polar Q (e i) (orthReflProd Q e s v) =
      -((Q (e i))⁻¹ * polar Q (e i) v) := fun i hi => by
    rw [polar_orthReflProd horth, if_pos hi, polar_self, nsmul_eq_mul]
    field_simp [he i]
    ring
  rw [Finset.sum_congr rfl fun i hi => by rw [hs i hi], orthReflProd_apply]
  simp only [neg_smul, Finset.sum_neg_distrib]
  abel

end Refl

section Matrix

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

private noncomputable def reflGL (Q : QuadraticForm K (Fin d → K)) (f : Fin d → K)
    (hf : Q f ≠ 0) : GL (Fin d) K :=
  letI := invertibleOfNonzero hf
  glEquiv.symm (TauCeti.QuadraticMap.reflection Q f)

private theorem glEquiv_reflGL_apply (f : Fin d → K) (hf : Q f ≠ 0) (v : Fin d → K) :
    glEquiv (reflGL Q f hf) v = v - ((Q f)⁻¹ * polar Q f v) • f := by
  letI := invertibleOfNonzero hf
  rw [reflGL, MulEquiv.apply_symm_apply, TauCeti.QuadraticMap.reflection_apply, invOf_eq_inv]

private theorem reflGL_mem (f : Fin d → K) (hf : Q f ≠ 0) : reflGL Q f hf ∈ matrixIsometries Q := by
  letI := invertibleOfNonzero hf
  rw [mem_matrixIsometries_iff]
  intro v
  rw [matrixLinearEquiv_apply, ← glEquiv_apply, reflGL, MulEquiv.apply_symm_apply]
  exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1
    (TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q f) v

private theorem pair_eq_commutator (h2 : (2 : K) ≠ 0) {e e' : Fin d → K} (he' : Q e' ≠ 0)
    {c : K} (hc : c ≠ 0) (hQe : Q e = c ^ 2 * Q e') (hee' : polar Q e e' = 0)
    (hf : Q (e - c • e') ≠ 0) (hQe0 : Q e ≠ 0) (v : Fin d → K) :
    glEquiv ⁅reflGL Q e hQe0, reflGL Q (e - c • e') hf⁆ v =
      v - ((Q e)⁻¹ * polar Q e v) • e - ((Q e')⁻¹ * polar Q e' v) • e' := by
  set f := e - c • e' with hfdef
  set q := Q e' with hq
  set a := polar Q e v with ha
  set b := polar Q e' v with hb
  have he'e : polar Q e' e = 0 := by rw [polar_comm, hee']
  have hQf : Q f = 2 * c ^ 2 * q := by
    rw [hfdef, sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add ⇑Q, QuadraticMap.map_smul,
      polar_smul_right, hee', smul_zero, add_zero, hQe, smul_eq_mul]
    ring
  have hpee : polar Q e e = 2 * (c ^ 2 * q) := by rw [polar_self, nsmul_eq_mul, hQe]; ring
  have hpe'e' : polar Q e' e' = 2 * q := by rw [polar_self, nsmul_eq_mul, Nat.cast_ofNat]
  have hpef : polar Q e f = 2 * c ^ 2 * q := by
    rw [hfdef, polar_sub_right, polar_smul_right, hee', hpee, smul_zero, sub_zero]; ring
  have hpe'f : polar Q e' f = -(2 * c * q) := by
    rw [hfdef, polar_sub_right, polar_smul_right, he'e, hpe'e', smul_eq_mul]; ring
  have hpff : polar Q f f = 2 * Q f := by rw [polar_self, nsmul_eq_mul, Nat.cast_ofNat]
  have hpfe : polar Q f e = 2 * c ^ 2 * q := by rw [polar_comm, hpef]
  have hq0 : q ≠ 0 := he'
  have hpf : ∀ w, polar Q f w = polar Q e w - c * polar Q e' w := fun w => by
    rw [hfdef, polar_sub_left, polar_smul_left, smul_eq_mul]
  set v₁ := v - ((Q f)⁻¹ * polar Q f v) • f with hv₁
  have h1e : polar Q e v₁ = c * b := by
    rw [hv₁, polar_sub_right, polar_smul_right, hpef, hpf, hQf, smul_eq_mul]
    field_simp
    ring
  have h1f : polar Q f v₁ = -(a - c * b) := by
    rw [hv₁, polar_sub_right, polar_smul_right, hpff, hpf, smul_eq_mul, hQf]
    field_simp
    ring
  set v₂ := v₁ - ((Q e)⁻¹ * polar Q e v₁) • e with hv₂
  have h2e : polar Q e v₂ = -(c * b) := by
    rw [hv₂, polar_sub_right, polar_smul_right, h1e, hpee, hQe, smul_eq_mul]
    field_simp
    ring
  have h2f : polar Q f v₂ = -a - c * b := by
    rw [hv₂, polar_sub_right, polar_smul_right, h1f, h1e, hpfe, hQe, smul_eq_mul]
    field_simp
    ring
  set v₃ := v₂ - ((Q f)⁻¹ * polar Q f v₂) • f with hv₃
  have h3e : polar Q e v₃ = a := by
    rw [hv₃, polar_sub_right, polar_smul_right, h2e, h2f, hpef, hQf, smul_eq_mul]
    field_simp
    ring
  have hstep : glEquiv ⁅reflGL Q e hQe0, reflGL Q f hf⁆ v =
      v₃ - ((Q e)⁻¹ * polar Q e v₃) • e := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    have hinv : ∀ (g : Fin d → K) (hg : Q g ≠ 0), (glEquiv (reflGL Q g hg))⁻¹ =
        glEquiv (reflGL Q g hg) := fun g hg => by
      letI := invertibleOfNonzero hg
      rw [reflGL, MulEquiv.apply_symm_apply, TauCeti.QuadraticMap.reflection_inv]
    rw [hinv, hinv, glEquiv_reflGL_apply, glEquiv_reflGL_apply, glEquiv_reflGL_apply,
      glEquiv_reflGL_apply]
  rw [hstep, h3e, hv₃, hv₂, hv₁, h2f, h1e, hpf, hQf, hQe, hfdef]
  ext k
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

private theorem exists_isSquare_mul_of_three [Finite K] {x y z : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hz : z ≠ 0) : IsSquare (x * y) ∨ IsSquare (x * z) ∨ IsSquare (y * z) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have key : ∀ {a b : K}, a ≠ 0 → b ≠ 0 → quadraticChar K a = quadraticChar K b →
      IsSquare (a * b) := fun {a b} ha hb hab => by
    rw [← quadraticChar_one_iff_isSquare (mul_ne_zero ha hb), map_mul, hab]
    rcases quadraticChar_dichotomy hb with h | h <;> rw [h] <;> norm_num
  rcases quadraticChar_dichotomy hx with h1 | h1 <;>
    rcases quadraticChar_dichotomy hy with h2 | h2 <;>
    rcases quadraticChar_dichotomy hz with h3 | h3
  all_goals first
    | exact Or.inl (key hx hy (h1.trans h2.symm))
    | exact Or.inr (Or.inl (key hx hz (h1.trans h3.symm)))
    | exact Or.inr (Or.inr (key hy hz (h2.trans h3.symm)))

private noncomputable def reflProdGL {ι : Type*} [DecidableEq ι] (Q : QuadraticForm K (Fin d → K))
    {e : ι → (Fin d → K)} (he : ∀ i, Q (e i) ≠ 0)
    (horth : ∀ i j, i ≠ j → polar Q (e i) (e j) = 0) (s : Finset ι) : GL (Fin d) K :=
  glEquiv.symm (LinearEquiv.ofInvolutive (orthReflProd Q e s)
    (fun v => LinearMap.congr_fun (orthReflProd_comp_self he horth s) v))

section Prod

variable {ι : Type*} [DecidableEq ι] {e : ι → (Fin d → K)} (he : ∀ i, Q (e i) ≠ 0)
  (horth : ∀ i j, i ≠ j → polar Q (e i) (e j) = 0)

include he horth in
private theorem glEquiv_reflProdGL_apply (s : Finset ι) (v : Fin d → K) :
    glEquiv (reflProdGL Q he horth s) v = orthReflProd Q e s v := by
  rw [reflProdGL, MulEquiv.apply_symm_apply]
  rfl

include he horth in
private theorem reflProdGL_union {s t : Finset ι} (hst : Disjoint s t) :
    reflProdGL Q he horth (s ∪ t) = reflProdGL Q he horth s * reflProdGL Q he horth t := by
  apply glEquiv.injective
  rw [map_mul]
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, glEquiv_reflProdGL_apply, glEquiv_reflProdGL_apply,
    glEquiv_reflProdGL_apply, ← LinearMap.comp_apply, orthReflProd_comp horth hst]

include he horth in
private theorem reflProdGL_empty : reflProdGL Q he horth ∅ = 1 := by
  apply glEquiv.injective
  rw [map_one]
  refine LinearEquiv.ext fun v => ?_
  rw [glEquiv_reflProdGL_apply, orthReflProd_apply]
  simp

private theorem quad_sub_smul {e₁ e₂ : Fin d → K} (h12 : polar Q e₁ e₂ = 0) (c : K) :
    Q (e₁ - c • e₂) = Q e₁ + c ^ 2 * Q e₂ := by
  rw [sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add ⇑Q, QuadraticMap.map_smul,
    polar_smul_right, h12, smul_zero, add_zero, smul_eq_mul]
  ring

include he horth in
private theorem reflProdGL_pair_mem (h2 : (2 : K) ≠ 0) {i j : ι} (hij : i ≠ j)
    (hsq : IsSquare (Q (e i) * Q (e j))) : reflProdGL Q he horth {i, j} ∈ matrixDerived Q := by
  obtain ⟨b, hb⟩ := hsq
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact mul_ne_zero (he i) (he j) (by rw [hb, mul_zero])
  set c := b / Q (e j) with hcdef
  have hc : c ≠ 0 := div_ne_zero hb0 (he j)
  have hQe : Q (e i) = c ^ 2 * Q (e j) := by
    rw [hcdef]
    field_simp [he j]
    linear_combination hb
  have hf : Q (e i - c • e j) ≠ 0 := by
    rw [quad_sub_smul (horth i j hij), ← hQe, ← two_mul]
    exact mul_ne_zero h2 (he i)
  have hmem : ⁅reflGL Q (e i) (he i), reflGL Q (e i - c • e j) hf⁆ ∈ matrixDerived Q :=
    Subgroup.commutator_mem_commutator (reflGL_mem _ _) (reflGL_mem _ _)
  convert hmem using 1
  apply glEquiv.injective
  refine LinearEquiv.ext fun v => ?_
  rw [glEquiv_reflProdGL_apply,
    pair_eq_commutator h2 (he j) hc hQe (horth i j hij) hf (he i), orthReflProd_apply,
    Finset.sum_pair hij]
  abel

include he horth in
private theorem reflProdGL_mem [Finite K] (h2 : (2 : K) ≠ 0) :
    ∀ (n : ℕ) (s : Finset ι), s.card = n → Even n → IsSquare (∏ i ∈ s, Q (e i)) →
      reflProdGL Q he horth s ∈ matrixDerived Q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hs hev hsq
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Finset.card_eq_zero.1 hs, reflProdGL_empty]
    exact one_mem _
  have hn2 : 2 ≤ n := by
    obtain ⟨k, rfl⟩ := hev
    omega
  obtain ⟨i, hi, j, hj, hij, hsqij⟩ :
      ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ IsSquare (Q (e i) * Q (e j)) := by
    rcases (show n = 2 ∨ 3 ≤ n by omega) with h2' | h3
    · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 (hs.trans h2')
      exact ⟨i, by simp, j, by simp, hij, by rwa [Finset.prod_pair hij] at hsq⟩
    · obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 (show 2 < s.card by omega)
      rcases exists_isSquare_mul_of_three (he a) (he b) (he c) with h | h | h
      · exact ⟨a, ha, b, hb, hab, h⟩
      · exact ⟨a, ha, c, hc, hac, h⟩
      · exact ⟨b, hb, c, hc, hbc, h⟩
  set t := (s.erase i).erase j with htdef
  have hjt : j ∈ s.erase i := Finset.mem_erase.2 ⟨Ne.symm hij, hj⟩
  have hst : s = {i, j} ∪ t := by
    ext k
    simp only [htdef, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_erase]
    constructor
    · intro hk
      by_cases hki : k = i
      · exact Or.inl (Or.inl hki)
      by_cases hkj : k = j
      · exact Or.inl (Or.inr hkj)
      exact Or.inr ⟨hkj, hki, hk⟩
    · rintro ((rfl | rfl) | ⟨-, -, hk⟩)
      · exact hi
      · exact hj
      · exact hk
  have hdisj : Disjoint ({i, j} : Finset ι) t := by
    rw [Finset.disjoint_left]
    intro k hk hkt
    simp only [htdef, Finset.mem_erase] at hkt
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact hkt.2.1 rfl
    · exact hkt.1 rfl
  have htcard : t.card = n - 2 := by
    rw [htdef, Finset.card_erase_of_mem hjt, Finset.card_erase_of_mem hi, hs]
    omega
  have htsq : IsSquare (∏ k ∈ t, Q (e k)) := by
    obtain ⟨a, ha⟩ := hsq
    obtain ⟨b, hb⟩ := hsqij
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact mul_ne_zero (he i) (he j) (by rw [hb, mul_zero])
    have hprod : (Q (e i) * Q (e j)) * ∏ k ∈ t, Q (e k) = a * a := by
      rw [← ha, hst, Finset.prod_union hdisj, Finset.prod_pair hij]
    refine ⟨a / b, ?_⟩
    rw [hb] at hprod
    field_simp
    linear_combination hprod
  rw [hst, reflProdGL_union he horth hdisj]
  refine mul_mem (reflProdGL_pair_mem he horth h2 hij hsqij)
    (ih (n - 2) (by omega) t htcard ?_ htsq)
  obtain ⟨k, rfl⟩ := hev
  exact ⟨k - 1, by omega⟩

end Prod

theorem mem_matrixDerived_of_orthogonal_family [Finite K] (h2 : (2 : K) ≠ 0)
    (Q : QuadraticForm K (Fin d → K)) {m : ℕ} (e : Fin m → (Fin d → K)) (he : ∀ i, Q (e i) ≠ 0)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (e i) (e j) = 0) (hm : Even m)
    (hsq : IsSquare (∏ i, Q (e i))) {z : GL (Fin d) K}
    (hz : ∀ v, glEquiv z v = v - ∑ i, ((Q (e i))⁻¹ * QuadraticMap.polar Q (e i) v) • e i) :
    z ∈ matrixDerived Q := by
  have hz' : z = reflProdGL Q he horth Finset.univ := by
    apply glEquiv.injective
    refine LinearEquiv.ext fun v => ?_
    rw [hz, glEquiv_reflProdGL_apply, orthReflProd_apply]
  rw [hz']
  exact reflProdGL_mem he horth h2 m Finset.univ (by simp) hm hsq

end Matrix

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
