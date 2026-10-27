module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinusDefs
public import CFSG.LieType.BorelTits.OrthogonalForm

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus

open Matrix CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank Polynomial

section Aux

variable {F : Type} [Field F]

private abbrev i0 : Idx 0 := Sum.inr (Sum.inr 0)

private abbrev i1 : Idx 0 := Sum.inr (Sum.inr 1)

private theorem qm0_apply (b c : F) (v : Idx 0 → F) :
    Qm 0 F b c v = v i0 ^ 2 + b * v i0 * v i1 + c * v i1 ^ 2 := by
  simp [Qm, StatedQuadMinus]

omit [Field F] in
private theorem idx0_ext {u w : Idx 0 → F} (h0 : u i0 = w i0) (h1 : u i1 = w i1) : u = w := by
  funext x
  rcases x with a | a | a
  · exact a.elim0
  · exact a.elim0
  · fin_cases a
    · exact h0
    · exact h1

private theorem eq_zero_of_qm0 {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {v : Idx 0 → F} (hv : Qm 0 F b c v = 0) : v = 0 := by
  rw [qm0_apply] at hv
  by_cases h1 : v i1 = 0
  · rw [h1] at hv
    have h0 : v i0 = 0 := by simpa using hv
    exact idx0_ext (by simpa using h0) (by simpa using h1)
  · exfalso
    apply hirr (v i0 / v i1)
    have : (v i0 / v i1) ^ 2 + b * (v i0 / v i1) + c = (v i0 ^ 2 + b * v i0 * v i1 +
        c * v i1 ^ 2) / v i1 ^ 2 := by
      field_simp
    rw [this, hv, zero_div]

end Aux

section Main

variable {F : Type} [Field F] [CharP F 2]

private theorem two_eq_zero' : (2 : F) = 0 := by
  have := CharP.cast_eq_zero F 2
  simpa using this

private theorem polar_qm0 (b c : F) (u w : Idx 0 → F) :
    Qm 0 F b c (u + w) - Qm 0 F b c u - Qm 0 F b c w = b * (u i0 * w i1 + u i1 * w i0) := by
  simp only [qm0_apply, Pi.add_apply]
  linear_combination (u i0 * w i0 + c * u i1 * w i1) * (two_eq_zero' (F := F))

private theorem exists_smul_of_fix {b c : F} (hb : b ≠ 0) {M : Matrix (Idx 0) (Idx 0) F}
    (hQ : ∀ v, Qm 0 F b c (M *ᵥ v) = Qm 0 F b c v) {v : Idx 0 → F} (hv : v ≠ 0)
    (hMv : M *ᵥ v = v) (u : Idx 0 → F) : ∃ t : F, M *ᵥ u = u + t • v := by
  have hP : ∀ x y, Qm 0 F b c (M *ᵥ x + M *ᵥ y) - Qm 0 F b c (M *ᵥ x) - Qm 0 F b c (M *ᵥ y) =
      Qm 0 F b c (x + y) - Qm 0 F b c x - Qm 0 F b c y := by
    intro x y
    rw [← Matrix.mulVec_add, hQ, hQ, hQ]
  have h := hP v u
  rw [hMv, polar_qm0, polar_qm0] at h
  have h' := mul_left_cancel₀ hb h
  have h2 := two_eq_zero' (F := F)
  by_cases h0 : v i0 = 0
  · have h1 : v i1 ≠ 0 := by
      intro h1
      exact hv (idx0_ext (by simpa using h0) (by simpa using h1))
    have ha : (M *ᵥ u) i0 = u i0 := by
      have : v i1 * ((M *ᵥ u) i0 - u i0) = 0 := by
        rw [h0] at h'
        linear_combination h'
      have := (mul_eq_zero.mp this).resolve_left h1
      linear_combination this
    refine ⟨((M *ᵥ u) i1 - u i1) / v i1, idx0_ext ?_ ?_⟩
    · simp [h0, ha]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
  · refine ⟨((M *ᵥ u) i0 - u i0) / v i0, idx0_ext ?_ ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination h' - v i1 * ((M *ᵥ u) i0 - u i0) * h2

omit [CharP F 2] in
private theorem exists_eigenvector [Finite F] {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card F - 1)
    (M : Matrix (Idx 0) (Idx 0) F) (hM : M ^ p = 1) :
    ∃ (v : Idx 0 → F) (l : F), v ≠ 0 ∧ M *ᵥ v = l • v := by
  classical
  have := Fact.mk hp
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p
    (by rw [Nat.card_units]; exact hpq)
  have hprim : IsPrimitiveRoot (x : F) p :=
    IsPrimitiveRoot.coe_units_iff.mpr (hx ▸ IsPrimitiveRoot.orderOf x)
  have hsplit := Polynomial.X_pow_sub_one_eq_prod hp.pos hprim
  set f : Module.End F (Idx 0 → F) := Matrix.toLin' M with hfdef
  have hf : f ^ p = 1 := by
    have := congrArg (Matrix.toLinAlgEquiv' (R := F) (n := Idx 0)) hM
    rw [map_pow, map_one] at this
    exact this
  have hdvd : minpoly F f ∣ (X ^ p - 1 : F[X]) := minpoly.dvd F f (by simp [hf])
  have hint : IsIntegral F f := Algebra.IsIntegral.isIntegral f
  have hnu : ¬ IsUnit (minpoly F f) := minpoly.not_isUnit F f
  obtain ⟨q, hq, hqd⟩ := WfDvdMonoid.exists_irreducible_factor hnu (minpoly.ne_zero hint)
  have hqprod : q ∣ ∏ ζ ∈ nthRootsFinset p (1 : F), (X - C ζ) := by
    rw [← hsplit]; exact hqd.trans hdvd
  obtain ⟨ζ, -, hζ⟩ := (hq.prime.dvd_finsetProd_iff _).mp hqprod
  have hassoc := hq.associated_of_dvd (irreducible_X_sub_C ζ) hζ
  have hroot : (minpoly F f).IsRoot ζ :=
    dvd_iff_isRoot.mp (hassoc.symm.dvd.trans hqd)
  have heig : f.HasEigenvalue ζ := Module.End.hasEigenvalue_iff_isRoot.mpr hroot
  obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
  refine ⟨v, ζ, hv.2, ?_⟩
  have := Module.End.mem_eigenspace_iff.mp hv.1
  simpa [hfdef] using this

private theorem natCast_eq_one_of_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (p : F) = 1 := by
  obtain ⟨k, hk⟩ := hp.eq_two_or_odd'.resolve_left hp2
  rw [hk]
  push_cast
  linear_combination (k : F) * (two_eq_zero' (F := F))

theorem eq_one_of_pow_of_orth_two {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F - 1) {g : GL (Idx 0) F}
    (hg : g ∈ CFSG.LieType.BorelTits.orthGroup (Qm 0 F b c)) (hgp : g ^ p = 1) : g = 1 := by
  have hQ := orthGroup_preserves (Qm 0 F b c) hg
  set M : Matrix (Idx 0) (Idx 0) F := (g : Matrix (Idx 0) (Idx 0) F) with hMdef
  have hM : M ^ p = 1 := by
    have := congrArg (fun x : GL (Idx 0) F => (x : Matrix (Idx 0) (Idx 0) F)) hgp
    simpa [hMdef] using this
  have h2 := two_eq_zero' (F := F)
  have hb : b ≠ 0 := by
    intro hb0
    obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (F := F) (ringChar.eq F 2) c
    apply hirr s
    rw [hb0]
    have : c = s * s := hs
    rw [this]
    linear_combination s ^ 2 * h2
  obtain ⟨v, l, hv, hMv⟩ := exists_eigenvector hp hpq M hM
  have hl : l = 1 := by
    have hq := hQ v
    rw [hMv] at hq
    rw [qm0_apply, qm0_apply] at hq
    have hQv : Qm 0 F b c v ≠ 0 := fun h => hv (eq_zero_of_qm0 hirr h)
    rw [qm0_apply] at hQv
    have h3 : (l ^ 2 - 1) * (v i0 ^ 2 + b * v i0 * v i1 + c * v i1 ^ 2) = 0 := by
      simp only [Pi.smul_apply, smul_eq_mul] at hq
      linear_combination hq
    have h4 := (mul_eq_zero.mp h3).resolve_right hQv
    have h5 : (l - 1) ^ 2 = 0 := by linear_combination h4 - (l - 1) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h5)
  rw [hl, one_smul] at hMv
  have hmul := exists_smul_of_fix hb hQ hv hMv
  have hall : ∀ u, M *ᵥ u = u := by
    intro u
    obtain ⟨t, ht⟩ := hmul u
    have hk : ∀ k : ℕ, (M ^ k) *ᵥ u = u + ((k : F) * t) • v := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_add, ht, Matrix.mulVec_smul, hMv]
        push_cast
        rw [add_assoc, ← add_smul]
        congr 2
        ring
    have := hk p
    rw [hM, Matrix.one_mulVec, natCast_eq_one_of_odd hp hp2, one_mul] at this
    have h0 : t • v = 0 := by
      have := congrArg (fun x => x - u) this
      simpa using this.symm
    have ht0 : t = 0 := (smul_eq_zero.mp h0).resolve_right hv
    rw [ht, ht0, zero_smul, add_zero]
  have hM1 : M = 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro u
    simp [hall]
  exact Units.ext hM1

theorem orth_two_split {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (p : ℕ) (hp57 : p = 5 ∨ p = 7)
    (hpq : p ∣ Nat.card F - 1) :
    ∀ g : GL (Idx 0) F, g ∈ CFSG.LieType.BorelTits.orthGroup (Qm 0 F b c) → g ^ p = 1 → g = 1 := by
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by rcases hp57 with rfl | rfl <;> norm_num
  intro g hg hgp
  exact eq_one_of_pow_of_orth_two hirr hp hp2 hpq hg hgp

end Main

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus
