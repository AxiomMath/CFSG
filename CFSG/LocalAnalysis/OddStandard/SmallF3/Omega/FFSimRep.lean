module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesSign

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

private lemma ff_two_neg : ∀ d : ZMod 3, -d + -d = d := by decide

private lemma ff_three_values_pair :
    ∀ a b c d : ZMod 3, a ≠ 0 → b ≠ 0 → c ≠ 0 → d ≠ 0 →
      (a = d ∧ b = d) ∨ (a = d ∧ c = d) ∨ (b = d ∧ c = d) ∨
        (a = -d ∧ b = -d) ∨ (a = -d ∧ c = -d) ∨ (b = -d ∧ c = -d) := by
  decide

private lemma ff_quad_values :
    ∀ a b d : ZMod 3, a ≠ 0 → b ≠ 0 → d ≠ 0 →
      ∃ x y : ZMod 3, x ^ 2 * a + y ^ 2 * b = d := by
  decide

private lemma ff_polarBilin_basis_ne {W : Type} [AddCommGroup W] [Module (ZMod 3) W]
    {R : QuadraticForm (ZMod 3) W} {n : ℕ} (b : Module.Basis (Fin n) (ZMod 3) W)
    (horth : R.polarBilin.IsOrthoᵢ b) (hB : R.polarBilin.Nondegenerate) (i : Fin n) :
    R (b i) ≠ 0 := by
  intro hi
  refine horth.not_isOrtho_basis_self_of_separatingLeft hB.1 i ?_
  rw [polarBilin_apply_apply, polar_self, hi, smul_zero]

private lemma ff_eval_two {W : Type} [AddCommGroup W] [Module (ZMod 3) W]
    {R : QuadraticForm (ZMod 3) W} {n : ℕ} (b : Module.Basis (Fin n) (ZMod 3) W)
    (horth : R.polarBilin.IsOrthoᵢ b) {i j : Fin n} (hij : i ≠ j) (x y : ZMod 3) :
    R (x • b i + y • b j) = x ^ 2 * R (b i) + y ^ 2 * R (b j) := by
  have hp : polar R (b i) (b j) = 0 := by
    have h := LinearMap.isOrthoᵢ_def.mp horth i j hij
    rwa [polarBilin_apply_apply] at h
  have h1 : R (x • b i + y • b j)
      = R (x • b i) + R (y • b j) + polar R (x • b i) (y • b j) :=
    QuadraticMap.map_add R (x • b i) (y • b j)
  rw [h1, R.map_smul x (b i), R.map_smul y (b j)]
  simp only [polar_smul_left, polar_smul_right, hp, smul_zero, zero_add, add_zero,
    smul_eq_mul, pow_two]
  ring

private lemma ff_basis_pair_independent {W : Type} [AddCommGroup W] [Module (ZMod 3) W]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod 3) W) {i j : Fin n} (hij : i ≠ j) :
    LinearIndependent (ZMod 3) ![b i, b j] := by
  have hf : Function.Injective ![i, j] := by
    intro a c hac
    fin_cases a <;> fin_cases c <;> simp_all
  have h : LinearIndependent (ZMod 3) (b ∘ ![i, j]) := b.linearIndependent.comp ![i, j] hf
  have heq : (b ∘ ![i, j]) = ![b i, b j] := by
    funext k
    fin_cases k <;> simp
  rwa [heq] at h

private lemma ff_pair_of_common {W : Type} [AddCommGroup W] [Module (ZMod 3) W]
    {R : QuadraticForm (ZMod 3) W} {n : ℕ} (b : Module.Basis (Fin n) (ZMod 3) W)
    (horth : R.polarBilin.IsOrthoᵢ b) {i j : Fin n} (hij : i ≠ j) {d : ZMod 3}
    (hv : (R (b i) = d ∧ R (b j) = d) ∨ (R (b i) = -d ∧ R (b j) = -d)) :
    ∃ w₁ w₂ : W, R w₁ = d ∧ R w₂ = d ∧ LinearIndependent (ZMod 3) ![w₁, w₂] := by
  rcases hv with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · exact ⟨b i, b j, hi, hj, ff_basis_pair_independent b hij⟩
  · refine ⟨b i + b j, b i - b j, ?_, ?_, ?_⟩
    · have h := ff_eval_two b horth hij 1 1
      rw [one_smul, one_smul] at h
      rw [h, hi, hj]
      simp only [one_pow, one_mul]
      exact ff_two_neg d
    · have h := ff_eval_two b horth hij 1 (-1)
      rw [one_smul, neg_one_smul] at h
      rw [sub_eq_add_neg, h, hi, hj]
      simp only [one_pow, neg_one_sq, one_mul]
      exact ff_two_neg d
    · have hbase := ff_basis_pair_independent b hij
      have hind := (LinearIndependent.pair_add_smul_add_smul_iff (R := ZMod 3) (x := b i)
        (y := b j) (a := (1 : ZMod 3)) (b := 1) (c := 1) (d := -1)).mpr
        ⟨hbase, by decide⟩
      simpa [one_smul, neg_one_smul, sub_eq_add_neg] using hind

theorem ff_exists_eq_of_nondegenerate {W : Type} [AddCommGroup W] [Module (ZMod 3) W]
    [FiniteDimensional (ZMod 3) W] {R : QuadraticForm (ZMod 3) W} (hR : R.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) W) {d : ZMod 3} (hd : d ≠ 0) : ∃ w : W, R w = d := by
  haveI : Invertible (2 : ZMod 3) := invertibleOfNonzero (by decide)
  have hB : R.polarBilin.Nondegenerate :=
    (QuadraticMap.nondegenerate_polar_iff (Q := R)).mpr hR
  obtain ⟨b, horth⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (B := R.polarBilin) ((LinearMap.BilinForm.isSymm_iff).mp (QuadraticMap.isSymm_polarBilin R))
  have hself : ∀ i, R (b i) ≠ 0 := fun i => ff_polarBilin_basis_ne b horth hB i
  let i0 : Fin (Module.finrank (ZMod 3) W) := ⟨0, by omega⟩
  let i1 : Fin (Module.finrank (ZMod 3) W) := ⟨1, by omega⟩
  have hi01 : i0 ≠ i1 := by simp [i0, i1]
  obtain ⟨x, y, hxy⟩ := ff_quad_values (R (b i0)) (R (b i1)) d (hself i0) (hself i1) hd
  exact ⟨x • b i0 + y • b i1, by rw [ff_eval_two b horth hi01 x y, hxy]⟩

theorem ff_exists_pair_eq_of_nondegenerate {W : Type} [AddCommGroup W] [Module (ZMod 3) W]
    [FiniteDimensional (ZMod 3) W] {R : QuadraticForm (ZMod 3) W} (hR : R.Nondegenerate)
    (h3 : 3 ≤ Module.finrank (ZMod 3) W) {d : ZMod 3} (hd : d ≠ 0) :
    ∃ w₁ w₂ : W, R w₁ = d ∧ R w₂ = d ∧ LinearIndependent (ZMod 3) ![w₁, w₂] := by
  haveI : Invertible (2 : ZMod 3) := invertibleOfNonzero (by decide)
  have hB : R.polarBilin.Nondegenerate :=
    (QuadraticMap.nondegenerate_polar_iff (Q := R)).mpr hR
  obtain ⟨b, horth⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (B := R.polarBilin) ((LinearMap.BilinForm.isSymm_iff).mp (QuadraticMap.isSymm_polarBilin R))
  have hself : ∀ i, R (b i) ≠ 0 := fun i => ff_polarBilin_basis_ne b horth hB i
  let i0 : Fin (Module.finrank (ZMod 3) W) := ⟨0, by omega⟩
  let i1 : Fin (Module.finrank (ZMod 3) W) := ⟨1, by omega⟩
  let i2 : Fin (Module.finrank (ZMod 3) W) := ⟨2, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1]
  have h02 : i0 ≠ i2 := by simp [i0, i2]
  have h12 : i1 ≠ i2 := by simp [i1, i2]
  have h3v := ff_three_values_pair (R (b i0)) (R (b i1)) (R (b i2)) d
    (hself i0) (hself i1) (hself i2) hd
  rcases h3v with ⟨ha, hb⟩ | ⟨ha, hc⟩ | ⟨hb, hc⟩ | ⟨ha, hb⟩ | ⟨ha, hc⟩ | ⟨hb, hc⟩
  · exact ff_pair_of_common b horth h01 (Or.inl ⟨ha, hb⟩)
  · exact ff_pair_of_common b horth h02 (Or.inl ⟨ha, hc⟩)
  · exact ff_pair_of_common b horth h12 (Or.inl ⟨hb, hc⟩)
  · exact ff_pair_of_common b horth h01 (Or.inr ⟨ha, hb⟩)
  · exact ff_pair_of_common b horth h02 (Or.inr ⟨ha, hc⟩)
  · exact ff_pair_of_common b horth h12 (Or.inr ⟨hb, hc⟩)

end CFSG.OddStandard.SmallF3.Omega
