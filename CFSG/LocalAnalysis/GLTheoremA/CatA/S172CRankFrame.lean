module

public import CFSG.ClassicalGroups.Orthogonal.MinusPlaneFrames
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankRot

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172C.Rank

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.GroupTheory.WeirSylow

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem polar_eq_zero_of_mem_span_pair {u a b x : V} (ha : polar Q u a = 0) (hb : polar Q u b = 0)
    (hx : x ∈ Submodule.span F {a, b}) : polar Q u x = 0 := by
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hx
  rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, ha, hb, mul_zero, mul_zero,
    add_zero]

theorem polar_eq_zero_of_mem_span_pair_pair {a b c d x y : V} (hac : polar Q a c = 0)
    (had : polar Q a d = 0) (hbc : polar Q b c = 0) (hbd : polar Q b d = 0)
    (hx : x ∈ Submodule.span F {a, b}) (hy : y ∈ Submodule.span F {c, d}) : polar Q x y = 0 := by
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hx
  rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
    polar_eq_zero_of_mem_span_pair hac had hy, polar_eq_zero_of_mem_span_pair hbc hbd hy, mul_zero,
    mul_zero, add_zero]

theorem exists_rotationFrame [Finite F] [CharP F 2] [FiniteDimensional F V]
    (hQ : (polarBilin Q).Nondegenerate) {n : ℕ} (hdim : finrank F V = 2 * n) (hminus : ¬ IsPlusType Q)
    (hn : 2 ≤ n) (heven : Even n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) :
    ∃ (x y : Fin (n - 1) → V) (u v : V),
      (∀ i, Q (x i) ≠ 0 ∧ Q (y i) ≠ 0 ∧ orderOf (reflect Q (x i) * reflect Q (y i)) = p) ∧
      (∀ i j, i ≠ j → polar Q (x i) (x j) = 0 ∧ polar Q (x i) (y j) = 0 ∧ polar Q (y i) (x j) = 0 ∧
        polar Q (y i) (y j) = 0) ∧
      Q u = 0 ∧ Q v = 0 ∧ polar Q u v = 1 ∧
      ∀ i, polar Q u (x i) = 0 ∧ polar Q u (y i) = 0 ∧ polar Q v (x i) = 0 ∧ polar Q v (y i) = 0 := by
  obtain ⟨a, b, e, f, hpair, hperp, he, hf, hef, horth⟩ := exists_anisoPairFrame hQ hdim hminus hn heven
  have hrot : ∀ i, ∃ x ∈ Submodule.span F {a i, b i}, ∃ y ∈ Submodule.span F {a i, b i},
      Q x ≠ 0 ∧ Q y ≠ 0 ∧ orderOf (reflect Q x * reflect Q y) = p := fun i =>
    exists_orderOf_reflect_mul_reflect_eq (hpair i).finrank_span_pair
      (fun x hx h => (hpair i).eq_zero_of_mem_span_pair hx h) hp hp2 hpq
  choose x hx y hy hQx hQy hord using hrot
  refine ⟨x, y, e, f, fun i => ⟨hQx i, hQy i, hord i⟩, fun i j hij => ?_, he, hf, hef, fun i => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hperp i j hij
    exact ⟨polar_eq_zero_of_mem_span_pair_pair h1 h2 h3 h4 (hx i) (hx j),
      polar_eq_zero_of_mem_span_pair_pair h1 h2 h3 h4 (hx i) (hy j),
      polar_eq_zero_of_mem_span_pair_pair h1 h2 h3 h4 (hy i) (hx j),
      polar_eq_zero_of_mem_span_pair_pair h1 h2 h3 h4 (hy i) (hy j)⟩
  · obtain ⟨h1, h2, h3, h4⟩ := horth i
    exact ⟨polar_eq_zero_of_mem_span_pair h1 h2 (hx i), polar_eq_zero_of_mem_span_pair h1 h2 (hy i),
      polar_eq_zero_of_mem_span_pair h3 h4 (hx i), polar_eq_zero_of_mem_span_pair h3 h4 (hy i)⟩

end CFSG.LocalAnalysis.GLTheoremA.S172C.Rank

end
