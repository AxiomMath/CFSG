module

public import CFSG.LinearAlgebra.FrobeniusSemilinearFixed

public section

namespace CFSG.LinearAlgebra

variable {L : Type*} [Field L] [IsAlgClosed L]

open scoped Matrix

private lemma frobBasis_surjective {σ : L →+* L} {Q : ℕ} (hQ : 0 < Q)
    (hσ : ∀ c, σ c = c ^ Q) : Function.Surjective σ := by
  intro c
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c hQ
  exact ⟨d, by rw [hσ, hd]⟩

private lemma frobBasis_exists_pow_sub_add {Q : ℕ} (hQ : 2 ≤ Q) (c : L) :
    ∃ a : L, a ^ Q - a + c = 0 := by
  have hdeg : (Polynomial.X ^ Q - Polynomial.X + Polynomial.C c : Polynomial L).degree = Q := by
    have hsplit : (Polynomial.X ^ Q - Polynomial.X + Polynomial.C c : Polynomial L) =
        Polynomial.X ^ Q + (-Polynomial.X + Polynomial.C c) := by ring
    rw [hsplit, Polynomial.degree_add_eq_left_of_degree_lt]
    · exact Polynomial.degree_X_pow (R := L) (n := Q)
    · rw [Polynomial.degree_X_pow]
      calc
        (-Polynomial.X + Polynomial.C c : Polynomial L).degree
            ≤ max (-Polynomial.X : Polynomial L).degree (Polynomial.C c).degree :=
              Polynomial.degree_add_le _ _
        _ ≤ max 1 0 := by
              apply max_le
              · rw [Polynomial.degree_neg, Polynomial.degree_X]
                exact le_max_left _ _
              · exact Polynomial.degree_C_le.trans (le_max_right _ _)
        _ = 1 := max_eq_left zero_le_one
        _ < (Q : WithBot ℕ) :=
              WithBot.coe_lt_coe.mpr (by omega : (1 : ℕ) < Q)
  have hp : (Polynomial.X ^ Q - Polynomial.X + Polynomial.C c : Polynomial L).degree ≠ 0 := by
    rw [hdeg]
    exact ne_of_gt (WithBot.coe_lt_coe.mpr (by omega : 0 < Q))
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root _ hp
  exact ⟨a, by simpa [Polynomial.IsRoot] using ha⟩

private lemma frobBasis_span_invariant {V : Type*} [AddCommGroup V] [Module L V]
    {σ : L →+* L} {φ : V →ₛₗ[σ] V} {k : ℕ} {b : Fin k → V}
    (hfix : ∀ i, φ (b i) = b i) :
    Submodule.span L (Set.range b) ≤
      Submodule.comap φ (Submodule.span L (Set.range b)) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, hfix i]
  exact Submodule.subset_span ⟨i, rfl⟩

private lemma frobBasis_preimage {V : Type*} [AddCommGroup V] [Module L V]
    {σ : L →+* L} {φ : V →ₛₗ[σ] V} (hφ : Function.Injective φ) {k : ℕ} {b : Fin k → V}
    (hfix : ∀ i, φ (b i) = b i) (hsurj : Function.Surjective σ) :
    ∀ x : V, φ x ∈ Submodule.span L (Set.range b) →
      x ∈ Submodule.span L (Set.range b) := by
  intro x hx
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun (R := L) (v := b) (x := φ x)).mp hx
  choose d hd using fun i => hsurj (c i)
  have hsum : (∑ i, σ (d i) • b i) = φ x := by
    rw [← hc]
    exact Finset.sum_congr rfl fun i _ => by rw [hd i]
  have hφsum : φ (∑ i, d i • b i) = ∑ i, σ (d i) • b i := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smulₛₗ, hfix i]
  have hxd : (∑ i, d i • b i) = x := hφ (hφsum.trans hsum)
  rw [← hxd]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private lemma frobBasis_mapQ_injective {V : Type*} [AddCommGroup V] [Module L V]
    {σ : L →+* L} {U : Submodule L V} {φ : V →ₛₗ[σ] V}
    (hmap : U ≤ Submodule.comap φ U) (hpre : ∀ x, φ x ∈ U → x ∈ U) :
    Function.Injective (U.mapQ U φ hmap) := by
  have hker : ∀ z : V ⧸ U, U.mapQ U φ hmap z = 0 → z = 0 := by
    intro z hz
    induction z using Submodule.Quotient.induction_on with
    | H x =>
        rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hz
        rw [Submodule.Quotient.mk_eq_zero]
        exact hpre x hz
  intro x y hxy
  have hsub : U.mapQ U φ hmap (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (hker (x - y) hsub)

private lemma frobBasis_fixed_outside {V : Type*} [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] {σ : L →+* L} {Q : ℕ} (hQ : 2 ≤ Q)
    (hσ : ∀ c, σ c = c ^ Q) (φ : V →ₛₗ[σ] V) (hφ : Function.Injective φ)
    {k : ℕ} {b : Fin k → V} (hfix : ∀ i, φ (b i) = b i)
    (hUtop : Submodule.span L (Set.range b) ≠ ⊤) :
    ∃ w' : V, φ w' = w' ∧ w' ∉ Submodule.span L (Set.range b) := by
  classical
  let U : Submodule L V := Submodule.span L (Set.range b)
  have hUtop' : U ≠ ⊤ := by simpa [U] using hUtop
  have hmap : U ≤ Submodule.comap φ U := frobBasis_span_invariant hfix
  have hsurj : Function.Surjective σ := frobBasis_surjective (by omega) hσ
  have hpre : ∀ x, φ x ∈ U → x ∈ U := frobBasis_preimage hφ hfix hsurj
  let ψ : V ⧸ U →ₛₗ[σ] V ⧸ U := U.mapQ U φ hmap
  have hψinj : Function.Injective ψ := frobBasis_mapQ_injective hmap hpre
  haveI : Nontrivial (V ⧸ U) := Submodule.Quotient.nontrivial_iff.mpr hUtop'
  obtain ⟨wbar, hwbar_ne, hwbar_fix⟩ :=
    exists_ne_zero_fixed_of_frobeniusSemilinear (V := V ⧸ U) hQ hσ ψ hψinj
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective (p := U) wbar
  have hdiff : φ w - w ∈ U := by
    have h : (Submodule.Quotient.mk (p := U) (φ w) : V ⧸ U) =
        (Submodule.Quotient.mk (p := U) w : V ⧸ U) := by
      simpa [ψ, Submodule.mapQ_apply] using hwbar_fix
    exact (Submodule.Quotient.eq (p := U)).mp h
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun (R := L) (v := b) (x := φ w - w)).mp hdiff
  choose a ha using fun i => frobBasis_exists_pow_sub_add (L := L) hQ (c i)
  let w' : V := w + ∑ i, a i • b i
  have hφw : φ w = w + ∑ i, c i • b i := by
    rw [hc]
    abel
  have hCA : (∑ i, c i • b i) + (∑ i, a i ^ Q • b i) = ∑ i, a i • b i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← add_smul]
    congr 1
    linear_combination ha i
  have hw'fix : φ w' = w' := by
    change φ (w + ∑ i, a i • b i) = w + ∑ i, a i • b i
    calc
      φ (w + ∑ i, a i • b i) = φ w + ∑ i, σ (a i) • b i := by
        rw [map_add, map_sum]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by rw [map_smulₛₗ, hfix i]
      _ = φ w + ∑ i, a i ^ Q • b i := by
        congr 1
        exact Finset.sum_congr rfl fun i _ => by rw [hσ (a i)]
      _ = (w + ∑ i, c i • b i) + ∑ i, a i ^ Q • b i := by rw [hφw]
      _ = w + ∑ i, a i • b i := by rw [add_assoc, hCA]
  have hw'not : w' ∉ U := by
    intro hw'U
    have hsub : w' - w ∈ U := by
      have h : w' - w = ∑ i, a i • b i := by
        change (w + ∑ i, a i • b i) - w = ∑ i, a i • b i
        abel
      rw [h]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hwU : w ∈ U := by
      have h : w = w' - (w' - w) := by abel
      rw [h]
      exact U.sub_mem hw'U hsub
    exact hwbar_ne (by rw [Submodule.Quotient.mk_eq_zero]; exact hwU)
  exact ⟨w', hw'fix, by simpa [U] using hw'not⟩

private lemma frobBasis_snoc {V : Type*} [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] {σ : L →+* L} {Q : ℕ} (hQ : 2 ≤ Q)
    (hσ : ∀ c, σ c = c ^ Q) (φ : V →ₛₗ[σ] V) (hφ : Function.Injective φ)
    {k : ℕ} {b : Fin k → V} (hb : LinearIndependent L b) (hfix : ∀ i, φ (b i) = b i)
    (hk : k < Module.finrank L V) :
    ∃ b' : Fin (k + 1) → V, LinearIndependent L b' ∧ ∀ i, φ (b' i) = b' i := by
  classical
  let U : Submodule L V := Submodule.span L (Set.range b)
  have hUtop : U ≠ ⊤ := by
    intro htop
    have hdim : Module.finrank L U = k := by
      rw [show U = Submodule.span L (Set.range b) from rfl, finrank_span_eq_card hb,
        Fintype.card_fin]
    have hdimV : Module.finrank L U = Module.finrank L V := by rw [htop, finrank_top]
    omega
  obtain ⟨w', hw'fix, hw'not⟩ :=
    frobBasis_fixed_outside hQ hσ φ hφ hfix (by simpa [U] using hUtop)
  refine ⟨Fin.snoc b w', ?_, ?_⟩
  · rw [linearIndependent_finSnoc]
    exact ⟨hb, by simpa [U] using hw'not⟩
  · intro i
    refine Fin.lastCases ?_ ?_ i
    · simpa using hw'fix
    · intro j
      simpa using hfix j

private lemma frobBasis_exists_family {V : Type*} [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] {σ : L →+* L} {Q : ℕ} (hQ : 2 ≤ Q)
    (hσ : ∀ c, σ c = c ^ Q) (φ : V →ₛₗ[σ] V) (hφ : Function.Injective φ) :
    ∀ k ≤ Module.finrank L V,
      ∃ b : Fin k → V, LinearIndependent L b ∧ ∀ i, φ (b i) = b i := by
  intro k
  induction k with
  | zero =>
      intro _
      exact ⟨Fin.elim0, linearIndependent_empty_type, fun i => i.elim0⟩
  | succ k ih =>
      intro hk
      obtain ⟨b, hb, hfix⟩ := ih (Nat.le_trans (Nat.le_succ k) hk)
      exact frobBasis_snoc hQ hσ φ hφ hb hfix (by omega)

theorem exists_basis_fixed_of_frobeniusSemilinear {V : Type*} [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] {σ : L →+* L} {Q : ℕ} (hQ : 2 ≤ Q) (hσ : ∀ c, σ c = c ^ Q)
    (φ : V →ₛₗ[σ] V) (hφ : Function.Injective φ) :
    ∃ b : Module.Basis (Fin (Module.finrank L V)) L V, ∀ i, φ (b i) = b i := by
  obtain ⟨b, hb, hfix⟩ := frobBasis_exists_family hQ hσ φ hφ (Module.finrank L V) le_rfl
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' b hb (by simp), ?_⟩
  intro i
  rw [coe_basisOfLinearIndependentOfCardEqFinrank']
  exact hfix i

theorem exists_map_frobenius_eq_mul {n : ℕ} {σ : L →+* L} {Q : ℕ} (hQ : 2 ≤ Q)
    (hσ : ∀ c, σ c = c ^ Q) (C : GL (Fin n) L) :
    ∃ Y : GL (Fin n) L, (Y : Matrix (Fin n) (Fin n) L).map σ =
      (Y : Matrix (Fin n) (Fin n) L) * (C : Matrix (Fin n) (Fin n) L) := by
  classical
  have hCC : ((C⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      (C : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one]
  let φ : (Fin n → L) →ₛₗ[σ] (Fin n → L) :=
    { toFun := fun v => (fun j => σ (v j)) ᵥ* ((C⁻¹ : GL (Fin n) L) :
        Matrix (Fin n) (Fin n) L)
      map_add' := by
        intro x y
        ext j
        simp only [Pi.add_apply, Matrix.vecMul_apply_eq_sum, map_add, add_mul,
          Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        ext j
        simp only [Pi.smul_apply, Matrix.vecMul_apply_eq_sum, map_mul, smul_eq_mul]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring }
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have h2 : (fun j => σ (x j)) = fun j => σ (y j) := by
      have h3 := congrArg (fun v => v ᵥ* (C : Matrix (Fin n) (Fin n) L)) hxy
      simpa [φ, Matrix.vecMul_vecMul, hCC] using h3
    ext j
    exact RingHom.injective σ (congrFun h2 j)
  obtain ⟨b, hbfix⟩ :=
    exists_basis_fixed_of_frobeniusSemilinear (V := Fin n → L) hQ hσ φ hφinj
  let e : Fin (Module.finrank L (Fin n → L)) ≃ Fin n :=
    finCongr (Module.finrank_fin_fun (R := L) (n := n))
  let b' : Module.Basis (Fin n) L (Fin n → L) := b.reindex e
  have hb'fix : ∀ i, φ (b' i) = b' i := by
    intro i
    simpa [b', e, Module.Basis.reindex_apply] using hbfix (e.symm i)
  let Y : Matrix (Fin n) (Fin n) L := Matrix.of fun i => b' i
  have hYli : LinearIndependent L Y.row := by
    simpa [Y] using b'.linearIndependent
  have hYunit : IsUnit Y.det :=
    (Matrix.isUnit_iff_isUnit_det (A := Y)).mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp hYli)
  have hYmap : Y.map σ = Y * (C : Matrix (Fin n) (Fin n) L) := by
    refine Matrix.ext_row fun i => ?_
    rw [Matrix.row_map, Matrix.row_mul_eq_vecMul_row]
    have hrow : (fun j => σ (b' i j)) = b' i ᵥ* (C : Matrix (Fin n) (Fin n) L) := by
      have h := congrArg (fun v => v ᵥ* (C : Matrix (Fin n) (Fin n) L)) (hb'fix i)
      simpa [φ, Matrix.vecMul_vecMul, hCC] using h
    ext j
    simpa [Y] using congrFun hrow j
  refine ⟨Matrix.GeneralLinearGroup.mk'' Y hYunit, ?_⟩
  change Y.map σ = Y * (C : Matrix (Fin n) (Fin n) L)
  exact hYmap

end CFSG.LinearAlgebra
