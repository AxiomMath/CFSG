module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.ComponentClassification.RankTwoClassical

section Fixed

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_ne_zero_fixed_of_isPGroup [Finite K] [CharP K 2] [FiniteDimensional K V]
    {P : Subgroup (LinearMap.GeneralLinearGroup K V)} (hP : IsPGroup 2 P) {W : Submodule K V}
    (hW : W ≠ ⊥) (hPW : ∀ g ∈ P, ∀ w ∈ W, (g : Module.End K V) w ∈ W) :
    ∃ w ∈ W, w ≠ 0 ∧ ∀ g ∈ P, (g : Module.End K V) w = w := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction P W :=
    { smul := fun g w => ⟨((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) w,
        hPW g g.2 w w.2⟩
      one_smul := fun w => Subtype.ext rfl
      mul_smul := fun g h w => Subtype.ext rfl }
  have hsmul : ∀ (g : P) (w : W), ((g • w : W) : V) =
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) w := fun _ _ => rfl
  have : Finite W := Module.finite_of_finite K
  have hmod := hP.card_modEq_card_fixedPoints W
  have h2W : 2 ∣ Nat.card W := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨f, -, hf⟩ := FiniteField.card K 2
    have hpos : 0 < Module.finrank K W := by
      rw [Nat.pos_iff_ne_zero]
      intro h0
      exact hW (Submodule.finrank_eq_zero.mp h0)
    rw [Module.natCard_eq_pow_finrank (K := K), Nat.card_eq_fintype_card, hf]
    exact dvd_pow (dvd_pow_self 2 f.ne_zero) hpos.ne'
  by_contra hcon
  push Not at hcon
  have hfix : MulAction.fixedPoints P W = {0} := by
    ext w
    simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro hw
      by_contra hw0
      obtain ⟨g, hg, hgw⟩ := hcon w w.2 fun h => hw0 (Subtype.ext h)
      exact hgw (congrArg Subtype.val (hw ⟨g, hg⟩))
    · rintro rfl g
      exact Subtype.ext (by rw [hsmul]; exact map_zero _)
  rw [hfix, Nat.card_unique (α := ↑({0} : Set ↥W))] at hmod
  have h3 : Nat.card W % 2 = 1 := hmod
  omega

end Fixed

section Monomial

variable {E U : Type*} [Field E] [AddCommGroup U] [Module E U] {m : ℕ}
  (b : Module.Basis (Fin m) E U)

@[expose] noncomputable def basisScale (c : E) (i : Fin m) : U →ₗ[E] U :=
  b.constr E fun j => if j = i then c • b j else b j

@[expose] noncomputable def basisSwap (i j : Fin m) : U →ₗ[E] U :=
  b.constr E fun k => b (Equiv.swap i j k)

theorem basisScale_basis (c : E) (i k : Fin m) :
    basisScale b c i (b k) = if k = i then c • b k else b k := by
  rw [basisScale, Module.Basis.constr_basis]

theorem basisSwap_basis (i j k : Fin m) : basisSwap b i j (b k) = b (Equiv.swap i j k) := by
  rw [basisSwap, Module.Basis.constr_basis]

theorem repr_basisScale (c : E) (i : Fin m) (u : U) (k : Fin m) :
    b.repr (basisScale b c i u) k = if k = i then c * b.repr u k else b.repr u k := by
  conv_lhs => rw [← b.sum_repr u]
  rw [map_sum, map_sum]
  simp only [map_smul, basisScale_basis]
  rw [Finset.sum_apply' (s := Finset.univ), Finset.sum_eq_single k]
  · split_ifs with hk
    · subst hk
      simp [mul_comm]
    · simp
  · intro j _ hjk
    split_ifs with hj
    · simp [Module.Basis.repr_self, hjk]
    · simp [Module.Basis.repr_self, hjk]
  · simp

theorem repr_basisSwap (i j : Fin m) (u : U) (k : Fin m) :
    b.repr (basisSwap b i j u) k = b.repr u (Equiv.swap i j k) := by
  conv_lhs => rw [← b.sum_repr u]
  rw [map_sum, map_sum]
  simp only [map_smul, basisSwap_basis]
  rw [Finset.sum_apply' (s := Finset.univ), Finset.sum_eq_single (Equiv.swap i j k)]
  · simp
  · intro l _ hl
    have hl' : Equiv.swap i j l ≠ k := fun h => hl (by rw [← h, Equiv.swap_apply_self])
    simp [Module.Basis.repr_self, hl']
  · simp

theorem basisScale_apply (c : E) (i : Fin m) (u : U) :
    basisScale b c i u = u + ((c - 1) * b.repr u i) • b i := by
  apply b.repr.injective
  ext k
  rw [repr_basisScale, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
    Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
  split_ifs with h1 h2 h2
  · subst h1
    ring
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · ring

theorem eq_top_of_basisScale_basisSwap {c : E} (hc : c ≠ 1) (W : Submodule E U) (hW : W ≠ ⊥)
    (hscale : ∀ i, ∀ w ∈ W, basisScale b c i w ∈ W)
    (hswap : ∀ i j, ∀ w ∈ W, basisSwap b i j w ∈ W) : W = ⊤ := by
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨i, hi⟩ : ∃ i, b.repr w i ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 (b.ext_elem fun i => by rw [h i, map_zero, Finsupp.zero_apply])
  have hci : (c - 1) * b.repr w i ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hc) hi
  have hbi : b i ∈ W := by
    have h1 : ((c - 1) * b.repr w i) • b i ∈ W := by
      have := W.sub_mem (hscale i w hw) hw
      rwa [basisScale_apply, add_sub_cancel_left] at this
    have h2 := W.smul_mem ((c - 1) * b.repr w i)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hci, one_smul] at h2
  have hall : ∀ j, b j ∈ W := fun j => by
    have := hswap i j (b i) hbi
    rwa [basisSwap_basis, Equiv.swap_apply_left] at this
  rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact hall j

@[expose] noncomputable def basisScaleUnit (c : Eˣ) (i : Fin m) :
    LinearMap.GeneralLinearGroup E U where
  val := basisScale b c i
  inv := basisScale b (c⁻¹ : Eˣ) i
  val_inv := b.ext fun k => by
    rw [Module.End.mul_apply, basisScale_basis, Module.End.one_apply]
    by_cases hk : k = i
    · simp only [hk, ↓reduceIte, map_smul, basisScale_basis, smul_smul]
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    · simp only [hk, ↓reduceIte, basisScale_basis]
  inv_val := b.ext fun k => by
    rw [Module.End.mul_apply, basisScale_basis, Module.End.one_apply]
    by_cases hk : k = i
    · simp only [hk, ↓reduceIte, map_smul, basisScale_basis, smul_smul]
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
    · simp only [hk, ↓reduceIte, basisScale_basis]

@[expose] noncomputable def basisSwapUnit (i j : Fin m) : LinearMap.GeneralLinearGroup E U where
  val := basisSwap b i j
  inv := basisSwap b i j
  val_inv := b.ext fun k => by
    rw [Module.End.mul_apply, basisSwap_basis, basisSwap_basis, Equiv.swap_apply_self,
      Module.End.one_apply]
  inv_val := b.ext fun k => by
    rw [Module.End.mul_apply, basisSwap_basis, basisSwap_basis, Equiv.swap_apply_self,
      Module.End.one_apply]

theorem sesq_eq_sum_of_orthonormal {σ : E →+* E} {H : U →ₛₗ[σ] U →ₗ[E] E}
    (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0) (u w : U) :
    H u w = ∑ i, σ (b.repr u i) * b.repr w i := by
  conv_lhs => rw [← b.sum_repr u, ← b.sum_repr w]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, map_smul, hb, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Finset.sum_ite_eq', mul_comm]

theorem sesq_basisScale {σ : E →+* E} {H : U →ₛₗ[σ] U →ₗ[E] E}
    (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0) {c : E} (hc : σ c * c = 1)
    (i : Fin m) (u w : U) : H (basisScale b c i u) (basisScale b c i w) = H u w := by
  rw [sesq_eq_sum_of_orthonormal b hb, sesq_eq_sum_of_orthonormal b hb]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [repr_basisScale, repr_basisScale]
  split_ifs with hk
  · rw [map_mul, show σ c * σ (b.repr u k) * (c * b.repr w k) =
      (σ c * c) * (σ (b.repr u k) * b.repr w k) by ring, hc, one_mul]
  · rfl

theorem sesq_basisSwap {σ : E →+* E} {H : U →ₛₗ[σ] U →ₗ[E] E}
    (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0) (i j : Fin m) (u w : U) :
    H (basisSwap b i j u) (basisSwap b i j w) = H u w := by
  rw [sesq_eq_sum_of_orthonormal b hb, sesq_eq_sum_of_orthonormal b hb]
  simp only [repr_basisSwap]
  exact Equiv.sum_comp (Equiv.swap i j) fun k => σ (b.repr u k) * b.repr w k

end Monomial

end CFSG.ComponentClassification.RankTwoClassical
