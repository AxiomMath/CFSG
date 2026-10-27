module

public import CFSG.LieType.AlgebraicGroups.ClosedCone
public import CFSG.Mathlib.RingTheory.HomogeneousElimination
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction

public noncomputable section

open WithConv TauCeti.Comodule MvPolynomial

namespace CFSG.LieType.AlgebraicGroups.ClosedCone

universe u v w

variable {k : Type u} [Field k]

theorem eval_smul_of_isHomogeneous {σ : Type*} [Fintype σ] {p : MvPolynomial σ k} {d : ℕ}
    (hp : p.IsHomogeneous d) (c : k) (v : σ → k) :
    eval (c • v) p = c ^ d * eval v p := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmd : ∑ i, m i = d := by
    by_contra h
    exact (mem_support_iff.mp hm) (hp.coeff_eq_zero (by rwa [Finsupp.degree_eq_sum]))
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hmd]
  ring

theorem eval_homogeneousComponent_eq_zero [Infinite k] {σ : Type*} [Fintype σ]
    {f : MvPolynomial σ k} {v : σ → k} (h : ∀ c : k, eval (c • v) f = 0) (n : ℕ) :
    eval v (homogeneousComponent n f) = 0 := by
  rcases lt_or_ge f.totalDegree n with hn | hn
  · rw [homogeneousComponent_eq_zero n f hn, map_zero]
  let Q : Polynomial k := ∑ e ∈ Finset.range (f.totalDegree + 1),
    Polynomial.monomial e (eval v (homogeneousComponent e f))
  have hQ : Q = 0 := by
    refine Polynomial.funext fun c => ?_
    rw [Polynomial.eval_zero, ← h c]
    conv_rhs => rw [← sum_homogeneousComponent f]
    rw [map_sum, Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Polynomial.eval_monomial,
      eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous e f), mul_comm]
  have hcoeff := congrArg (fun q : Polynomial k => q.coeff n) hQ
  simp only [Q, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero,
    Finset.sum_ite_eq', Finset.mem_range] at hcoeff
  rwa [if_pos (Nat.lt_succ_of_le hn)] at hcoeff

theorem IsZariskiClosed.exists_isHomogeneous [Infinite k] {V : Type v} [AddCommGroup V]
    [Module k V] {X : Set V} (hX : IsZariskiClosed k X) (hc : IsCone k X) {σ : Type*}
    [Fintype σ] (b : Module.Basis σ k V) :
    ∃ S : Set (MvPolynomial σ k), (∀ f ∈ S, ∃ n, f.IsHomogeneous n) ∧
      ∀ x, x ∈ X ↔ ∀ f ∈ S, eval (b.equivFun x) f = 0 := by
  obtain ⟨I, hI⟩ := hX.exists_eq_preimage_zeroLocus b
  refine ⟨{p | ∃ f ∈ I, ∃ n, p = homogeneousComponent n f}, ?_, fun x => ⟨fun hx => ?_,
    fun hx => ?_⟩⟩
  · rintro _ ⟨f, -, n, rfl⟩
    exact ⟨n, homogeneousComponent_isHomogeneous n f⟩
  · rintro _ ⟨f, hf, n, rfl⟩
    refine eval_homogeneousComponent_eq_zero (fun c => ?_) n
    have hcx : c • x ∈ X := hc c x hx
    rw [hI, Set.mem_preimage, mem_zeroLocus_iff, map_smul] at hcx
    exact hcx f hf
  · rw [hI, Set.mem_preimage, mem_zeroLocus_iff]
    intro f hf
    change eval (b.equivFun x) f = 0
    rw [← sum_homogeneousComponent f, map_sum]
    exact Finset.sum_eq_zero fun e _ => hx _ ⟨f, hf, e, rfl⟩

theorem mem_span_singleton_iff_forall_mul_eq {V : Type v} [AddCommGroup V] [Module k V]
    {σ : Type*} [Fintype σ] (b : Module.Basis σ k V) {x : V} (hx : x ≠ 0) (u : V) :
    u ∈ k ∙ x ↔ ∀ i j, b.equivFun u i * b.equivFun x j = b.equivFun u j * b.equivFun x i := by
  constructor
  · intro hu i j
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    ring
  · intro h
    obtain ⟨j, hj⟩ : ∃ j, b.equivFun x j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hx (b.equivFun.injective (by rw [map_zero]; exact funext hcon))
    refine Submodule.mem_span_singleton.mpr
      ⟨b.equivFun u j / b.equivFun x j, b.equivFun.injective (funext fun i => ?_)⟩
    rw [map_smul, Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, ← h i j]
    exact mul_div_cancel_right₀ _ hj

variable {H : Type v} [CommRing H] [HopfAlgebra k H]
variable {W : Type w} [AddCommGroup W] [Module k W] [TauCeti.Comodule k H W]

theorem equivFun_basePointsRepresentation {σ : Type*} [Fintype σ] (b : Module.Basis σ k W)
    (F : W →ₗ[k] W) (g : WithConv (H →ₐ[k] k)) (x : W) (i : σ) :
    b.equivFun (basePointsRepresentation (H := H) W g (F x)) i =
      ∑ l, g.ofConv (matrixCoefficient (C := H) (b.coord i) (F (b l))) * b.equivFun x l := by
  simp only [apply_matrixCoefficient]
  conv_lhs => rw [← b.sum_equivFun x]
  rw [map_sum, map_sum, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, map_smul, map_smul, Pi.smul_apply, smul_eq_mul, Module.Basis.coord_apply]
  simp only [Module.Basis.equivFun_apply]
  ring

variable (H) in
@[expose] def minorPoly {σ : Type*} [Fintype σ] (b : Module.Basis σ k W) (F : W →ₗ[k] W)
    (i j : σ) : MvPolynomial σ H :=
  (∑ l, C (matrixCoefficient (C := H) (b.coord i) (F (b l))) * X l) * X j -
    (∑ l, C (matrixCoefficient (C := H) (b.coord j) (F (b l))) * X l) * X i

theorem isHomogeneous_minorPoly {σ : Type*} [Fintype σ] (b : Module.Basis σ k W)
    (F : W →ₗ[k] W) (i j : σ) : (minorPoly H b F i j).IsHomogeneous 2 := by
  have hlin : ∀ i', (∑ l, C (matrixCoefficient (C := H) (b.coord i') (F (b l))) * X l :
      MvPolynomial σ H).IsHomogeneous 1 := fun i' =>
    IsHomogeneous.sum _ _ _ fun l _ => (isHomogeneous_C_mul_X _ l)
  exact ((hlin i).mul (isHomogeneous_X H j)).sub ((hlin j).mul (isHomogeneous_X H i))

theorem eval_map_minorPoly {σ : Type*} [Fintype σ] (b : Module.Basis σ k W) (F : W →ₗ[k] W)
    (i j : σ) (g : WithConv (H →ₐ[k] k)) (x : W) :
    eval (b.equivFun x) (map (g.ofConv : H →+* k) (minorPoly H b F i j)) =
      b.equivFun (basePointsRepresentation (H := H) W g (F x)) i * b.equivFun x j -
        b.equivFun (basePointsRepresentation (H := H) W g (F x)) j * b.equivFun x i := by
  simp only [minorPoly, map_sub, map_mul, map_sum, map_C, map_X, eval_X, eval_C,
    equivFun_basePointsRepresentation]
  rfl

theorem exists_ideal_forall_iff_exists_apply_mem_span [IsAlgClosed k] [FiniteDimensional k W]
    {X : Set W} (hX : IsZariskiClosed k X) (hc : IsCone k X) (F : W →ₗ[k] W) :
    ∃ J : Ideal H, ∀ g : WithConv (H →ₐ[k] k), (∀ a ∈ J, g.ofConv a = 0) ↔
      ∃ x ∈ X, x ≠ 0 ∧ basePointsRepresentation (H := H) W g (F x) ∈ k ∙ x := by
  let b := Module.finBasis k W
  obtain ⟨S₀, hS₀, hX'⟩ := hX.exists_isHomogeneous hc b
  let S : Set (MvPolynomial (Fin (Module.finrank k W)) H) :=
    map (algebraMap k H) '' S₀ ∪ Set.range fun ij : Fin _ × Fin _ => minorPoly H b F ij.1 ij.2
  have hS : ∀ f ∈ S, ∃ n, f.IsHomogeneous n := by
    rintro f (⟨p, hp, rfl⟩ | ⟨ij, rfl⟩)
    · obtain ⟨n, hn⟩ := hS₀ p hp
      exact ⟨n, hn.map _⟩
    · exact ⟨2, isHomogeneous_minorPoly b F ij.1 ij.2⟩
  have hmap : ∀ (g : WithConv (H →ₐ[k] k)) (p : MvPolynomial (Fin (Module.finrank k W)) k),
      map (g.ofConv : H →+* k) (map (algebraMap k H) p) = p := fun g p => by
    rw [map_map, AlgHom.comp_algebraMap, Algebra.algebraMap_self, map_id]
  refine ⟨CFSG.eliminationIdeal S, fun g => ?_⟩
  rw [CFSG.forall_mem_eliminationIdeal_iff hS g.ofConv]
  constructor
  · rintro ⟨v, hv, hvS⟩
    have hx0 : b.equivFun.symm v ≠ 0 := fun h0 => hv (by
      rw [← b.equivFun.apply_symm_apply v, h0, map_zero])
    refine ⟨b.equivFun.symm v, (hX' _).mpr fun p hp => ?_, hx0,
      (mem_span_singleton_iff_forall_mul_eq b hx0 _).mpr fun i j => ?_⟩
    · have h := hvS _ (Or.inl ⟨p, hp, rfl⟩)
      rwa [hmap, ← b.equivFun.apply_symm_apply v] at h
    · have h := hvS _ (Or.inr ⟨(i, j), rfl⟩)
      rw [← b.equivFun.apply_symm_apply v, eval_map_minorPoly, sub_eq_zero] at h
      exact h
  · rintro ⟨x, hxX, hx0, hgx⟩
    refine ⟨b.equivFun x, fun h => hx0 (b.equivFun.injective (by rw [h, map_zero])), ?_⟩
    rintro f (⟨p, hp, rfl⟩ | ⟨ij, rfl⟩)
    · rw [hmap]
      exact (hX' x).mp hxX p hp
    · rw [eval_map_minorPoly, sub_eq_zero]
      exact (mem_span_singleton_iff_forall_mul_eq b hx0 _).mp hgx ij.1 ij.2

theorem exists_ideal_forall_iff_exists_mem_span [IsAlgClosed k] [FiniteDimensional k W]
    {X : Set W} (hX : IsZariskiClosed k X) (hc : IsCone k X) :
    ∃ J : Ideal H, ∀ g : WithConv (H →ₐ[k] k), (∀ a ∈ J, g.ofConv a = 0) ↔
      ∃ x ∈ X, x ≠ 0 ∧ basePointsRepresentation (H := H) W g x ∈ k ∙ x := by
  simpa only [LinearMap.id_apply] using
    exists_ideal_forall_iff_exists_apply_mem_span (H := H) hX hc LinearMap.id

end CFSG.LieType.AlgebraicGroups.ClosedCone
