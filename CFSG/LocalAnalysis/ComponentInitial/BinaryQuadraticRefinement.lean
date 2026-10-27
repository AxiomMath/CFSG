module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.ComponentInitial

variable {U W : Type*} [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]

@[expose] noncomputable def coordBilin {ι : Type*} (e : Module.Basis ι (ZMod 2) U) (i j : ι)
    (w : W) : U →ₗ[ZMod 2] U →ₗ[ZMod 2] W :=
  LinearMap.mk₂ (ZMod 2) (fun u v => (e.coord i u * e.coord j v) • w)
    (fun u u' v => by simp [add_mul, add_smul])
    (fun c u v => by simp [mul_assoc, smul_smul])
    (fun u v v' => by simp [mul_add, add_smul])
    (fun c u v => by simp [smul_smul, mul_left_comm])

theorem coordBilin_apply {ι : Type*} (e : Module.Basis ι (ZMod 2) U) (i j : ι) (w : W)
    (u v : U) : coordBilin e i j w u v = (e.repr u i * e.repr v j) • w :=
  rfl

@[expose] noncomputable def bilinRefinement {n : ℕ} (e : Module.Basis (Fin n) (ZMod 2) U)
    (q : U → W) (B : U →ₗ[ZMod 2] U →ₗ[ZMod 2] W) : U →ₗ[ZMod 2] U →ₗ[ZMod 2] W :=
  (∑ i, coordBilin e i i (q (e i))) +
    ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
      coordBilin e p.1 p.2 (B (e p.1) (e p.2))

theorem bilinRefinement_apply {n : ℕ} (e : Module.Basis (Fin n) (ZMod 2) U) (q : U → W)
    (B : U →ₗ[ZMod 2] U →ₗ[ZMod 2] W) (u v : U) :
    bilinRefinement e q B u v = ∑ i, (e.repr u i * e.repr v i) • q (e i) +
      ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
        (e.repr u p.1 * e.repr v p.2) • B (e p.1) (e p.2) := by
  simp [bilinRefinement, LinearMap.sum_apply, coordBilin_apply]

theorem two_smul_eq_zero_of_zmod (w : W) : w + w = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem binary_quadratic_bilinear_refinement [FiniteDimensional (ZMod 2) U]
    (q : U → W) (hq0 : q 0 = 0) (B : U →ₗ[ZMod 2] U →ₗ[ZMod 2] W)
    (hB : ∀ u v, B u v = q (u + v) + q u + q v) :
    (∀ (n : ℕ) (e : Module.Basis (Fin n) (ZMod 2) U),
      (∀ u v, bilinRefinement e q B u v = ∑ i, (e.repr u i * e.repr v i) • q (e i) +
        ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
          (e.repr u p.1 * e.repr v p.2) • B (e p.1) (e p.2)) ∧
      ∀ u, bilinRefinement e q B u u = q u) ∧
    ∃ b : U →ₗ[ZMod 2] U →ₗ[ZMod 2] W, ∀ u, b u u = q u := by
  have hBsymm : ∀ u v, B u v = B v u := fun u v => by rw [hB, hB, add_comm u v]; abel
  have hBdiag : ∀ u, B u u = 0 := fun u => by
    rw [hB, two_smul_eq_zero_of_zmod u, hq0, zero_add, two_smul_eq_zero_of_zmod]
  have key : ∀ (n : ℕ) (e : Module.Basis (Fin n) (ZMod 2) U), ∀ u,
      bilinRefinement e q B u u = q u := by
    intro n e
    set b := bilinRefinement e q B
    have hadd : ∀ u v, q (u + v) - b (u + v) (u + v) = (q u - b u u) + (q v - b v v) := by
      intro u v
      have hpol : b (u + v) (u + v) = b u u + b v v + B u v := by
        simp only [map_add, LinearMap.add_apply]
        have hcross : b u v + b v u = B u v := by
          rw [bilinRefinement_apply, bilinRefinement_apply]
          have hexp : B u v = ∑ i, ∑ j, (e.repr u i * e.repr v j) • B (e i) (e j) := by
            have h1 : ∀ x : U, B x v = ∑ j, e.repr v j • B x (e j) := fun x => by
              conv_lhs => rw [← e.sum_repr v]
              rw [map_sum]
              simp only [map_smul]
            have h2 : B u v = ∑ i, e.repr u i • B (e i) v := by
              conv_lhs => rw [← e.sum_repr u]
              rw [map_sum, LinearMap.sum_apply]
              simp only [map_smul, LinearMap.smul_apply]
            rw [h2]
            simp only [h1, Finset.smul_sum, smul_smul]
          have hBexp : B u v = ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
              (e.repr u p.1 * e.repr v p.2 + e.repr v p.1 * e.repr u p.2) •
                B (e p.1) (e p.2) := by
            rw [hexp, ← Fintype.sum_prod_type' (fun i j => (e.repr u i * e.repr v j) •
              B (e i) (e j))]
            rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : Fin n × Fin n =>
              p.1 < p.2)]
            rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter fun p : Fin n × Fin n =>
              ¬ p.1 < p.2) (fun p : Fin n × Fin n => p.1 = p.2)]
            have hdiag0 : ∑ x ∈ (Finset.univ.filter fun p : Fin n × Fin n => ¬ p.1 < p.2).filter
                (fun p : Fin n × Fin n => p.1 = p.2),
                (e.repr u x.1 * e.repr v x.2) • B (e x.1) (e x.2) = 0 := by
              refine Finset.sum_eq_zero fun x hx => ?_
              rw [Finset.mem_filter] at hx
              rw [hx.2, hBdiag, smul_zero]
            rw [hdiag0, zero_add]
            have hswap : ∑ x ∈ (Finset.univ.filter fun p : Fin n × Fin n => ¬ p.1 < p.2).filter
                (fun p : Fin n × Fin n => ¬ p.1 = p.2),
                (e.repr u x.1 * e.repr v x.2) • B (e x.1) (e x.2) =
                ∑ x ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
                (e.repr v x.1 * e.repr u x.2) • B (e x.1) (e x.2) := by
              refine Finset.sum_nbij' Prod.swap Prod.swap (fun x hx => ?_) (fun x hx => ?_)
                (fun x _ => rfl) (fun x _ => rfl) (fun x _ => ?_)
              · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
                exact lt_of_le_of_ne (not_lt.1 hx.1) (Ne.symm hx.2)
              · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
                exact ⟨not_lt.2 hx.le, hx.ne'⟩
              · simp only [Prod.fst_swap, Prod.snd_swap]
                rw [hBsymm, mul_comm]
            rw [hswap, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun x _ => (add_smul _ _ _).symm
          rw [hBexp]
          have hdiagsum : ∑ i, (e.repr u i * e.repr v i) • q (e i) +
              ∑ i, (e.repr v i * e.repr u i) • q (e i) = 0 := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_eq_zero fun i _ => ?_
            rw [mul_comm (e.repr v i), two_smul_eq_zero_of_zmod]
          calc _ = (∑ i, (e.repr u i * e.repr v i) • q (e i) +
                ∑ i, (e.repr v i * e.repr u i) • q (e i)) +
              ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
                ((e.repr u p.1 * e.repr v p.2) • B (e p.1) (e p.2) +
                  (e.repr v p.1 * e.repr u p.2) • B (e p.1) (e p.2)) := by
                rw [Finset.sum_add_distrib]; abel
            _ = _ := by
                rw [hdiagsum, zero_add]
                exact Finset.sum_congr rfl fun x _ => (add_smul _ _ _).symm
        rw [← hcross]
        abel
      rw [hpol, hB u v, ← sub_eq_zero]
      have e : q (u + v) - (b u u + b v v + (q (u + v) + q u + q v)) -
          (q u - b u u + (q v - b v v)) = -((q u + q u) + (q v + q v)) := by abel
      rw [e, two_smul_eq_zero_of_zmod, two_smul_eq_zero_of_zmod, add_zero, neg_zero]
    let D : U →+ W := AddMonoidHom.mk' (fun u => q u - b u u) hadd
    have hDe : ∀ i, D (e i) = 0 := by
      intro i
      change q (e i) - b (e i) (e i) = 0
      rw [bilinRefinement_apply, sub_eq_zero]
      have h1 : ∑ j, (e.repr (e i) j * e.repr (e i) j) • q (e j) = q (e i) := by
        rw [Finset.sum_eq_single i (fun j _ hj => by simp [Module.Basis.repr_self, Ne.symm hj])
          (by simp)]
        simp [Module.Basis.repr_self]
      have h2 : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
          (e.repr (e i) p.1 * e.repr (e i) p.2) • B (e p.1) (e p.2) = 0 := by
        refine Finset.sum_eq_zero fun p hp => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        simp only [Module.Basis.repr_self, Finsupp.single_apply]
        by_cases h1 : i = p.1
        · have : i ≠ p.2 := fun h => absurd hp (by rw [← h1, ← h]; exact lt_irrefl _)
          simp [this]
        · simp [h1]
      rw [h1, h2, add_zero]
    have hDsmul : ∀ (c : ZMod 2) (x : U), D x = 0 → D (c • x) = 0 := by
      intro c x hx
      rcases (by revert c; decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
      · rw [zero_smul, map_zero]
      · rw [one_smul]
        exact hx
    intro u
    have hDu : D u = 0 := by
      rw [← e.sum_repr u, map_sum]
      exact Finset.sum_eq_zero fun i _ => hDsmul _ _ (hDe i)
    exact (sub_eq_zero.1 hDu).symm
  refine ⟨fun n e => ⟨bilinRefinement_apply e q B, key n e⟩, ?_⟩
  exact ⟨bilinRefinement (Module.finBasisOfFinrankEq (ZMod 2) U rfl) q B, key _ _⟩

end CFSG.LocalAnalysis.ComponentInitial
