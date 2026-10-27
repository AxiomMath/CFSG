module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888E2
import Mathlib.Tactic.Group

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {X : Type} [Group X] {V : Subgroup X} {W : Fin 4 → Subgroup X}

noncomputable def comp (hS : PlaneSys V W) (v : V) : Fin 4 → X :=
  Classical.choose (hS.decomp (v : X) v.2)

theorem comp_mem (hS : PlaneSys V W) (v : V) (i : Fin 4) : comp hS v i ∈ W i :=
  (Classical.choose_spec (hS.decomp (v : X) v.2)).1 i

theorem prod_comp (hS : PlaneSys V W) (v : V) :
    (v : X) = comp hS v 0 * comp hS v 1 * comp hS v 2 * comp hS v 3 :=
  (Classical.choose_spec (hS.decomp (v : X) v.2)).2

theorem comp_injective (hS : PlaneSys V W) : Function.Injective (comp hS) := by
  intro v v' hvv
  apply Subtype.ext
  rw [prod_comp hS v, prod_comp hS v', hvv]

private theorem s888_conj_prod_four (y a b c d : X) :
    (y * a * y⁻¹) * (y * b * y⁻¹) * (y * c * y⁻¹) * (y * d * y⁻¹)
      = y * (a * b * c * d) * y⁻¹ := by
  group

private theorem s888_prod_perm_four {M : Type*} [Monoid M] (f : Fin 4 → M)
    (τ : Equiv.Perm (Fin 4)) (hc : ∀ a b : Fin 4, Commute (f a) (f b)) :
    f (τ 0) * f (τ 1) * f (τ 2) * f (τ 3) = f 0 * f 1 * f 2 * f 3 := by
  have hperm : List.Perm (List.ofFn (f ∘ τ)) (List.ofFn f) := Equiv.Perm.ofFn_comp_perm τ f
  have hpair : (List.ofFn (f ∘ τ)).Pairwise Commute := by
    rw [List.pairwise_ofFn]
    intro i j _
    exact hc _ _
  have h := hperm.prod_eq' hpair
  simpa [List.ofFn_succ, List.prod_cons, mul_assoc] using h

theorem comp_fixed (hS : PlaneSys V W) (v : V) (y : normalizer (V : Set X))
    (hv : (y : X) * (v : X) * (y : X)⁻¹ = v) (i : Fin 4) :
    comp hS v (planeHom hS y i) = (y : X) * comp hS v i * (y : X)⁻¹ := by
  classical
  let w : Fin 4 → X := comp hS v
  have hw : ∀ j, w j ∈ W j := fun j => comp_mem hS v j
  have hvprod : (v : X) = w 0 * w 1 * w 2 * w 3 := prod_comp hS v
  let u : Fin 4 → ↥V := fun j =>
    ⟨(y : X) * w j * (y : X)⁻¹,
      hS.le (planeHom hS y j) (planeHom_spec hS y j (w j) (hw j))⟩
  have hu : ∀ j, (u j : X) = (y : X) * w j * (y : X)⁻¹ := fun _ => rfl
  have hmem : ∀ k, (u ((planeHom hS y).symm k) : X) ∈ W k := by
    intro k
    have h := planeHom_spec hS y ((planeHom hS y).symm k) (w ((planeHom hS y).symm k))
      (hw ((planeHom hS y).symm k))
    rwa [Equiv.apply_symm_apply] at h
  have hcomm : ∀ a b : Fin 4, Commute (u a : X) (u b : X) :=
    fun a b => hS.comm (u a) (u a).2 (u b) (u b).2
  have hreorder : (u ((planeHom hS y).symm 0) : X) * (u ((planeHom hS y).symm 1) : X)
      * (u ((planeHom hS y).symm 2) : X) * (u ((planeHom hS y).symm 3) : X)
      = (u 0 : X) * (u 1 : X) * (u 2 : X) * (u 3 : X) :=
    s888_prod_perm_four (fun j => (u j : X)) ((planeHom hS y).symm) hcomm
  have huv : (u 0 : X) * (u 1 : X) * (u 2 : X) * (u 3 : X) = (v : X) := by
    rw [hu 0, hu 1, hu 2, hu 3, s888_conj_prod_four, ← hvprod, hv]
  have hfun : (fun k => (u ((planeHom hS y).symm k) : X)) = w :=
    hS.eq_of_prod_eq hmem hw (by rw [hreorder, huv, hvprod])
  have hcongr : (u ((planeHom hS y).symm (planeHom hS y i)) : X) = w (planeHom hS y i) :=
    congrFun hfun (planeHom hS y i)
  rw [Equiv.symm_apply_apply] at hcongr
  exact hcongr.symm.trans (hu i)

end CFSG.OddStandard.SmallF3.Omega
