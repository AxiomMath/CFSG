module

public import CFSG.CGT.A8S.R3Model
public import CFSG.CGT.A8S.Interfaces

public section

namespace CFSG.CGT.A8S.R3

open CFSG.CosetTable

variable {G : Type} [Group G] {T T₁ : Subgroup G}

@[expose] def cphi (c : T1ConfigA8 T T₁) : PG 5 relsN0A8 →* G :=
  (Subgroup.normalizer (T : Set G)).subtype.comp c.ψ.toMonoidHom

theorem cphi_injective (c : T1ConfigA8 T T₁) : Function.Injective (cphi c) :=
  Subtype.val_injective.comp c.ψ.injective

theorem cphi_apply (c : T1ConfigA8 T T₁) (x : PG 5 relsN0A8) : cphi c x = ((c.ψ x : _) : G) :=
  rfl

theorem gens_five (c : T1ConfigA8 T T₁) : c.gens 5 = c.g := by
  simp [T1ConfigA8.gens, genTupleA8]

theorem gens_castSucc (c : T1ConfigA8 T T₁) (i : Fin 5) :
    c.gens (Fin.castSucc i) = cphi c (PresentedGroup.of i) := by
  simp [T1ConfigA8.gens, genTupleA8, cphi]

theorem evalA8_liftW5' (c : T1ConfigA8 T T₁) (w : List (Fin 5 × Bool)) :
    evalA8 c.gens (liftW5 w) = cphi c (n0v w) := by
  rw [evalA8_liftW5]
  have h : FreeGroup.lift (fun i : Fin 5 => c.gens (Fin.castSucc i)) =
      (cphi c).comp (PresentedGroup.mk _) := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    rw [FreeGroup.lift_apply_of, gens_castSucc]
    rfl
  rw [h]
  rfl

theorem cphi_mem_T (c : T1ConfigA8 T T₁) {x : PG 5 relsN0A8}
    (hx : x ∈ Subgroup.closure (Set.range tGenA8)) : cphi c x ∈ T := by
  have h : c.ψ x ∈ (Subgroup.closure (Set.range tGenA8)).map c.ψ.toMonoidHom :=
    Subgroup.mem_map_of_mem _ hx
  rw [c.map_t, Subgroup.mem_subgroupOf] at h
  exact h

theorem thetaRelsA8_eq : thetaRelsA8 = [[(5, true), (5, true)],
    (5, true) :: dWordA8 0 ++ (5, true) :: invA8 (thetaWordA8 0),
    (5, true) :: dWordA8 1 ++ (5, true) :: invA8 (thetaWordA8 1)] := by
  decide

theorem g_mul_g (c : T1ConfigA8 T T₁) : c.g * c.g = 1 := by
  have h := c.rel [(5, true), (5, true)] (by rw [thetaRelsA8_eq]; exact List.mem_cons_self ..)
  change evalA8 c.gens _ = 1 at h
  rw [evalA8_cons_true, evalA8_cons_true, evalA8_nil, mul_one, gens_five] at h
  exact h

theorem g_inv (c : T1ConfigA8 T T₁) : c.g⁻¹ = c.g :=
  inv_eq_of_mul_eq_one_right (g_mul_g c)

theorem conj_dW (c : T1ConfigA8 T T₁) (i : Fin 2) :
    c.g * cphi c (n0v (dW i)) * c.g⁻¹ = cphi c (n0v (thW i)) := by
  have hmem : (5, true) :: dWordA8 i ++ (5, true) :: invA8 (thetaWordA8 i) ∈ thetaRelsA8 := by
    rw [thetaRelsA8_eq]
    fin_cases i
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have h := c.rel _ hmem
  change evalA8 c.gens _ = 1 at h
  rw [List.cons_append, evalA8_cons_true, evalA8_append, evalA8_cons_true, evalA8_invA8,
    ← liftW5_dW, ← liftW5_thW, evalA8_liftW5', evalA8_liftW5', gens_five] at h
  rw [g_inv]
  calc c.g * cphi c (n0v (dW i)) * c.g
      = c.g * (cphi c (n0v (dW i)) * (c.g * (cphi c (n0v (thW i)))⁻¹)) *
          cphi c (n0v (thW i)) := by group
    _ = cphi c (n0v (thW i)) := by rw [h, one_mul]

theorem conj_dExp (c : T1ConfigA8 T T₁) (v : List (Fin 2 × Bool)) :
    c.g * cphi c (n0v (dExp v)) * c.g⁻¹ = cphi c (n0v (thExp v)) := by
  induction v with
  | nil =>
    show c.g * cphi c (n0v []) * c.g⁻¹ = cphi c (n0v [])
    rw [n0v_nil, map_one, mul_one, mul_inv_cancel]
  | cons p v ih =>
    have h1 : dExp (p :: v) = (if p.2 then dW p.1 else FreeGroup.invRev (dW p.1)) ++ dExp v :=
      rfl
    have h2 : thExp (p :: v) =
        (if p.2 then thW p.1 else FreeGroup.invRev (thW p.1)) ++ thExp v := rfl
    rw [h1, h2, n0v_append, n0v_append, map_mul, map_mul]
    have hl : c.g * cphi c (n0v (if p.2 then dW p.1 else FreeGroup.invRev (dW p.1))) * c.g⁻¹ =
        cphi c (n0v (if p.2 then thW p.1 else FreeGroup.invRev (thW p.1))) := by
      obtain ⟨i, b⟩ := p
      cases b
      · simp only [Bool.false_eq_true, ite_false, n0v_invRev, map_inv]
        rw [← conj_dW c i]
        group
      · exact conj_dW c i
    rw [← hl, ← ih]
    group

end CFSG.CGT.A8S.R3
