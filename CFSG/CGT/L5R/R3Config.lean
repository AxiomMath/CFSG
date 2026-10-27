module

public import CFSG.CGT.L5R.R3Data
public import CFSG.CGT.L5R.Interfaces
public import CFSG.CGT.M24R.Assembly
public import CFSG.CGT.M24R.L2TabBase

public section

namespace CFSG.CGT.L5R.R3

open CFSG.CGT.Timmesfeld75 CFSG.CosetTable CFSG.CGT.M24R

theorem n8_inv10 (w : N0Word) : n8 (inv10 w) = (n8 w)⁻¹ := by
  rw [n8, n8, ← map_inv, FreeGroup.inv_mk, FreeGroup.invRev, inv10, List.map_reverse]

theorem n8_mem_tSub {w : N0Word} (hw : ∀ l ∈ w, l.2 = true ∧ 6 ≤ l.1.val) :
    n8 w ∈ Subgroup.closure (Set.range tGen8) := by
  induction w with
  | nil => rw [n8_nil]; exact Subgroup.one_mem _
  | cons l w ih =>
    rw [show l :: w = [l] ++ w from rfl, n8_append]
    refine Subgroup.mul_mem _ ?_ (ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    obtain ⟨⟨k, hk⟩, b⟩ := l
    obtain ⟨hb, h6⟩ := hw _ (List.mem_cons_self ..)
    have h6' : 6 ≤ k := h6
    subst hb
    refine Subgroup.subset_closure ⟨⟨k - 6, by omega⟩, ?_⟩
    have e : (⟨6 + (k - 6), by omega⟩ : Fin 10) = ⟨k, hk⟩ := Fin.ext (by simp only; omega)
    show PresentedGroup.of (⟨6 + (k - 6), by omega⟩ : Fin 10) = PresentedGroup.of ⟨k, hk⟩
    rw [e]

variable {G : Type} [Group G] {T T₁ : Subgroup G}

@[expose] def cphi (c : T1ConfigL T T₁) : N8 →* G :=
  (Subgroup.normalizer (T : Set G)).subtype.comp c.ψ.toMonoidHom

theorem cphi_injective (c : T1ConfigL T T₁) : Function.Injective (cphi c) :=
  Subtype.val_injective.comp c.ψ.injective

theorem cphi_apply (c : T1ConfigL T T₁) (x : N8) : cphi c x = ((c.ψ x : _) : G) := rfl

theorem evalW_liftW10' (c : T1ConfigL T T₁) (w : N0Word) :
    evalW c.gens (liftW10 w) = cphi c (n8 w) := by
  rw [evalW_liftW10]
  have h2 : (FreeGroup.lift (fun i : Fin 10 => c.gens (Fin.castSucc i)) :
      FreeGroup (Fin 10) →* G) = (cphi c).comp (PresentedGroup.mk _) := by
    apply FreeGroup.ext_hom
    intro i
    simp [T1ConfigL.gens, genTuple8, PresentedGroup.mk, cphi]
    rfl
  rw [h2]
  rfl

theorem gens_letG (c : T1ConfigL T T₁) : c.gens letG = c.g := by
  simp [T1ConfigL.gens, genTuple8, letG]

theorem g_mul_g (c : T1ConfigL T T₁) : c.g * c.g = 1 := by
  have h := c.rel [(10, true), (10, true)] (by simp [thetaRelsL])
  change evalW c.gens _ = 1 at h
  have e : ([(10, true), (10, true)] : M24Word) = (letG, true) :: [(letG, true)] := rfl
  rw [e, evalW_cons_true, evalW_cons_true, evalW_nil, mul_one, gens_letG] at h
  exact h

theorem g_inv (c : T1ConfigL T T₁) : c.g⁻¹ = c.g :=
  inv_eq_of_mul_eq_one_right (g_mul_g c)

theorem conj_dW (c : T1ConfigL T T₁) (i : Fin 2) :
    c.g * cphi c (n8 (dW i)) * c.g⁻¹ = cphi c (n8 (thW i)) := by
  have hmem : (letG, true) :: dWordL i ++ (letG, true) :: invW (thetaWordL i) ∈ thetaRelsL := by
    fin_cases i <;> decide
  have h := c.rel _ hmem
  change evalW c.gens _ = 1 at h
  rw [List.cons_append, evalW_cons_true, evalW_append, evalW_cons_true, evalW_invW,
    ← liftW10_dW, ← liftW10_thW, evalW_liftW10', evalW_liftW10', gens_letG] at h
  rw [g_inv]
  calc c.g * cphi c (n8 (dW i)) * c.g
      = c.g * (cphi c (n8 (dW i)) * (c.g * (cphi c (n8 (thW i)))⁻¹)) * cphi c (n8 (thW i)) := by
        group
    _ = cphi c (n8 (thW i)) := by rw [h, one_mul]

theorem conj_dExp (c : T1ConfigL T T₁) (u : List (Fin 2 × Bool)) :
    c.g * cphi c (n8 (dExp u)) * c.g⁻¹ = cphi c (n8 (thExp u)) := by
  induction u with
  | nil =>
    show c.g * cphi c (n8 []) * c.g⁻¹ = cphi c (n8 [])
    rw [n8_nil, map_one, mul_one, mul_inv_cancel]
  | cons p u ih =>
    have h1 : dExp (p :: u) = (if p.2 then dW p.1 else inv10 (dW p.1)) ++ dExp u := rfl
    have h2 : thExp (p :: u) = (if p.2 then thW p.1 else inv10 (thW p.1)) ++ thExp u := rfl
    rw [h1, h2, n8_append, n8_append, map_mul, map_mul]
    have hl : c.g * cphi c (n8 (if p.2 then dW p.1 else inv10 (dW p.1))) * c.g⁻¹ =
        cphi c (n8 (if p.2 then thW p.1 else inv10 (thW p.1))) := by
      obtain ⟨i, b⟩ := p
      cases b
      · simp only [Bool.false_eq_true, ite_false, n8_inv10, map_inv]
        rw [← conj_dW c i]
        group
      · exact conj_dW c i
    rw [← hl, ← ih]
    group

theorem card_N8 (hyp : L52CtxHyp T T₁) (c : T1ConfigL T T₁) : Nat.card N8 = 322560 := by
  rw [Nat.card_congr c.ψ.toEquiv,
    Subgroup.card_eq_card_quotient_mul_card_subgroup (T.subgroupOf _)]
  obtain ⟨e⟩ := hyp.quot
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv, hyp.card16,
    Nat.card_fin]
  decide

theorem cphi_mem_T (c : T1ConfigL T T₁) {x : N8}
    (hx : x ∈ Subgroup.closure (Set.range tGen8)) : cphi c x ∈ T := by
  have h : c.ψ x ∈ (Subgroup.closure (Set.range tGen8)).map c.ψ.toMonoidHom :=
    Subgroup.mem_map_of_mem _ hx
  rw [c.map_t, Subgroup.mem_subgroupOf] at h
  exact h

end CFSG.CGT.L5R.R3
