module

public import CFSG.CGT.M24R.R3Count
public import CFSG.CGT.M24R.Assembly

public section

namespace CFSG.CGT.M24R.R3

open CFSG.CGT.Timmesfeld75 CFSG.CosetTable

variable {G : Type} [Group G] {T T₁ : Subgroup G}

@[expose] def cphi (c : T1Config8 T T₁) : N0 →* G :=
  (Subgroup.normalizer (T : Set G)).subtype.comp c.ψ.toMonoidHom

theorem cphi_injective (c : T1Config8 T T₁) : Function.Injective (cphi c) :=
  Subtype.val_injective.comp c.ψ.injective

theorem cphi_apply (c : T1Config8 T T₁) (x : N0) : cphi c x = ((c.ψ x : _) : G) := rfl

theorem evalW_liftW10' (c : T1Config8 T T₁) (w : N0Word) :
    evalW c.gens (liftW10 w) = cphi c (n0 w) := by
  rw [evalW_liftW10]
  have h2 : (FreeGroup.lift (fun i : Fin 10 => c.gens (Fin.castSucc i)) :
      FreeGroup (Fin 10) →* G) = (cphi c).comp (PresentedGroup.mk _) := by
    apply FreeGroup.ext_hom
    intro i
    simp [T1Config8.gens, genTuple8, PresentedGroup.mk, cphi]
    rfl
  rw [h2]
  rfl

theorem gens_letG (c : T1Config8 T T₁) : c.gens letG = c.g := by
  simp [T1Config8.gens, genTuple8, letG]

theorem g_mul_g (c : T1Config8 T T₁) : c.g * c.g = 1 := by
  have h := c.rel [(10, true), (10, true)] (by simp [thetaRels8])
  change evalW c.gens _ = 1 at h
  have e : ([(10, true), (10, true)] : M24Word) = (letG, true) :: [(letG, true)] := rfl
  rw [e, evalW_cons_true, evalW_cons_true, evalW_nil, mul_one, gens_letG] at h
  exact h

theorem g_inv (c : T1Config8 T T₁) : c.g⁻¹ = c.g :=
  inv_eq_of_mul_eq_one_right (g_mul_g c)

theorem conj_dW (c : T1Config8 T T₁) (i : Fin 3) :
    c.g * cphi c (n0 (dW i)) * c.g⁻¹ = cphi c (n0 (thW i)) := by
  have hmem : (letG, true) :: dWord i ++ (letG, true) :: invW (thetaWord i) ∈ thetaRels8 := by
    rw [thetaRels8_eq]
    exact List.mem_cons_of_mem _ (List.mem_ofFn.2 ⟨i, rfl⟩)
  have h := c.rel _ hmem
  change evalW c.gens _ = 1 at h
  rw [List.cons_append, evalW_cons_true, evalW_append, evalW_cons_true, evalW_invW,
    ← liftW10_dW, ← liftW10_thW, evalW_liftW10', evalW_liftW10', gens_letG] at h
  rw [g_inv]
  calc c.g * cphi c (n0 (dW i)) * c.g
      = c.g * (cphi c (n0 (dW i)) * (c.g * (cphi c (n0 (thW i)))⁻¹)) * cphi c (n0 (thW i)) := by
        group
    _ = cphi c (n0 (thW i)) := by rw [h, one_mul]

theorem conj_dExp (c : T1Config8 T T₁) (u : List (Fin 3 × Bool)) :
    c.g * cphi c (n0 (dExp u)) * c.g⁻¹ = cphi c (n0 (thExp u)) := by
  induction u with
  | nil =>
    show c.g * cphi c (n0 []) * c.g⁻¹ = cphi c (n0 [])
    rw [n0_nil, map_one, mul_one, mul_inv_cancel]
  | cons p u ih =>
    have h1 : dExp (p :: u) = (if p.2 then dW p.1 else inv10 (dW p.1)) ++ dExp u := rfl
    have h2 : thExp (p :: u) = (if p.2 then thW p.1 else inv10 (thW p.1)) ++ thExp u := rfl
    rw [h1, h2, n0_append, n0_append, map_mul, map_mul]
    have hl : c.g * cphi c (n0 (if p.2 then dW p.1 else inv10 (dW p.1))) * c.g⁻¹ =
        cphi c (n0 (if p.2 then thW p.1 else inv10 (thW p.1))) := by
      obtain ⟨i, b⟩ := p
      cases b
      · simp only [Bool.false_eq_true, ite_false, n0_inv10, map_inv]
        rw [← conj_dW c i]
        group
      · exact conj_dW c i
    rw [← hl, ← ih]
    group

theorem finite_N0 [Finite G] (c : T1Config8 T T₁) : Finite N0 :=
  Finite.of_equiv _ c.ψ.symm.toEquiv

theorem card_N0 (hyp : M24CtxHyp T T₁) (c : T1Config8 T T₁) : Nat.card N0 = 322560 := by
  rw [Nat.card_congr c.ψ.toEquiv,
    Subgroup.card_eq_card_quotient_mul_card_subgroup (T.subgroupOf _)]
  obtain ⟨e⟩ := hyp.quot
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv, hyp.card16,
    Nat.card_fin]
  decide

abbrev tSub : Subgroup N0 := Subgroup.closure (Set.range tGen8)

theorem n0_mem_tSub {w : N0Word} (hw : ∀ l ∈ w, l.2 = true ∧ 6 ≤ l.1.val) : n0 w ∈ tSub := by
  induction w with
  | nil => rw [n0_nil]; exact Subgroup.one_mem _
  | cons l w ih =>
    rw [show l :: w = [l] ++ w from rfl, n0_append]
    refine Subgroup.mul_mem _ ?_ (ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    obtain ⟨⟨k, hk⟩, b⟩ := l
    obtain ⟨hb, h6⟩ := hw _ (List.mem_cons_self ..)
    have h6' : 6 ≤ k := h6
    subst hb
    refine Subgroup.subset_closure ⟨⟨k - 6, by omega⟩, ?_⟩
    have e : (⟨6 + (k - 6), by omega⟩ : Fin 10) = ⟨k, hk⟩ := Fin.ext (by simp only; omega)
    show PresentedGroup.of (⟨6 + (k - 6), by omega⟩ : Fin 10) = PresentedGroup.of ⟨k, hk⟩
    rw [e]

theorem n0_tWordOf_mem (v : Fin 16) : n0 (tWordOf v) ∈ tSub := by
  refine n0_mem_tSub fun l hl => ?_
  simp only [tWordOf, List.mem_map] at hl
  obtain ⟨j, -, rfl⟩ := hl
  exact ⟨rfl, by simp⟩

theorem tWordOf_zero : tWordOf 0 = [] := by decide

theorem rho_ne_of_nEq (h : relCheck = true) {w w' : N0Word} (hw : nEq w w' = false) :
    rho h (n0 w) ≠ rho h (n0 w') := by
  intro e
  have := tabEq_of_perm_eq (rep_wTab w) (rep_wTab w') (by rw [← rho_n0 h, ← rho_n0 h, e])
  rw [nEq] at hw
  rw [hw] at this
  exact Bool.false_ne_true this

section Faithful

variable (ψ : N0 ≃* ↥(Subgroup.normalizer (T : Set G)))
  (hψ : Subgroup.map ψ.toMonoidHom (Subgroup.closure (Set.range tGen8)) =
    T.subgroupOf (Subgroup.normalizer (T : Set G)))

include hψ in
theorem mem_tSub_iff (x : N0) : x ∈ tSub ↔ ((ψ x : _) : G) ∈ T := by
  constructor
  · intro hx
    have : ψ x ∈ tSub.map ψ.toMonoidHom := Subgroup.mem_map_of_mem _ hx
    rw [hψ, Subgroup.mem_subgroupOf] at this
    exact this
  · intro hx
    have : ψ x ∈ T.subgroupOf (Subgroup.normalizer (T : Set G)) := Subgroup.mem_subgroupOf.2 hx
    rw [← hψ, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at this
    exact this

include hψ in
theorem card_tSub (h16 : Nat.card T = 16) : Nat.card tSub = 16 := by
  rw [← Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, hψ,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv, h16]

include hψ in
theorem exists_tWordOf [Finite G] (h16 : Nat.card T = 16) (h : relCheck = true)
    (hd : distinctCheck = true) {x : N0} (hx : x ∈ tSub) : ∃ v, x = n0 (tWordOf v) := by
  have : Finite N0 := Finite.of_equiv _ ψ.symm.toEquiv
  let f : Fin 16 → tSub := fun v => ⟨n0 (tWordOf v), n0_tWordOf_mem v⟩
  have hf : Function.Injective f := by
    intro v v' hvv
    by_contra hne
    exact n0_ne_of_nEq h ((distinctCheck_spec hd).2 v v' hne) (congrArg Subtype.val hvv)
  have hb := hf.bijective_of_nat_card_le (by rw [Nat.card_fin, card_tSub ψ hψ h16])
  obtain ⟨v, hv⟩ := hb.2 ⟨x, hx⟩
  exact ⟨v, (congrArg Subtype.val hv).symm⟩

include hψ in
theorem eq_one_of_mem_tSub [Finite G] (h16 : Nat.card T = 16) (h : relCheck = true)
    (hd : distinctCheck = true) {x : N0} (hx : x ∈ tSub) (h1 : rho h x = 1) : x = 1 := by
  obtain ⟨v, rfl⟩ := exists_tWordOf ψ hψ h16 h hd hx
  by_cases hv : v = 0
  · rw [hv, tWordOf_zero, n0_nil]
  · exfalso
    apply rho_ne_of_nEq h ((distinctCheck_spec hd).2 v 0 hv)
    rw [h1, tWordOf_zero, n0_nil, map_one]

include hψ in
theorem rho_injective_of_psi [Finite G] (h16 : Nat.card T = 16)
    (hcent : Subgroup.centralizer (T : Set G) = T) (h : relCheck = true)
    (hd : distinctCheck = true) : Function.Injective (rho h) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hcomm : ∀ t ∈ T, t * ((ψ x : _) : G) = ((ψ x : _) : G) * t := by
    intro t ht
    set τ : N0 := ψ.symm ⟨t, Subgroup.le_normalizer ht⟩ with hτdef
    have hτ : ((ψ τ : _) : G) = t := by rw [hτdef, MulEquiv.apply_symm_apply]
    have hkS : x * τ * x⁻¹ * τ⁻¹ ∈ tSub := by
      rw [mem_tSub_iff ψ hψ, map_mul, map_mul, map_mul, map_inv, map_inv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hτ]
      have hxN : ((ψ x : _) : G) ∈ Subgroup.normalizer (T : Set G) := (ψ x).2
      exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.1 hxN t).1 ht) (Subgroup.inv_mem _ ht)
    have hk1 : rho h (x * τ * x⁻¹ * τ⁻¹) = 1 := by
      simp only [map_mul, map_inv, hx, one_mul, inv_one, mul_one, mul_inv_cancel]
    have hk := eq_one_of_mem_tSub ψ hψ h16 h hd hkS hk1
    have hxτ : x * τ = τ * x := by
      calc x * τ = x * τ * x⁻¹ * τ⁻¹ * (τ * x) := by group
        _ = τ * x := by rw [hk, one_mul]
    have := congrArg (fun y => ((ψ y : _) : G)) hxτ
    simp only [map_mul, Subgroup.coe_mul, hτ] at this
    exact this.symm
  have hC : ((ψ x : _) : G) ∈ Subgroup.centralizer (T : Set G) :=
    Subgroup.mem_centralizer_iff.2 hcomm
  rw [hcent] at hC
  exact eq_one_of_mem_tSub ψ hψ h16 h hd ((mem_tSub_iff ψ hψ x).2 hC) hx

end Faithful

theorem rho_injective [Finite G] (hyp : M24CtxHyp T T₁) (c : T1Config8 T T₁) (h : relCheck = true)
    (hd : distinctCheck = true) : Function.Injective (rho h) :=
  rho_injective_of_psi c.ψ c.map_t hyp.card16 hyp.cent_eq h hd

end CFSG.CGT.M24R.R3
