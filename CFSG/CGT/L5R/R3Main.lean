module

public import CFSG.CGT.L5R.R3Config
public import CFSG.CGT.L5R.R3Model

public section

namespace CFSG.CGT.L5R.R3

open CFSG.CGT.Timmesfeld75 CFSG.CGT.M24R

structure R3FactsL : Prop where
  ident : identCheck = true
  cent : centCheck (mkCtx ()) = true

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem r3_core (hf : R3FactsL) (hyp : L52CtxHyp T T₁)
    (c : T1ConfigL T T₁) :
    c.g * cphi c (n8 nW) * c.g * (cphi c (n8 nW))⁻¹ * c.g = cphi c (n8 wW) := by
  have hcard := card_N8 hyp c
  obtain ⟨hu, hb, hbD, hd, hd0, hy⟩ := identCheck_spec hf.ident
  have eqN : ∀ {w w' : N0Word}, tEq w w' = true → n8 w = n8 w' := fun hw =>
    n8_eq_of_tEq hcard hw
  have hg : c.g⁻¹ = c.g := g_inv c
  have hU : c.g * cphi c (n8 (dExp uD)) * c.g⁻¹ = cphi c (n8 (dExp uD)) := by
    rw [conj_dExp c uD, eqN hu]
  have hgU : c.g * cphi c (n8 (dExp uD)) = cphi c (n8 (dExp uD)) * c.g := by
    calc c.g * cphi c (n8 (dExp uD)) = c.g * cphi c (n8 (dExp uD)) * c.g⁻¹ * c.g := by group
      _ = cphi c (n8 (dExp uD)) * c.g := by rw [hU]
  have hb' : cphi c (n8 nW) * cphi c (n8 (dExp uD)) * (cphi c (n8 nW))⁻¹ =
      cphi c (n8 (dExp bD)) := by
    rw [eqN hbD, ← eqN hb, n8_append, n8_append, n8_inv10, map_mul, map_mul, map_inv]
  have hd' : c.g * cphi c (n8 (dExp bD)) * c.g⁻¹ = cphi c (n8 dAW) := by
    rw [conj_dExp c bD, eqN hd]
  have hdT : cphi c (n8 dAW) ∈ T := cphi_mem_T c (n8_mem_tSub (by decide))
  have hd1 : cphi c (n8 dAW) ≠ 1 := by
    intro h1
    apply n8_ne_of_tEq hd0
    apply cphi_injective c
    rw [h1, n8_nil, map_one]
  have hdU : cphi c (n8 dAW) = (c.g * cphi c (n8 nW)) * cphi c (n8 (dExp uD)) *
      (c.g * cphi c (n8 nW))⁻¹ := by
    rw [← hd', ← hb']
    group
  have hcomm : (c.g * cphi c (n8 nW) * c.g * (c.g * cphi c (n8 nW))⁻¹) * cphi c (n8 dAW) =
      cphi c (n8 dAW) * (c.g * cphi c (n8 nW) * c.g * (c.g * cphi c (n8 nW))⁻¹) := by
    rw [hdU]
    calc c.g * cphi c (n8 nW) * c.g * (c.g * cphi c (n8 nW))⁻¹ *
          (c.g * cphi c (n8 nW) * cphi c (n8 (dExp uD)) * (c.g * cphi c (n8 nW))⁻¹)
        = c.g * cphi c (n8 nW) * (c.g * cphi c (n8 (dExp uD))) * (c.g * cphi c (n8 nW))⁻¹ := by
          group
      _ = c.g * cphi c (n8 nW) * (cphi c (n8 (dExp uD)) * c.g) * (c.g * cphi c (n8 nW))⁻¹ := by
          rw [hgU]
      _ = c.g * cphi c (n8 nW) * cphi c (n8 (dExp uD)) * (c.g * cphi c (n8 nW))⁻¹ *
          (c.g * cphi c (n8 nW) * c.g * (c.g * cphi c (n8 nW))⁻¹) := by group
  have hw_eq : c.g * cphi c (n8 nW) * c.g * (c.g * cphi c (n8 nW))⁻¹ =
      c.g * cphi c (n8 nW) * c.g * (cphi c (n8 nW))⁻¹ * c.g := by
    rw [mul_inv_rev, hg]
    group
  have hwN : c.g * cphi c (n8 nW) * c.g * (cphi c (n8 nW))⁻¹ * c.g ∈
      Subgroup.normalizer (T : Set G) := by
    rw [← hw_eq]
    exact hyp.cent_le _ hdT hd1 (Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact hcomm.symm)
  set w := c.g * cphi c (n8 nW) * c.g * (cphi c (n8 nW))⁻¹ * c.g with hwdef
  set x : N8 := c.ψ.symm ⟨w, hwN⟩ with hxdef
  have hx : cphi c x = w := by rw [cphi_apply, hxdef, MulEquiv.apply_symm_apply]
  have hconj : ∀ j, x⁻¹ * n8 (yW j) * x = (n8 wW)⁻¹ * n8 (yW j) * n8 wW := by
    intro j
    obtain ⟨hyD, ha1, hb1, hF, hwF⟩ := hy j
    have eF : (n8 wW)⁻¹ * n8 (yW j) * n8 wW = n8 (thExp (b1D j)) := by
      rw [eqN hF, ← eqN hwF, n8_append, n8_append, n8_inv10]
    rw [eF, ← eqN hyD]
    apply cphi_injective c
    rw [map_mul, map_mul, map_inv, hx]
    have e1 : c.g * cphi c (n8 (dExp (yD j))) * c.g⁻¹ = cphi c (n8 (thExp (yD j))) :=
      conj_dExp c (yD j)
    have e2 : (cphi c (n8 nW))⁻¹ * cphi c (n8 (thExp (yD j))) * cphi c (n8 nW) =
        cphi c (n8 (dExp (a1D j))) := by
      rw [← eqN ha1, n8_append, n8_append, n8_inv10, map_mul, map_mul, map_inv]
    have e3 : c.g * cphi c (n8 (dExp (a1D j))) * c.g⁻¹ = cphi c (n8 (thExp (a1D j))) :=
      conj_dExp c (a1D j)
    have e4 : cphi c (n8 nW) * cphi c (n8 (thExp (a1D j))) * (cphi c (n8 nW))⁻¹ =
        cphi c (n8 (dExp (b1D j))) := by
      rw [← eqN hb1, n8_append, n8_append, n8_inv10, map_mul, map_mul, map_inv]
    have e5 : c.g * cphi c (n8 (dExp (b1D j))) * c.g⁻¹ = cphi c (n8 (thExp (b1D j))) :=
      conj_dExp c (b1D j)
    rw [← e5, ← e4, ← e3, ← e2, ← e1, hwdef]
    simp only [mul_inv_rev, inv_inv, hg]
    group
  have hxw : ∀ j, x * (n8 wW)⁻¹ * n8 (yW j) = n8 (yW j) * (x * (n8 wW)⁻¹) := by
    intro j
    calc x * (n8 wW)⁻¹ * n8 (yW j) = x * ((n8 wW)⁻¹ * n8 (yW j) * n8 wW) * (n8 wW)⁻¹ := by
          group
      _ = x * (x⁻¹ * n8 (yW j) * x) * (n8 wW)⁻¹ := by rw [hconj j]
      _ = n8 (yW j) * (x * (n8 wW)⁻¹) := by group
  have h1 := eq_one_of_commute hf.cent hcard (hxw 0) (hxw 1)
  have hxe : x = n8 wW := by
    calc x = x * (n8 wW)⁻¹ * n8 wW := by group
      _ = n8 wW := by rw [h1, one_mul]
  rw [← hx, hxe]

theorem ruRelL_eq : ruRelL =
    [(letG, true) :: nWordL ++ (letG, true) :: invW nWordL ++ (letG, true) :: invW wWordL] := by
  decide

theorem r3StatementL_of_facts (hf : R3FactsL) :
    R3StatementL := by
  intro G _ _ T T₁ hyp c r hr
  rw [ruRelL_eq, List.mem_singleton] at hr
  subst hr
  have key := r3_core hf hyp c
  simp only [List.cons_append, evalW_cons_true, evalW_append, evalW_invW, ← liftW10_nW,
    ← liftW10_wW, evalW_liftW10', gens_letG]
  rw [← key]
  group

end CFSG.CGT.L5R.R3
