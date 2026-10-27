module

public import CFSG.CGT.M24R.R3Collapse

public section

namespace CFSG.CGT.M24R.R3

open CFSG.CGT.Timmesfeld75

structure R3Facts : Prop where
  rel : relCheck = true
  ident : identCheck = true
  distinct : distinctCheck = true
  orbit : ∃ Z : List N0Word, Z.length = 20160 ∧ (Z.map conjKey).Nodup
  collapse : ∀ i : Fin 16, i ≠ 0 → Collapse8 i

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}

theorem r3_core (hf : R3Facts) (hyp : M24CtxHyp T T₁) (c : T1Config8 T T₁) :
    c.g * cphi c (n0 nW) * c.g * (cphi c (n0 nW))⁻¹ * c.g = cphi c (n0 wW) := by
  have hinj := rho_injective hyp c hf.rel hf.distinct
  have hid := identCheck_spec hf.ident
  have eqN : ∀ {w w' : N0Word}, nEq w w' = true → n0 w = n0 w' := fun hw =>
    n0_eq_of_nEq hf.rel hinj hw
  have hg : c.g⁻¹ = c.g := g_inv c
  have hU : c.g * cphi c (n0 (dExp uD)) * c.g⁻¹ = cphi c (n0 (dExp uD)) := by
    rw [conj_dExp c uD, eqN hid.1]
  have hgU : c.g * cphi c (n0 (dExp uD)) = cphi c (n0 (dExp uD)) * c.g := by
    calc c.g * cphi c (n0 (dExp uD)) = c.g * cphi c (n0 (dExp uD)) * c.g⁻¹ * c.g := by group
      _ = cphi c (n0 (dExp uD)) * c.g := by rw [hU]
  have hb : cphi c (n0 nW) * cphi c (n0 (dExp uD)) * (cphi c (n0 nW))⁻¹ =
      cphi c (n0 (dExp bD)) := by
    rw [← eqN hid.2.1, n0_append, n0_append, n0_inv10, map_mul, map_mul, map_inv]
  have hd : c.g * cphi c (n0 (dExp bD)) * c.g⁻¹ = cphi c (n0 aW) := by
    rw [conj_dExp c bD, eqN hid.2.2.1]
  have hdT : cphi c (n0 aW) ∈ T :=
    (mem_tSub_iff c.ψ c.map_t _).1 (n0_mem_tSub fun l hl => by simp [aW] at hl; subst hl; simp)
  have hd1 : cphi c (n0 aW) ≠ 1 := by
    intro h1
    have : n0 aW = n0 [] := cphi_injective c (by rw [h1, n0_nil, map_one])
    exact n0_ne_of_nEq hf.rel hid.2.2.2.1 this
  have hdU : cphi c (n0 aW) = (c.g * cphi c (n0 nW)) * cphi c (n0 (dExp uD)) *
      (c.g * cphi c (n0 nW))⁻¹ := by
    rw [← hd, ← hb]
    group
  have hcomm : (c.g * cphi c (n0 nW) * c.g * (c.g * cphi c (n0 nW))⁻¹) * cphi c (n0 aW) =
      cphi c (n0 aW) * (c.g * cphi c (n0 nW) * c.g * (c.g * cphi c (n0 nW))⁻¹) := by
    rw [hdU]
    calc c.g * cphi c (n0 nW) * c.g * (c.g * cphi c (n0 nW))⁻¹ *
          (c.g * cphi c (n0 nW) * cphi c (n0 (dExp uD)) * (c.g * cphi c (n0 nW))⁻¹)
        = c.g * cphi c (n0 nW) * (c.g * cphi c (n0 (dExp uD))) * (c.g * cphi c (n0 nW))⁻¹ := by
          group
      _ = c.g * cphi c (n0 nW) * (cphi c (n0 (dExp uD)) * c.g) * (c.g * cphi c (n0 nW))⁻¹ := by
          rw [hgU]
      _ = c.g * cphi c (n0 nW) * cphi c (n0 (dExp uD)) * (c.g * cphi c (n0 nW))⁻¹ *
          (c.g * cphi c (n0 nW) * c.g * (c.g * cphi c (n0 nW))⁻¹) := by group
  have hw_eq : c.g * cphi c (n0 nW) * c.g * (c.g * cphi c (n0 nW))⁻¹ =
      c.g * cphi c (n0 nW) * c.g * (cphi c (n0 nW))⁻¹ * c.g := by
    rw [mul_inv_rev, hg]
    group
  have hwN : c.g * cphi c (n0 nW) * c.g * (cphi c (n0 nW))⁻¹ * c.g ∈
      Subgroup.normalizer (T : Set G) := by
    rw [← hw_eq]
    exact hyp.cent_le _ hdT hd1 (Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact hcomm.symm)
  set w := c.g * cphi c (n0 nW) * c.g * (cphi c (n0 nW))⁻¹ * c.g with hwdef
  set x : N0 := c.ψ.symm ⟨w, hwN⟩ with hxdef
  have hx : cphi c x = w := by rw [cphi_apply, hxdef, MulEquiv.apply_symm_apply]
  have hconj : ∀ j, x⁻¹ * yN j * x = (n0 wW)⁻¹ * yN j * n0 wW := by
    intro j
    obtain ⟨ha1, hb1, hF⟩ := hid.2.2.2.2.1 j
    have eF : (n0 wW)⁻¹ * yN j * n0 wW = n0 (thExp (b1D j)) := by
      rw [← eqN hF, n0_append, n0_append, n0_inv10]
      rfl
    rw [eF]
    apply cphi_injective c
    rw [map_mul, map_mul, map_inv, hx]
    have e1 : c.g * cphi c (yN j) * c.g⁻¹ = cphi c (n0 (thExp (yD j))) := conj_dExp c (yD j)
    have e2 : (cphi c (n0 nW))⁻¹ * cphi c (n0 (thExp (yD j))) * cphi c (n0 nW) =
        cphi c (n0 (dExp (a1D j))) := by
      rw [← eqN ha1, n0_append, n0_append, n0_inv10, map_mul, map_mul, map_inv]
    have e3 : c.g * cphi c (n0 (dExp (a1D j))) * c.g⁻¹ = cphi c (n0 (thExp (a1D j))) :=
      conj_dExp c (a1D j)
    have e4 : cphi c (n0 nW) * cphi c (n0 (thExp (a1D j))) * (cphi c (n0 nW))⁻¹ =
        cphi c (n0 (dExp (b1D j))) := by
      rw [← eqN hb1, n0_append, n0_append, n0_inv10, map_mul, map_mul, map_inv]
    have e5 : c.g * cphi c (n0 (dExp (b1D j))) * c.g⁻¹ = cphi c (n0 (thExp (b1D j))) :=
      conj_dExp c (b1D j)
    rw [← e5, ← e4, ← e3, ← e2, ← e1, hwdef]
    simp only [mul_inv_rev, inv_inv, hg]
    group
  have hxw : ∀ j, x * (n0 wW)⁻¹ * yN j = yN j * (x * (n0 wW)⁻¹) := by
    intro j
    calc x * (n0 wW)⁻¹ * yN j = x * ((n0 wW)⁻¹ * yN j * n0 wW) * (n0 wW)⁻¹ := by group
      _ = x * (x⁻¹ * yN j * x) * (n0 wW)⁻¹ := by rw [hconj j]
      _ = yN j * (x * (n0 wW)⁻¹) := by group
  have := finite_N0 c
  obtain ⟨i, hi⟩ := mem_eW_of_commute hf.rel hinj hf.ident hf.distinct hf.orbit
    (card_N0 hyp c).le hxw
  have hxi : x = n0 (eW i ++ wW) := by
    rw [n0_append, ← hi]
    group
  by_cases h0 : i = 0
  · rw [← hx, hxi, h0]
    rfl
  · exfalso
    apply not_collapse hyp c (hf.collapse i h0)
    simp only [collRel, List.cons_append, evalW_cons_true, evalW_append, evalW_invW,
      ← liftW10_nW, evalW_liftW10', gens_letG]
    rw [← hxi, hx, hwdef]
    group

theorem r3Statement_of_facts (hf : R3Facts) : R3Statement := by
  intro G _ _ T T₁ hyp c r hr
  rw [ruRel_eq, List.mem_singleton] at hr
  subst hr
  have key := r3_core hf hyp c
  simp only [List.cons_append, evalW_cons_true, evalW_append, evalW_invW, ← liftW10_nW,
    ← liftW10_wW, evalW_liftW10', gens_letG]
  rw [← key]
  group

end CFSG.CGT.M24R.R3
