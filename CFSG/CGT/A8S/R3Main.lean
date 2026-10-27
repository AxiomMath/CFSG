module

public import CFSG.CGT.A8S.R3Config
public import CFSG.CGT.A8S.CollapseCert

public section

namespace CFSG.CGT.A8S

open CFSG.CosetTable CFSG.CGT.Timmesfeld75

namespace R3

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem gens_one (c : T1ConfigA8 T T₁) : c.gens 1 = cphi c (n0v nW) := by
  rw [← evalA8_liftW5', liftW5_nW]
  simp [nWordA8]

theorem evalA8_wWordA8 (c : T1ConfigA8 T T₁) : evalA8 c.gens wWordA8 = cphi c (n0v wW) := by
  rw [← liftW5_wW, evalA8_liftW5']

theorem evalA8_wrongWordA8 (c : T1ConfigA8 T T₁) (k : Fin 7) :
    evalA8 c.gens (wrongWordA8 k) = cphi c (n0v (wrongW k)) := by
  rw [← liftW5_wrongW, evalA8_liftW5']

theorem w_mem_normalizer (hyp : A8CtxHyp T T₁)
    (c : T1ConfigA8 T T₁) :
    c.g * c.gens 1 * c.g * (c.gens 1)⁻¹ * c.g ∈ Subgroup.normalizer (T : Set G) := by
  have hg : c.g⁻¹ = c.g := g_inv c
  have hU : c.g * cphi c (n0v (dExp uD)) * c.g⁻¹ = cphi c (n0v (dExp uD)) := by
    rw [conj_dExp c uD, n0v_eq_of_affBEq affEval_thExp_uD]
  have hgU : c.g * cphi c (n0v (dExp uD)) = cphi c (n0v (dExp uD)) * c.g := by
    calc c.g * cphi c (n0v (dExp uD)) = c.g * cphi c (n0v (dExp uD)) * c.g⁻¹ * c.g := by group
      _ = cphi c (n0v (dExp uD)) * c.g := by rw [hU]
  have hb : cphi c (n0v nW) * cphi c (n0v (dExp uD)) * (cphi c (n0v nW))⁻¹ =
      cphi c (n0v (dExp bD)) := by
    rw [← n0v_eq_of_affBEq affEval_conj_uD, n0v_append, n0v_append, n0v_invRev, map_mul,
      map_mul, map_inv]
  have hd : c.g * cphi c (n0v (dExp bD)) * c.g⁻¹ = cphi c (n0v [(2, true)]) := by
    rw [conj_dExp c bD, n0v_eq_of_affBEq affEval_thExp_bD]
  have hdT : cphi c (n0v [(2, true)]) ∈ T := cphi_mem_T c (Subgroup.subset_closure ⟨0, rfl⟩)
  have hd1 : cphi c (n0v [(2, true)]) ≠ 1 := by
    intro h1
    apply n0v_ne_of_affBEq affEval_t0_ne
    apply cphi_injective c
    rw [h1, n0v_nil, map_one]
  have hdU : cphi c (n0v [(2, true)]) = (c.g * cphi c (n0v nW)) * cphi c (n0v (dExp uD)) *
      (c.g * cphi c (n0v nW))⁻¹ := by
    rw [← hd, ← hb]
    group
  have hcomm : (c.g * cphi c (n0v nW) * c.g * (c.g * cphi c (n0v nW))⁻¹) *
      cphi c (n0v [(2, true)]) = cphi c (n0v [(2, true)]) *
        (c.g * cphi c (n0v nW) * c.g * (c.g * cphi c (n0v nW))⁻¹) := by
    rw [hdU]
    calc c.g * cphi c (n0v nW) * c.g * (c.g * cphi c (n0v nW))⁻¹ *
          (c.g * cphi c (n0v nW) * cphi c (n0v (dExp uD)) * (c.g * cphi c (n0v nW))⁻¹)
        = c.g * cphi c (n0v nW) * (c.g * cphi c (n0v (dExp uD))) *
            (c.g * cphi c (n0v nW))⁻¹ := by group
      _ = c.g * cphi c (n0v nW) * (cphi c (n0v (dExp uD)) * c.g) *
            (c.g * cphi c (n0v nW))⁻¹ := by rw [hgU]
      _ = c.g * cphi c (n0v nW) * cphi c (n0v (dExp uD)) * (c.g * cphi c (n0v nW))⁻¹ *
          (c.g * cphi c (n0v nW) * c.g * (c.g * cphi c (n0v nW))⁻¹) := by group
  have hw_eq : c.g * cphi c (n0v nW) * c.g * (c.g * cphi c (n0v nW))⁻¹ =
      c.g * c.gens 1 * c.g * (c.gens 1)⁻¹ * c.g := by
    rw [mul_inv_rev, hg, gens_one]
    group
  rw [← hw_eq]
  exact hyp.cent_le _ hdT hd1 (Subgroup.mem_centralizer_iff.2 fun h hh => by
    rw [Set.mem_singleton_iff.1 hh]
    exact hcomm.symm)

theorem conj_yW (c : T1ConfigA8 T T₁) {x : PG 5 relsN0A8}
    (hx : cphi c x = c.g * c.gens 1 * c.g * (c.gens 1)⁻¹ * c.g) (j : Fin 3) :
    x⁻¹ * n0v (yW j) * x = n0v (fW j) := by
  have hg : c.g⁻¹ = c.g := g_inv c
  rw [← n0v_eq_of_affBEq (affEval_fW j), n0v_eq_of_affBEq (affEval_yD j)]
  apply cphi_injective c
  rw [map_mul, map_mul, map_inv, hx]
  have e1 : c.g * cphi c (n0v (dExp (yD j))) * c.g⁻¹ = cphi c (n0v (thExp (yD j))) :=
    conj_dExp c (yD j)
  have e2 : (cphi c (n0v nW))⁻¹ * cphi c (n0v (thExp (yD j))) * cphi c (n0v nW) =
      cphi c (n0v (dExp (aD j))) := by
    rw [← n0v_eq_of_affBEq (affEval_aD j), n0v_append, n0v_append, n0v_invRev, map_mul,
      map_mul, map_inv]
  have e3 : c.g * cphi c (n0v (dExp (aD j))) * c.g⁻¹ = cphi c (n0v (thExp (aD j))) :=
    conj_dExp c (aD j)
  have e4 : cphi c (n0v nW) * cphi c (n0v (thExp (aD j))) * (cphi c (n0v nW))⁻¹ =
      cphi c (n0v (dExp (bbD j))) := by
    rw [← n0v_eq_of_affBEq (affEval_bbD j), n0v_append, n0v_append, n0v_invRev, map_mul,
      map_mul, map_inv]
  have e5 : c.g * cphi c (n0v (dExp (bbD j))) * c.g⁻¹ = cphi c (n0v (thExp (bbD j))) :=
    conj_dExp c (bbD j)
  rw [← e5, ← e4, ← e3, ← e2, ← e1, gens_one]
  simp only [mul_inv_rev, inv_inv, hg]
  group

theorem r3_core
    (hyp : A8CtxHyp T T₁) (c : T1ConfigA8 T T₁) :
    c.g * c.gens 1 * c.g * (c.gens 1)⁻¹ * c.g = evalA8 c.gens wWordA8 := by
  set x : PG 5 relsN0A8 := c.ψ.symm ⟨_, w_mem_normalizer hyp c⟩ with hxdef
  have hx : cphi c x = c.g * c.gens 1 * c.g * (c.gens 1)⁻¹ * c.g := by
    rw [cphi_apply, hxdef, MulEquiv.apply_symm_apply]
  rcases eq_of_conj_eq x (conj_yW c hx) with h | ⟨k, hk⟩
  · rw [← hx, h, evalA8_wWordA8]
  · exfalso
    apply c.collapse_ne_wrong hyp k
    rw [← hx, hk, evalA8_wrongWordA8]

theorem ruRelA8_eq : ruRelA8 =
    [(5, true) :: nWordA8 ++ (5, true) :: invA8 nWordA8 ++ (5, true) :: invA8 wWordA8] := by
  decide

end R3

open R3 in
theorem r3StatementA8 :
    R3StatementA8 := by
  intro G _ _ T T₁ hyp c r hr
  rw [ruRelA8_eq, List.mem_singleton] at hr
  subst hr
  have hn : evalA8 c.gens nWordA8 = c.gens 1 := by simp [nWordA8]
  have key := r3_core hyp c
  simp only [List.cons_append, evalA8_cons_true, evalA8_append, evalA8_invA8, gens_five, hn]
  rw [← key]
  group

end CFSG.CGT.A8S
