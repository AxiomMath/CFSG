module

public import CFSG.CGT.L5R.L2ModelL
public import CFSG.CGT.L5R.N8
public import CFSG.CGT.M24R.L2Cert
public import CFSG.CGT.L5R.L2GThetaL

public section

namespace CFSG.CGT.L5R

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75JM CFSG.CosetTable CFSG.CGT.M24R

theorem liftW10_dW10 (i : Fin 2) : liftW10 (dW10 i) = dWordL i := by
  fin_cases i <;> decide

theorem liftW10_thW10 (i : Fin 2) : liftW10 (thW10 i) = thetaWordL i := by
  fin_cases i <;> decide

theorem thetaRelsL_eq : thetaRelsL = [(letG, true), (letG, true)] ::
    List.ofFn fun i : Fin 2 => (letG, true) :: dWordL i ++ (letG, true) :: invW (thetaWordL i) := by
  decide

theorem l2StatementL_of_n8
    (hN8 : N8StatementL) : L2StatementL := by
  intro G _ _ T T₁ hyp
  obtain ⟨ψ, hψ⟩ := hN8 G T T₁ hyp
  have hctx : TCtxL T T₁ := ⟨hyp.wc, hyp.inf_bot, hyp.conj, hyp.norm1, hyp.norm2⟩
  have hcard : Nat.card N8 = 322560 := by
    rw [Nat.card_congr ψ.toEquiv, card_normalizer_of_hypL hyp]
  have hfin : Finite N8 := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  let M := l2ModelL hcard
  let E : OntoEmb N8 (Subgroup.normalizer (T : Set G)) := OntoEmb.ofEquiv ψ
  have hE : ∀ x, x ∈ M.T0 ↔ E.Φ x ∈ T := by
    intro x
    have h1 : x ∈ Subgroup.closure (Set.range tGen8) ↔
        ψ x ∈ Subgroup.map ψ.toMonoidHom (Subgroup.closure (Set.range tGen8)) := by
      rw [Subgroup.mem_map_equiv]
      simp
    rw [hψ, Subgroup.mem_subgroupOf] at h1
    exact h1
  obtain ⟨E', g, hT', hgT, hgg, hrel⟩ := exists_configL hctx hyp.noType4 M E hE
  refine ⟨⟨E'.toEquiv, ?_, g, hgT, ?_⟩⟩
  · ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]
    have h3 : E'.Φ (E'.toEquiv.symm y) = (y : G) := by
      rw [← OntoEmb.toEquiv_apply_coe, MulEquiv.apply_symm_apply]
    have := hT' (E'.toEquiv.symm y)
    rw [h3] at this
    exact this
  · intro r hr
    have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
    rw [thetaRelsL_eq] at hr
    simp only [List.mem_cons, List.mem_ofFn] at hr
    rcases hr with rfl | ⟨i, rfl⟩
    · rw [evalW_cons_true, evalW_cons_true, evalW_nil, genTuple8_g, mul_one, hgg]
    · rw [evalW_append, evalW_cons_true, evalW_cons_true, evalW_invW, genTuple8_g,
        ← liftW10_dW10, ← liftW10_thW10, evalW_genTuple8_liftW10,
        evalW_genTuple8_liftW10, OntoEmb.toEquiv_apply_coe, OntoEmb.toEquiv_apply_coe]
      have h1 : g * E'.Φ (dL i) * g = E'.Φ (thL i) := by
        have := hrel i
        rw [hginv] at this
        exact this
      rw [show n8 (dW10 i) = dL i from rfl, show n8 (thW10 i) = thL i from rfl,
        ← mul_assoc, h1, mul_inv_cancel]

end CFSG.CGT.L5R
