module

public import CFSG.CGT.M24R.L2Model8
public import CFSG.CGT.M24R.L2GTheta8

public section

namespace CFSG.CGT.M24R

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75JM CFSG.CosetTable

theorem card_normalizer_of_hyp {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}
    (hyp : M24CtxHyp T T₁) : Nat.card (Subgroup.normalizer (T : Set G)) = 322560 := by
  obtain ⟨φ⟩ := hyp.quot
  have h1 : Nat.card (NQuot T) = 20160 := by
    rw [Nat.card_congr φ.toEquiv]
    have h := two_mul_nat_card_alternatingGroup (α := Fin 8)
    rw [Nat.card_perm, Nat.card_fin] at h
    have : Nat.factorial 8 = 40320 := by decide
    omega
  have h2 : Nat.card (T.subgroupOf (Subgroup.normalizer (T : Set G))) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv,
      hyp.card16]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (T.subgroupOf (Subgroup.normalizer (T : Set G)))]
  change Nat.card (NQuot T) * _ = _
  rw [h1, h2]

theorem evalW_genTuple8_liftW10 {G : Type} [Group G] {T : Subgroup G}
    (ψ : PG 10 relsN8Ten ≃* ↥(Subgroup.normalizer (T : Set G))) (g : G)
    (w : List (Fin 10 × Bool)) :
    evalW (genTuple8 ψ g) (liftW10 w) = ((ψ (n8 w) : ↥(Subgroup.normalizer (T : Set G))) : G) := by
  have hhom : (FreeGroup.lift fun j : Fin 10 => genTuple8 ψ g (Fin.castSucc j)) =
      (Subgroup.normalizer (T : Set G)).subtype.comp
        (ψ.toMonoidHom.comp (PresentedGroup.mk {r : FreeGroup (Fin 10) |
          r ∈ relsN8Ten.map FreeGroup.mk})) := by
    apply FreeGroup.ext_hom
    intro j
    simp [genTuple8]
    rfl
  have key : ∀ w : List (Fin 10 × Bool), evalW (genTuple8 ψ g) (liftW10 w) =
      FreeGroup.lift (fun j : Fin 10 => genTuple8 ψ g (Fin.castSucc j)) (FreeGroup.mk w) := by
    intro w
    induction w with
    | nil => simp [liftW10, evalW_nil]
    | cons l w ih =>
      have e1 : liftW10 (l :: w) = (Fin.castSucc l.1, l.2) :: liftW10 w := rfl
      rw [e1, evalW_cons, ih,
        show FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w from rfl, map_mul]
      obtain ⟨i, b⟩ := l
      cases b
      · rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
          FreeGroup.lift_apply_of]
        rfl
      · rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
        rfl
  rw [key, hhom]
  rfl

theorem genTuple8_g {G : Type} [Group G] {T : Subgroup G}
    (ψ : PG 10 relsN8Ten ≃* ↥(Subgroup.normalizer (T : Set G))) (g : G) :
    genTuple8 ψ g letG = g := by
  simp [genTuple8, letG]

theorem l2Statement8_of_n8 (hN8 : N8Statement) :
    L2Statement8 := by
  intro G _ _ T T₁ hyp
  obtain ⟨ψ, hψ⟩ := hN8 G T T₁ hyp
  have hctx : TCtx T T₁ := ⟨hyp.wc, hyp.inf_bot, hyp.conj, hyp.norm1, hyp.norm2⟩
  have hcard : Nat.card N8 = 322560 := by
    rw [Nat.card_congr ψ.toEquiv, card_normalizer_of_hyp hyp]
  have hfin : Finite N8 := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  let M := l2Model8 hcard
  let E : OntoEmb N8 (Subgroup.normalizer (T : Set G)) := OntoEmb.ofEquiv ψ
  have hE : ∀ x, x ∈ M.T0 ↔ E.Φ x ∈ T := by
    intro x
    have h1 : x ∈ Subgroup.closure (Set.range tGen8) ↔
        ψ x ∈ Subgroup.map ψ.toMonoidHom (Subgroup.closure (Set.range tGen8)) := by
      rw [Subgroup.mem_map_equiv]
      simp
    rw [hψ, Subgroup.mem_subgroupOf] at h1
    exact h1
  obtain ⟨E', g, hT', hgT, hgg, hrel⟩ := exists_config8 hctx M E hE
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
    rw [thetaRels8_eq] at hr
    simp only [List.mem_cons, List.mem_ofFn] at hr
    rcases hr with rfl | ⟨i, rfl⟩
    · rw [evalW_cons_true, evalW_cons_true, evalW_nil, genTuple8_g, mul_one, hgg]
    · rw [evalW_append, evalW_cons_true, evalW_cons_true, evalW_invW, genTuple8_g,
        ← liftW10_dWord10, ← liftW10_thetaWord10, evalW_genTuple8_liftW10,
        evalW_genTuple8_liftW10, OntoEmb.toEquiv_apply_coe, OntoEmb.toEquiv_apply_coe]
      have h1 : g * E'.Φ (d8 i) * g = E'.Φ (th8 i) := by
        have := hrel i
        rw [hginv] at this
        exact this
      rw [show n8 (dWord10 i) = d8 i from rfl, show n8 (thetaWord10 i) = th8 i from rfl,
        ← mul_assoc, h1, mul_inv_cancel]

end CFSG.CGT.M24R
