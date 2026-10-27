module

public import CFSG.CGT.T75JM.PData

public section

namespace CFSG.CGT.T75JM

open CFSG.CosetTable CFSG.CGT.Timmesfeld75 CFSG.CGT.T75I

theorem subst_append {α β : Type} (f : α → List β) (u u' : List α) :
    subst f (u ++ u') = subst f u ++ subst f u' := by
  induction u with
  | nil => rfl
  | cons a u ih => simp [subst, ih]

theorem vExp_append (u u' : List (Fin 2 × Bool)) : vExp (u ++ u') = vExp u ++ vExp u' :=
  subst_append _ u u'

theorem val6_nil : val6 [] = 1 := by
  rw [val6]
  exact map_one _

theorem val6_append (w w' : List (Fin 6 × Bool)) : val6 (w ++ w') = val6 w * val6 w' := by
  rw [val6, val6, val6, ← map_mul, FreeGroup.mul_mk]

theorem val6_invWord (w : List (Fin 6 × Bool)) : val6 (invWord w) = (val6 w)⁻¹ := by
  rw [val6, val6, ← map_inv, FreeGroup.inv_mk, FreeGroup.invRev, invWord, List.map_reverse]

theorem evalWord7_nil {H : Type*} [Group H] (e : Fin 7 → H) : evalWord7 e [] = 1 := by
  rw [evalWord7]
  exact map_one _

theorem evalWord7_append {H : Type*} [Group H] (e : Fin 7 → H) (w w' : M22Word) :
    evalWord7 e (w ++ w') = evalWord7 e w * evalWord7 e w' := by
  rw [evalWord7, evalWord7, evalWord7, ← map_mul, FreeGroup.mul_mk]

theorem evalWord7_invWord {H : Type*} [Group H] (e : Fin 7 → H) (w : M22Word) :
    evalWord7 e (invWord w) = (evalWord7 e w)⁻¹ := by
  rw [evalWord7, evalWord7, ← map_inv, FreeGroup.inv_mk, FreeGroup.invRev, invWord,
    List.map_reverse]

theorem evalWord7_single_true {H : Type*} [Group H] (e : Fin 7 → H) (i : Fin 7) :
    evalWord7 e [(i, true)] = e i := by
  show FreeGroup.lift e (FreeGroup.of i) = e i
  exact FreeGroup.lift_apply_of

theorem evalWord3_nil {H : Type*} [Group H] (x : Fin 3 → H) : evalWord3 x [] = 1 := rfl

theorem evalWord3_cons {H : Type*} [Group H] (x : Fin 3 → H) (p : Fin 3 × Bool)
    (w : List (Fin 3 × Bool)) :
    evalWord3 x (p :: w) = (if p.2 then x p.1 else (x p.1)⁻¹) * evalWord3 x w := by
  simp [evalWord3]

section Config

variable {G : Type} [Group G] {T T₁ : Subgroup G} (c : T1Config T T₁)

@[expose] def T1Config.phi : PG 6 rels6 →* G :=
  (Subgroup.normalizer (T : Set G)).subtype.comp c.ψ.toMonoidHom

theorem T1Config.phi_injective : Function.Injective c.phi :=
  Subtype.val_injective.comp c.ψ.injective

theorem T1Config.phi_mk :
    c.phi.comp (PresentedGroup.mk _) =
      FreeGroup.lift (fun i : Fin 6 => c.gens (Fin.castSucc i)) := by
  apply FreeGroup.ext_hom
  intro i
  simp [T1Config.phi, T1Config.gens, genTuple, PresentedGroup.mk]
  rfl

theorem T1Config.phi_val6 (w : List (Fin 6 × Bool)) :
    c.phi (val6 w) = evalWord7 c.gens (liftWord w) := by
  rw [evalWord7_liftWord]
  have := congrArg (fun f : FreeGroup (Fin 6) →* G => f (FreeGroup.mk w)) c.phi_mk
  simpa [val6] using this

theorem T1Config.gens_six : c.gens 6 = c.g := by
  simp [T1Config.gens, genTuple]

@[expose] def T1Config.aG : Fin 3 → G := ![c.phi (val6 (vGen 0)), c.phi (val6 (vGen 1)), c.g]

theorem T1Config.aG_castSucc (i : Fin 2) : c.aG (Fin.castSucc i) = c.phi (val6 (vGen i)) := by
  fin_cases i <;> rfl

theorem T1Config.aG_two : c.aG 2 = c.g := rfl

theorem T1Config.eval_castV (u : List (Fin 2 × Bool)) :
    evalWord3 c.aG (castV u) = c.phi (val6 (vExp u)) := by
  induction u with
  | nil =>
    show evalWord3 c.aG [] = c.phi (val6 [])
    rw [val6_nil, map_one]
    rfl
  | cons p u ih =>
    have h1 : castV (p :: u) = (Fin.castSucc p.1, p.2) :: castV u := rfl
    have h2 : vExp (p :: u) = (if p.2 then vGen p.1 else invWord (vGen p.1)) ++ vExp u := rfl
    rw [h1, evalWord3_cons, h2, val6_append, map_mul, ih]
    congr 1
    rcases p with ⟨i, b⟩
    cases b
    · simp [val6_invWord, c.aG_castSucc]
    · simp [c.aG_castSucc]

theorem T1Config.gg : c.g * c.g = 1 := by
  have h := c.rel [(6, true), (6, true)] (by simp [thetaRels])
  have e : ([(6, true), (6, true)] : M22Word) = [(6, true)] ++ [(6, true)] := rfl
  change evalWord7 c.gens _ = 1 at h
  rw [e, evalWord7_append, evalWord7_single_true, c.gens_six] at h
  exact h

theorem T1Config.conj_dGen (i : Fin 2) :
    c.g * c.phi (val6 (dGen i)) * c.g⁻¹ = c.phi (val6 (dTheta i)) := by
  have hmem : ([(6, true)] ++ liftWord (dGen i) ++ [(6, true)] ++
      liftWord (invWord (dTheta i)) : M22Word) ∈ thetaRels := by
    unfold thetaRels
    refine List.mem_cons_of_mem _ ?_
    rw [List.mem_ofFn]
    exact ⟨i, rfl⟩
  have h := c.rel _ hmem
  change evalWord7 c.gens _ = 1 at h
  rw [evalWord7_append, evalWord7_append, evalWord7_append, evalWord7_single_true, c.gens_six,
    ← c.phi_val6, ← c.phi_val6, val6_invWord, map_inv] at h
  have hg' : c.g⁻¹ = c.g := inv_eq_of_mul_eq_one_right c.gg
  rw [hg']
  exact mul_inv_eq_one.1 h

theorem T1Config.conj_dExp (u : List (Fin 2 × Bool)) :
    c.g * c.phi (val6 (dExp u)) * c.g⁻¹ = c.phi (val6 (thExp u)) := by
  induction u with
  | nil =>
    show c.g * c.phi (val6 []) * c.g⁻¹ = c.phi (val6 [])
    rw [val6_nil, map_one]
    group
  | cons p u ih =>
    have h1 : dExp (p :: u) = (if p.2 then dGen p.1 else invWord (dGen p.1)) ++ dExp u := rfl
    have h2 : thExp (p :: u) =
        (if p.2 then dTheta p.1 else invWord (dTheta p.1)) ++ thExp u := rfl
    rw [h1, h2, val6_append, val6_append, map_mul, map_mul]
    have hl : c.g * c.phi (val6 (if p.2 then dGen p.1 else invWord (dGen p.1))) * c.g⁻¹ =
        c.phi (val6 (if p.2 then dTheta p.1 else invWord (dTheta p.1))) := by
      rcases p with ⟨i, b⟩
      cases b
      · simp only [Bool.false_eq_true, ite_false, val6_invWord, map_inv]
        have := c.conj_dGen i
        calc c.g * (c.phi (val6 (dGen i)))⁻¹ * c.g⁻¹
            = (c.g * c.phi (val6 (dGen i)) * c.g⁻¹)⁻¹ := by group
          _ = (c.phi (val6 (dTheta i)))⁻¹ := by rw [this]
      · simpa using c.conj_dGen i
    have key : ∀ A B : G, c.g * (A * B) * c.g⁻¹ = (c.g * A * c.g⁻¹) * (c.g * B * c.g⁻¹) :=
      fun A B => by group
    rw [key, hl, ih]

theorem T1Config.eval_base3 (i : Fin 3) : evalWord7 c.gens (base3 i) = c.aG i := by
  fin_cases i
  · show evalWord7 c.gens (liftWord (vGen 0)) = c.phi (val6 (vGen 0))
    rw [← c.phi_val6]
  · show evalWord7 c.gens (liftWord (vGen 1)) = c.phi (val6 (vGen 1))
    rw [← c.phi_val6]
  · show evalWord7 c.gens [(6, true)] = c.g
    rw [evalWord7_single_true, c.gens_six]

theorem T1Config.eval_expand3 (w : List (Fin 3 × Bool)) :
    evalWord7 c.gens (expand3 w) = evalWord3 c.aG w := by
  induction w with
  | nil =>
    show evalWord7 c.gens [] = evalWord3 c.aG []
    rw [evalWord7_nil]
    rfl
  | cons p w ih =>
    have h1 : expand3 (p :: w) = (if p.2 then base3 p.1 else invWord (base3 p.1)) ++ expand3 w :=
      rfl
    rw [h1, evalWord7_append, ih, evalWord3_cons]
    congr 1
    rcases p with ⟨i, b⟩
    cases b
    · simp [evalWord7_invWord, c.eval_base3]
    · simp [c.eval_base3]

@[expose] def T1Config.K : Subgroup G := Subgroup.closure (Set.range c.aG)

@[expose] def T1Config.aK : Fin 3 → c.K := fun k => ⟨c.aG k, Subgroup.subset_closure ⟨k, rfl⟩⟩

theorem T1Config.val_evalWord3 (w : List (Fin 3 × Bool)) :
    ((evalWord3 c.aK w : c.K) : G) = evalWord3 c.aG w := by
  have := evalWord3_map c.K.subtype c.aK w
  exact this

theorem T1Config.val_V (u : List (Fin 2 × Bool)) :
    ((evalWord3 c.aK (castV u) : c.K) : G) = c.phi (val6 (vExp u)) := by
  rw [c.val_evalWord3, c.eval_castV]

@[expose] def epsN (hf : PFacts) : Multiplicative V3 →* PG 6 rels6 where
  toFun x := val6 (vExp (eW x.toAdd))
  map_one' := by
    have h := hf.e_mul 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.trans (mul_one _).symm)
  map_mul' x y := (hf.e_mul x.toAdd y.toAdd).symm

theorem epsN_injective (hf : PFacts) : Function.Injective (epsN hf) := fun _ _ h =>
  Multiplicative.toAdd.injective (hf.e_inj _ _ h)

@[expose] noncomputable def T1Config.epsK (hf : PFacts) : Multiplicative V3 →* c.K :=
  (c.phi.comp (epsN hf)).codRestrict c.K fun x => by
    show c.phi (val6 (vExp (eW x.toAdd))) ∈ c.K
    rw [← c.eval_castV, ← c.val_evalWord3]
    exact (evalWord3 c.aK _).2

theorem T1Config.epsK_val (hf : PFacts) (x : V3) :
    ((c.epsK hf (Multiplicative.ofAdd x) : c.K) : G) = c.phi (val6 (vExp (eW x))) := rfl

theorem T1Config.affHyp (hf : PFacts) (hyp : M22CtxHyp T T₁) :
    AffHyp (c.epsK hf) c.aK mv := by
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    have h : Subgroup.closure (((↑) : c.K → G) ⁻¹' Set.range c.aG) = ⊤ :=
      Subgroup.closure_closure_coe_preimage
    have hs : (((↑) : c.K → G) ⁻¹' Set.range c.aG : Set c.K) = Set.range c.aK := by
      ext x
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k, Subtype.ext hk⟩
      · rintro ⟨k, rfl⟩
        exact ⟨k, rfl⟩
    rw [hs] at h
    exact h
  ·
    intro x y h
    apply epsN_injective hf
    apply c.phi_injective
    exact congrArg (fun z : c.K => (z : G)) h
  ·
    intro k x
    apply Subtype.ext
    have hmul : ((c.aK k * c.epsK hf (Multiplicative.ofAdd x) * (c.aK k)⁻¹ : c.K) : G) =
        c.aG k * c.phi (val6 (vExp (eW x))) * (c.aG k)⁻¹ := rfl
    rw [hmul]
    show _ = c.phi (val6 (vExp (eW (glAct (mv k) x))))
    fin_cases k
    · show c.phi (val6 (vGen 0)) * c.phi (val6 (vExp (eW x))) * (c.phi (val6 (vGen 0)))⁻¹ = _
      rw [← map_inv, ← map_mul, ← map_mul, hf.act_v1]
      rfl
    · show c.phi (val6 (vGen 1)) * c.phi (val6 (vExp (eW x))) * (c.phi (val6 (vGen 1)))⁻¹ = _
      rw [← map_inv, ← map_mul, ← map_mul, hf.act_v2]
      rfl
    · show c.g * c.phi (val6 (vExp (eW x))) * c.g⁻¹ = c.phi (val6 (vExp (eW (glAct mG x))))
      rw [← (hf.act_g x).1, c.conj_dExp, (hf.act_g x).2]
  ·
    intro x hx
    obtain ⟨c0, hc0, hc0T⟩ := hf.e_tors
    have hE0mem : val6 (vExp (eW c0)) ∈ Subgroup.closure (Set.range tGen) := by
      rw [hc0T]
      have e : ([(2, true), (3, true), (4, true)] : List (Fin 6 × Bool)) =
          [(2, true)] ++ [(3, true)] ++ [(4, true)] := rfl
      rw [e, val6_append, val6_append]
      refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
      · exact Subgroup.subset_closure ⟨0, rfl⟩
      · exact Subgroup.subset_closure ⟨1, rfl⟩
      · exact Subgroup.subset_closure ⟨2, rfl⟩
    have hψ : c.ψ (val6 (vExp (eW c0))) ∈ T.subgroupOf (Subgroup.normalizer (T : Set G)) := by
      rw [← c.map_t]
      exact Subgroup.mem_map_of_mem c.ψ.toMonoidHom hE0mem
    have hzT : c.phi (val6 (vExp (eW c0))) ∈ T := Subgroup.mem_subgroupOf.1 hψ
    have hz1 : c.phi (val6 (vExp (eW c0))) ≠ 1 := by
      intro h
      have h1 : val6 (vExp (eW c0)) = 1 := c.phi_injective (by rw [h, map_one])
      have h2 : epsN hf (Multiplicative.ofAdd c0) = epsN hf (Multiplicative.ofAdd 0) := by
        rw [ofAdd_zero, map_one]
        exact h1
      exact hc0 (Multiplicative.ofAdd.injective (epsN_injective hf h2))
    have hxz : c.phi (val6 (vExp (eW c0))) * (x : G) = (x : G) * c.phi (val6 (vExp (eW c0))) :=
      (congrArg (fun y : c.K => (y : G)) (hx (Multiplicative.ofAdd c0))).symm
    have hxN : (x : G) ∈ Subgroup.normalizer (T : Set G) :=
      hyp.cent_le _ hzT hz1 (Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff.1 hh]
        exact hxz)
    set n : PG 6 rels6 := c.ψ.symm ⟨(x : G), hxN⟩ with hn
    have hnx : c.phi n = (x : G) := by
      show (((c.ψ (c.ψ.symm ⟨(x : G), hxN⟩)) : Subgroup.normalizer (T : Set G)) : G) = _
      rw [MulEquiv.apply_symm_apply]
    have hcomm : ∀ j : Fin 3, n * val6 (vExp (eW (Pi.single j 1))) =
        val6 (vExp (eW (Pi.single j 1))) * n := by
      intro j
      apply c.phi_injective
      rw [map_mul, map_mul, hnx]
      exact congrArg (fun y : c.K => (y : G)) (hx (Multiplicative.ofAdd (Pi.single j 1)))
    obtain ⟨c', hc'⟩ := hf.e_cent n hcomm
    refine ⟨Multiplicative.ofAdd c', Subtype.ext ?_⟩
    rw [T1Config.epsK_val, ← hc', hnx]

theorem T1Config.d8Hyp (hf : PFacts) :
    D8Hyp (c.epsK hf) (evalWord3 c.aK (castV sV)) (evalWord3 c.aK (castV rV)) mS mR := by
  have hv := c.val_V
  refine ⟨?_, ?_, ?_, ?_, ?_, hf.d8_dist⟩
  · apply Subtype.ext
    show (((evalWord3 c.aK (castV sV) : c.K) : G) * ((evalWord3 c.aK (castV sV) : c.K) : G)) = 1
    rw [hv, ← map_mul, ← val6_append, ← vExp_append, hf.d8_sq, map_one]
  · have h4 : ∀ z : c.K, z ^ 4 = z * z * z * z := fun z => by simp [pow_succ]
    rw [h4]
    apply Subtype.ext
    show (((evalWord3 c.aK (castV rV) : c.K) : G) * ((evalWord3 c.aK (castV rV) : c.K) : G) *
      ((evalWord3 c.aK (castV rV) : c.K) : G) * ((evalWord3 c.aK (castV rV) : c.K) : G)) = 1
    rw [hv, ← map_mul, ← map_mul, ← map_mul, ← val6_append, ← val6_append, ← val6_append,
      ← vExp_append, ← vExp_append, ← vExp_append, hf.d8_four, map_one]
  · apply eq_inv_of_mul_eq_one_left
    apply Subtype.ext
    show (((evalWord3 c.aK (castV sV) : c.K) : G) * ((evalWord3 c.aK (castV rV) : c.K) : G) *
      ((evalWord3 c.aK (castV sV) : c.K) : G) * ((evalWord3 c.aK (castV rV) : c.K) : G)) = 1
    rw [hv, hv, ← map_mul, ← map_mul, ← map_mul, ← val6_append, ← val6_append, ← val6_append,
      ← vExp_append, ← vExp_append, ← vExp_append, hf.d8_conj, map_one]
  · intro x
    apply Subtype.ext
    show (((evalWord3 c.aK (castV sV) : c.K) : G)) * c.phi (val6 (vExp (eW x))) *
      (((evalWord3 c.aK (castV sV) : c.K) : G))⁻¹ = c.phi (val6 (vExp (eW (glAct mS x))))
    rw [hv, ← map_inv, ← map_mul, ← map_mul, hf.d8_act_s]
  · intro x
    apply Subtype.ext
    show (((evalWord3 c.aK (castV rV) : c.K) : G)) * c.phi (val6 (vExp (eW x))) *
      (((evalWord3 c.aK (castV rV) : c.K) : G))⁻¹ = c.phi (val6 (vExp (eW (glAct mR x))))
    rw [hv, ← map_inv, ← map_mul, ← map_mul, hf.d8_act_r]

end Config

theorem pStatement_of_facts (hf : PFacts) : PStatement := by
  intro G _ _ _ T T₁ hyp c r hr
  have hA := c.affHyp hf hyp
  have hD := c.d8Hyp hf
  have hrel : ∀ r ∈ pRs, evalWord3 c.aK r.1 = evalWord3 c.aK r.2 := by
    intro r hr
    simp only [pRs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · apply Subtype.ext
      rw [c.val_evalWord3, c.val_evalWord3]
      show evalWord3 c.aG [(2, true), (2, true)] = evalWord3 c.aG []
      rw [evalWord3_cons, evalWord3_cons, evalWord3_nil]
      simpa [T1Config.aG_two] using c.gg
    · apply Subtype.ext
      rw [c.val_evalWord3, c.val_evalWord3]
      show evalWord3 c.aG ([(2, true)] ++ castV wA ++ [(2, true)]) = evalWord3 c.aG (castV wB)
      have e1 : evalWord3 c.aG [(2, true)] = c.g := by
        rw [evalWord3_cons, evalWord3_nil]
        simp [T1Config.aG_two]
      rw [evalWord3_append, evalWord3_append, e1, c.eval_castV, c.eval_castV,
        ← hf.theta_rel.1, ← hf.theta_rel.2]
      have hg' : c.g⁻¹ = c.g := inv_eq_of_mul_eq_one_right c.gg
      have := c.conj_dExp uW
      rw [hg'] at this
      exact this
  have hEw : ∀ j, evalWord3 c.aK (pEw j) = c.epsK hf (Multiplicative.ofAdd (Pi.single j 1)) := by
    intro j
    apply Subtype.ext
    rw [pEw, c.val_V]
    rfl
  have hK := rels_of_finCheck hA hD hf.fin hrel hEw
  rw [pRels_eq, List.mem_map] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  rw [c.eval_expand3, ← c.val_evalWord3, hK w hw]
  rfl

end CFSG.CGT.T75JM
