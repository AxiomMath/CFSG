module

public import CFSG.CGT.T75M23.P7Data
public import CFSG.CGT.T75M23.L2FTab7
public import CFSG.CGT.T75JM.L2GModel

public section

namespace CFSG.CGT.T75M23

open CFSG.CosetTable
open CFSG.CGT.T75JM (V3 glAct matD FinCheck OntoEmb AffHyp D8Hyp evalWord3 evalWord3_append
  evalWord3_map rels_of_finCheck)

theorem evalWord3_nil7 {H : Type*} [Group H] (x : Fin 3 → H) : evalWord3 x [] = 1 := rfl

theorem evalWord3_cons7 {H : Type*} [Group H] (x : Fin 3 → H) (p : Fin 3 × Bool)
    (w : List (Fin 3 × Bool)) :
    evalWord3 x (p :: w) = (if p.2 then x p.1 else (x p.1)⁻¹) * evalWord3 x w := by
  simp [evalWord3]

theorem subst7_append {α β : Type} (f : α → List β) (u u' : List α) :
    subst7 f (u ++ u') = subst7 f u ++ subst7 f u' := by
  induction u with
  | nil => rfl
  | cons a u ih => simp [subst7, ih]

theorem vExp7_append (u u' : List (Fin 2 × Bool)) : vExp7 (u ++ u') = vExp7 u ++ vExp7 u' :=
  subst7_append _ u u'

structure PCfg7 {G : Type} [Group G] (T T₁ : Subgroup G) (k : Fin 2) where
  E : OntoEmb N7 (Subgroup.normalizer (T : Set G))
  hT : ∀ x, x ∈ n7T ↔ E.Φ x ∈ T
  g : G
  hgg : g * g = E.Φ (n7 (d0W7 k))
  hconj : ∀ i : Fin 3, g * E.Φ (n7 (dGen7 i)) * g⁻¹ = E.Φ (n7 (thetaW7 k i))

section Config

variable {G : Type} [Group G] {T T₁ : Subgroup G} {k : Fin 2} (c : PCfg7 T T₁ k)

@[expose] def PCfg7.aG : Fin 3 → G := ![c.E.Φ (n7 (vGen7 0)), c.E.Φ (n7 (vGen7 1)), c.g]

theorem PCfg7.aG_castSucc (i : Fin 2) : c.aG (Fin.castSucc i) = c.E.Φ (n7 (vGen7 i)) := by
  fin_cases i <;> rfl

theorem PCfg7.aG_two : c.aG 2 = c.g := rfl

theorem PCfg7.eval_castV (u : List (Fin 2 × Bool)) :
    evalWord3 c.aG (castV7 u) = c.E.Φ (n7 (vExp7 u)) := by
  induction u with
  | nil =>
    show evalWord3 c.aG [] = c.E.Φ (n7 [])
    rw [n7_nil, map_one]
    rfl
  | cons p u ih =>
    have h1 : castV7 (p :: u) = (Fin.castSucc p.1, p.2) :: castV7 u := rfl
    have h2 : vExp7 (p :: u) = (if p.2 then vGen7 p.1 else invWord7 (vGen7 p.1)) ++ vExp7 u := rfl
    rw [h1, evalWord3_cons7, h2, n7_append, map_mul, ih]
    congr 1
    rcases p with ⟨i, b⟩
    cases b
    · simp [n7_invWord, c.aG_castSucc]
    · simp [c.aG_castSucc]

theorem PCfg7.conj_dExp (u : List (Fin 3 × Bool)) :
    c.g * c.E.Φ (n7 (dExp7 u)) * c.g⁻¹ = c.E.Φ (n7 (thExp7 k u)) := by
  induction u with
  | nil =>
    show c.g * c.E.Φ (n7 []) * c.g⁻¹ = c.E.Φ (n7 [])
    rw [n7_nil, map_one]
    group
  | cons p u ih =>
    have h1 : dExp7 (p :: u) = (if p.2 then dGen7 p.1 else invWord7 (dGen7 p.1)) ++ dExp7 u := rfl
    have h2 : thExp7 k (p :: u) =
        (if p.2 then thetaW7 k p.1 else invWord7 (thetaW7 k p.1)) ++ thExp7 k u := rfl
    rw [h1, h2, n7_append, n7_append, map_mul, map_mul]
    have hl : c.g * c.E.Φ (n7 (if p.2 then dGen7 p.1 else invWord7 (dGen7 p.1))) * c.g⁻¹ =
        c.E.Φ (n7 (if p.2 then thetaW7 k p.1 else invWord7 (thetaW7 k p.1))) := by
      rcases p with ⟨i, b⟩
      cases b
      · simp only [Bool.false_eq_true, ite_false, n7_invWord, map_inv]
        have := c.hconj i
        calc c.g * (c.E.Φ (n7 (dGen7 i)))⁻¹ * c.g⁻¹
            = (c.g * c.E.Φ (n7 (dGen7 i)) * c.g⁻¹)⁻¹ := by group
          _ = (c.E.Φ (n7 (thetaW7 k i)))⁻¹ := by rw [this]
      · simpa using c.hconj i
    have key : ∀ A B : G, c.g * (A * B) * c.g⁻¹ = (c.g * A * c.g⁻¹) * (c.g * B * c.g⁻¹) :=
      fun A B => by group
    rw [key, hl, ih]

@[expose] def PCfg7.K : Subgroup G := Subgroup.closure (Set.range c.aG)

@[expose] def PCfg7.aK : Fin 3 → c.K := fun j => ⟨c.aG j, Subgroup.subset_closure ⟨j, rfl⟩⟩

theorem PCfg7.val_evalWord3 (w : List (Fin 3 × Bool)) :
    ((evalWord3 c.aK w : c.K) : G) = evalWord3 c.aG w := by
  have := evalWord3_map c.K.subtype c.aK w
  exact this

theorem PCfg7.val_V (u : List (Fin 2 × Bool)) :
    ((evalWord3 c.aK (castV7 u) : c.K) : G) = c.E.Φ (n7 (vExp7 u)) := by
  rw [c.val_evalWord3, c.eval_castV]

@[expose] def epsN7 (hf : PFacts7) : Multiplicative V3 →* N7 where
  toFun x := n7 (vExp7 (eW7 x.toAdd))
  map_one' := by
    have h := hf.e_mul 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.trans (mul_one _).symm)
  map_mul' x y := (hf.e_mul x.toAdd y.toAdd).symm

theorem epsN7_injective (hf : PFacts7) : Function.Injective (epsN7 hf) := fun _ _ h =>
  Multiplicative.toAdd.injective (hf.e_inj _ _ h)

@[expose] noncomputable def PCfg7.epsK (hf : PFacts7) : Multiplicative V3 →* c.K :=
  (c.E.Φ.comp (epsN7 hf)).codRestrict c.K fun x => by
    show c.E.Φ (n7 (vExp7 (eW7 x.toAdd))) ∈ c.K
    rw [← c.eval_castV, ← c.val_evalWord3]
    exact (evalWord3 c.aK _).2

theorem PCfg7.epsK_val (hf : PFacts7) (x : V3) :
    ((c.epsK hf (Multiplicative.ofAdd x) : c.K) : G) = c.E.Φ (n7 (vExp7 (eW7 x))) := rfl

theorem PCfg7.affHyp (hf : PFacts7)
    (hcent : ∀ d ∈ T, d ≠ 1 →
      Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer (T : Set G)) :
    AffHyp (c.epsK hf) c.aK mv7 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    have h : Subgroup.closure (((↑) : c.K → G) ⁻¹' Set.range c.aG) = ⊤ :=
      Subgroup.closure_closure_coe_preimage
    have hs : (((↑) : c.K → G) ⁻¹' Set.range c.aG : Set c.K) = Set.range c.aK := by
      ext x
      constructor
      · rintro ⟨j, hj⟩
        exact ⟨j, Subtype.ext hj⟩
      · rintro ⟨j, rfl⟩
        exact ⟨j, rfl⟩
    rw [hs] at h
    exact h
  ·
    intro x y h
    apply epsN7_injective hf
    apply c.E.inj
    exact congrArg (fun z : c.K => (z : G)) h
  ·
    intro j x
    apply Subtype.ext
    have hmul : ((c.aK j * c.epsK hf (Multiplicative.ofAdd x) * (c.aK j)⁻¹ : c.K) : G) =
        c.aG j * c.E.Φ (n7 (vExp7 (eW7 x))) * (c.aG j)⁻¹ := rfl
    rw [hmul]
    show _ = c.E.Φ (n7 (vExp7 (eW7 (glAct (mv7 j) x))))
    fin_cases j
    · show c.E.Φ (n7 (vGen7 0)) * c.E.Φ (n7 (vExp7 (eW7 x))) * (c.E.Φ (n7 (vGen7 0)))⁻¹ = _
      rw [← map_inv, ← map_mul, ← map_mul, hf.act_v1]
      rfl
    · show c.E.Φ (n7 (vGen7 1)) * c.E.Φ (n7 (vExp7 (eW7 x))) * (c.E.Φ (n7 (vGen7 1)))⁻¹ = _
      rw [← map_inv, ← map_mul, ← map_mul, hf.act_v2]
      rfl
    · show c.g * c.E.Φ (n7 (vExp7 (eW7 x))) * c.g⁻¹ = c.E.Φ (n7 (vExp7 (eW7 (glAct mG7 x))))
      rw [← (hf.act_g k x).1, c.conj_dExp, (hf.act_g k x).2]
  ·
    intro x hx
    obtain ⟨c0, hc0, hc0T⟩ := hf.e_tors
    have hE0mem : n7 (vExp7 (eW7 c0)) ∈ n7T := by
      rw [hc0T]
      have e : ([(2, true), (5, true)] : Word6) = [(2, true)] ++ [(5, true)] := rfl
      rw [e, n7_append]
      refine Subgroup.mul_mem _ ?_ ?_
      · exact Subgroup.subset_closure ⟨0, rfl⟩
      · exact Subgroup.subset_closure ⟨3, rfl⟩
    have hzT : c.E.Φ (n7 (vExp7 (eW7 c0))) ∈ T := (c.hT _).1 hE0mem
    have hz1 : c.E.Φ (n7 (vExp7 (eW7 c0))) ≠ 1 := by
      intro h
      have h1 : n7 (vExp7 (eW7 c0)) = 1 := c.E.inj (by rw [h, map_one])
      have h2 : epsN7 hf (Multiplicative.ofAdd c0) = epsN7 hf (Multiplicative.ofAdd 0) := by
        rw [ofAdd_zero, map_one]
        exact h1
      exact hc0 (Multiplicative.ofAdd.injective (epsN7_injective hf h2))
    have hxz : c.E.Φ (n7 (vExp7 (eW7 c0))) * (x : G) = (x : G) * c.E.Φ (n7 (vExp7 (eW7 c0))) :=
      (congrArg (fun y : c.K => (y : G)) (hx (Multiplicative.ofAdd c0))).symm
    have hxN : (x : G) ∈ Subgroup.normalizer (T : Set G) :=
      hcent _ hzT hz1 (Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff.1 hh]
        exact hxz)
    obtain ⟨n, hnx⟩ := c.E.surj (x : G) hxN
    have hcomm : ∀ j : Fin 3, n * n7 (vExp7 (eW7 (Pi.single j 1))) =
        n7 (vExp7 (eW7 (Pi.single j 1))) * n := by
      intro j
      apply c.E.inj
      rw [map_mul, map_mul, hnx]
      exact congrArg (fun y : c.K => (y : G)) (hx (Multiplicative.ofAdd (Pi.single j 1)))
    obtain ⟨c', hc'⟩ := hf.e_cent n hcomm
    refine ⟨Multiplicative.ofAdd c', Subtype.ext ?_⟩
    rw [PCfg7.epsK_val, ← hc', hnx]

theorem PCfg7.d8Hyp (hf : PFacts7) :
    D8Hyp (c.epsK hf) (evalWord3 c.aK (castV7 sV7)) (evalWord3 c.aK (castV7 rV7)) mS7 mR7 := by
  have hv := c.val_V
  refine ⟨?_, ?_, ?_, ?_, ?_, hf.d8_dist⟩
  · apply Subtype.ext
    show (((evalWord3 c.aK (castV7 sV7) : c.K) : G) * ((evalWord3 c.aK (castV7 sV7) : c.K) : G)) = 1
    rw [hv, ← map_mul, ← n7_append, ← vExp7_append, hf.d8_sq, map_one]
  · have h4 : ∀ z : c.K, z ^ 4 = z * z * z * z := fun z => by simp [pow_succ]
    rw [h4]
    apply Subtype.ext
    show (((evalWord3 c.aK (castV7 rV7) : c.K) : G) * ((evalWord3 c.aK (castV7 rV7) : c.K) : G) *
      ((evalWord3 c.aK (castV7 rV7) : c.K) : G) * ((evalWord3 c.aK (castV7 rV7) : c.K) : G)) = 1
    rw [hv, ← map_mul, ← map_mul, ← map_mul, ← n7_append, ← n7_append, ← n7_append,
      ← vExp7_append, ← vExp7_append, ← vExp7_append, hf.d8_four, map_one]
  · apply eq_inv_of_mul_eq_one_left
    apply Subtype.ext
    show (((evalWord3 c.aK (castV7 sV7) : c.K) : G) * ((evalWord3 c.aK (castV7 rV7) : c.K) : G) *
      ((evalWord3 c.aK (castV7 sV7) : c.K) : G) * ((evalWord3 c.aK (castV7 rV7) : c.K) : G)) = 1
    rw [hv, hv, ← map_mul, ← map_mul, ← map_mul, ← n7_append, ← n7_append, ← n7_append,
      ← vExp7_append, ← vExp7_append, ← vExp7_append, hf.d8_conj, map_one]
  · intro x
    apply Subtype.ext
    show (((evalWord3 c.aK (castV7 sV7) : c.K) : G)) * c.E.Φ (n7 (vExp7 (eW7 x))) *
      (((evalWord3 c.aK (castV7 sV7) : c.K) : G))⁻¹ = c.E.Φ (n7 (vExp7 (eW7 (glAct mS7 x))))
    rw [hv, ← map_inv, ← map_mul, ← map_mul, hf.d8_act_s]
  · intro x
    apply Subtype.ext
    show (((evalWord3 c.aK (castV7 rV7) : c.K) : G)) * c.E.Φ (n7 (vExp7 (eW7 x))) *
      (((evalWord3 c.aK (castV7 rV7) : c.K) : G))⁻¹ = c.E.Φ (n7 (vExp7 (eW7 (glAct mR7 x))))
    rw [hv, ← map_inv, ← map_mul, ← map_mul, hf.d8_act_r]

theorem PCfg7.hEw (hf : PFacts7) (j : Fin 3) :
    evalWord3 c.aK (pEw7 j) = c.epsK hf (Multiplicative.ofAdd (Pi.single j 1)) := by
  apply Subtype.ext
  rw [pEw7, c.val_V]
  rfl

theorem PCfg7.eval_gg : evalWord3 c.aG [(2, true), (2, true)] = c.g * c.g := by
  rw [evalWord3_cons7, evalWord3_cons7, evalWord3_nil7]
  simp [PCfg7.aG_two]

theorem PCfg7.rels_of_zero [Finite G] (c : PCfg7 T T₁ 0) (hf : PFacts7)
    (hcent : ∀ d ∈ T, d ≠ 1 →
      Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer (T : Set G)) :
    ∀ w ∈ pWords7, evalWord3 c.aG w = 1 := by
  have hA := c.affHyp hf hcent
  have hD := c.d8Hyp hf
  have hg2 : c.g * c.g = 1 := by
    have := c.hgg
    simpa [d0W7, n7_nil] using this
  have hrel : ∀ r ∈ pRs7a, evalWord3 c.aK r.1 = evalWord3 c.aK r.2 := by
    intro r hr
    simp only [pRs7a, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · apply Subtype.ext
      rw [c.val_evalWord3, c.val_evalWord3, c.eval_gg]
      show c.g * c.g = evalWord3 c.aG []
      rw [evalWord3_nil7]
      exact hg2
    · apply Subtype.ext
      rw [c.val_evalWord3, c.val_evalWord3]
      show evalWord3 c.aG ([(2, true)] ++ castV7 wA7 ++ [(2, false)]) = evalWord3 c.aG (castV7 wB7)
      have e1 : evalWord3 c.aG [(2, true)] = c.g := by
        rw [evalWord3_cons7, evalWord3_nil7]
        simp [PCfg7.aG_two]
      have e2 : evalWord3 c.aG [(2, false)] = c.g⁻¹ := by
        rw [evalWord3_cons7, evalWord3_nil7]
        simp [PCfg7.aG_two]
      rw [evalWord3_append, evalWord3_append, e1, e2, c.eval_castV, c.eval_castV,
        ← hf.theta_rel.1, ← hf.theta_rel.2]
      exact c.conj_dExp uW7
  have hK := rels_of_finCheck hA hD hf.fin0 hrel (c.hEw hf)
  intro w hw
  rw [← c.val_evalWord3, hK w hw]
  rfl

theorem PCfg7.false_of_one [Finite G] (c : PCfg7 T T₁ 1) (hf : PFacts7)
    (hcent : ∀ d ∈ T, d ≠ 1 →
      Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer (T : Set G)) :
    False := by
  have hA := c.affHyp hf hcent
  have hD := c.d8Hyp hf
  have hrel : ∀ r ∈ pRs7b, evalWord3 c.aK r.1 = evalWord3 c.aK r.2 := by
    intro r hr
    simp only [pRs7b, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    apply Subtype.ext
    rw [c.val_evalWord3, c.val_evalWord3, c.eval_gg, c.eval_castV, ← hf.d0_rel]
    exact c.hgg
  have hK := rels_of_finCheck hA hD hf.fin1 hrel (c.hEw hf)
  have h0 := hK (pEw7 0) (List.mem_singleton_self _)
  rw [c.hEw hf 0] at h0
  have h1 : c.epsK hf (Multiplicative.ofAdd (Pi.single 0 1)) =
      c.epsK hf (Multiplicative.ofAdd 0) := by
    rw [h0, ofAdd_zero, map_one]
  have h2 := Multiplicative.ofAdd.injective (hA.inj h1)
  have h3 := congrFun h2 0
  simp at h3

end Config

end CFSG.CGT.T75M23
