module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainT0Check
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainLevelTwo

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1 CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem toVec4_addV4 (v w : Array ℕ) : toVec4 (addV4 v w) = toVec4 v + toVec4 w := by
  ext j
  simp [toVec4, addV4, ZMod.natCast_mod]

theorem toVec4_negV4 (v : Array ℕ) : toVec4 (negV4 v) = -toVec4 v := by
  ext j
  simp only [toVec4, negV4, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, j.isLt,
    dite_true, Option.getD_some, ZMod.natCast_mod, Nat.cast_mul, Pi.neg_apply]
  have : ((3 : ℕ) : ZMod 4) = -1 := by decide
  rw [this, neg_one_mul]

theorem toVec4_dig4_zero : toVec4 (dig4 0) = 0 := by
  ext j
  simp [toVec4, dig4]

theorem toVec4_dig4_one : toVec4 (dig4 1) = Pi.single 0 1 := by
  ext j
  fin_cases j <;> simp [toVec4, dig4]

theorem eq_of_toVec4_eq' {v w : Array ℕ} (hv : v.size = 6) (hw : w.size = 6)
    (hv4 : ∀ j < 6, v.getD j 0 < 4) (hw4 : ∀ j < 6, w.getD j 0 < 4) (h : toVec4 v = toVec4 w) :
    v = w := by
  refine Array.ext (by rw [hv, hw]) fun j hj hj' => ?_
  have hj6 : j < 6 := hv ▸ hj
  have h1 := congrFun h ⟨j, hj6⟩
  simp only [toVec4] at h1
  have h2 := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h1
  rw [Nat.mod_eq_of_lt (hv4 j hj6), Nat.mod_eq_of_lt (hw4 j hj6)] at h2
  simpa [Array.getD_eq_getD_getElem?, hj, hj'] using h2

theorem addV4_size (v w : Array ℕ) : (addV4 v w).size = 6 := by simp [addV4]

theorem addV4_lt (v w : Array ℕ) : ∀ j < 6, (addV4 v w).getD j 0 < 4 := fun j hj => by
  simp [addV4, Array.getD_eq_getD_getElem?, hj, Nat.mod_lt]

section Model

variable {G : Type*} [Group G] {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}

structure T0Data (hR : RadicalData .plus L U Q P a ψ p) (W : Subgroup G) (t : G)
    (Φ : (Fin 6 → ZMod 4) → G) (ℓ : ℕ → G) : Prop where
  coord : Coord4 W ψ Φ
  inv : ∀ x ∈ W, t * x * t⁻¹ = x⁻¹
  t_not_mem : t ∉ W
  t2 : t * t = 1
  W_N : ∀ x ∈ W, x ∈ normalizer (Q : Set G)
  W_lin : ∀ x ∈ W, ∀ v, lin ψ x v = v
  t_N : t ∈ normalizer (Q : Set G)
  t_lin : ∀ v, lin ψ t v = v
  ell_N : ∀ i, ℓ i ∈ normalizer (Q : Set G)
  ell_lin : ∀ i < 64, ∀ v, lin ψ (ℓ i) v = s0Mat .plus i *ᵥ v
  ell_mul : ∀ i < 64, ∀ j < 64, ℓ i * ℓ j = ℓ (tabGet (mulTab .plus) i j)
  ell_t : ∀ i, ℓ i * t = t * ℓ i
  ell_rep : ∀ i < 64, Rep Φ (ℓ i) (toMat4 (liftTab.getD i #[]))

@[expose] def muT (Φ : (Fin 6 → ZMod 4) → G) (t : G) (ℓ : ℕ → G) (g : Array ℕ × Bool × ℕ) :
    G :=
  Φ (toVec4 g.1) * (if g.2.1 then t else 1) * ℓ g.2.2

namespace T0Data

variable {hR : RadicalData .plus L U Q P a ψ p} {W : Subgroup G} {t : G}
  {Φ : (Fin 6 → ZMod 4) → G} {ℓ : ℕ → G} (hD : T0Data hR W t Φ ℓ)
include hD

theorem conj_t (e : Bool) (w : Fin 6 → ZMod 4) :
    (if e then t else 1) * Φ w * (if e then t else 1)⁻¹ = Φ (if e then -w else w) := by
  cases e
  · simp
  · simp only [ite_true]
    rw [hD.inv _ (hD.coord.mem w), hD.coord.neg]

theorem t_pow_mul (e e' : Bool) :
    (if e then t else 1) * (if e' then t else 1) = if (e ^^ e') then t else 1 := by
  cases e <;> cases e' <;> simp [hD.t2]

theorem muT_mul (g h : Array ℕ × Bool × ℕ) (hg : g.2.2 < 64) (hh : h.2.2 < 64) :
    muT Φ t ℓ g * muT Φ t ℓ h = muT Φ t ℓ (tmul (mulTab .plus) liftTab g h) := by
  obtain ⟨v, e, s⟩ := g
  obtain ⟨v', e', s'⟩ := h
  simp only at hg hh
  have hcomm : ℓ s * (if e' then t else 1) = (if e' then t else 1) * ℓ s := by
    cases e' <;> simp [hD.ell_t]
  have e1 : muT Φ t ℓ (v, e, s) * muT Φ t ℓ (v', e', s') =
      Φ (toVec4 v) * ((if e then t else 1) * (ℓ s * Φ (toVec4 v') * (ℓ s)⁻¹) *
        (if e then t else 1)⁻¹) * ((if e then t else 1) * (if e' then t else 1)) *
        (ℓ s * ℓ s') := by
    simp only [muT]
    calc Φ (toVec4 v) * (if e then t else 1) * ℓ s *
          (Φ (toVec4 v') * (if e' then t else 1) * ℓ s') =
        Φ (toVec4 v) * ((if e then t else 1) * (ℓ s * Φ (toVec4 v') * (ℓ s)⁻¹) *
          (if e then t else 1)⁻¹) * (if e then t else 1) * (ℓ s * (if e' then t else 1)) *
          ℓ s' := by group
      _ = _ := by rw [hcomm]; group
  rw [e1, hD.ell_rep s hg (toVec4 v'), hD.conj_t, hD.t_pow_mul, hD.ell_mul s hg s' hh,
    ← hD.coord.add]
  simp only [muT, tmul]
  congr 2
  rw [toVec4_addV4]
  congr 1
  cases e
  · simp [toVec4_mv4]
  · simp [toVec4_mv4, toVec4_negV4]

theorem te_N (e : Bool) : (if e then t else 1) ∈ normalizer (Q : Set G) := by
  cases e
  · exact one_mem _
  · exact hD.t_N

theorem te_lin (e : Bool) (v : V6) : lin ψ (if e then t else 1) v = v := by
  cases e
  · exact hR.lin_one v
  · exact hD.t_lin v

theorem lin_muT (g : Array ℕ × Bool × ℕ) (hg : g.2.2 < 64) (v : V6) :
    lin ψ (muT Φ t ℓ g) v = s0Mat .plus g.2.2 *ᵥ v := by
  have h1 := hD.W_N _ (hD.coord.mem (toVec4 g.1))
  simp only [muT]
  rw [hR.lin_mul (mul_mem h1 (hD.te_N _)) (hD.ell_N _), hR.lin_mul h1 (hD.te_N _),
    hD.ell_lin _ hg, hD.te_lin, hD.W_lin _ (hD.coord.mem _)]

theorem muT_inj {g h : Array ℕ × Bool × ℕ} (hg : g.2.2 < 64)
    (hh : h.2.2 < 64) (hg6 : g.1.size = 6) (hh6 : h.1.size = 6)
    (hg4 : ∀ j < 6, g.1.getD j 0 < 4) (hh4 : ∀ j < 6, h.1.getD j 0 < 4)
    (heq : muT Φ t ℓ g = muT Φ t ℓ h) : g = h := by
  obtain ⟨v, e, s⟩ := g
  obtain ⟨v', e', s'⟩ := h
  simp only at hg hh hg6 hh6 hg4 hh4
  have hs : s = s' := eq_of_mulVec_eq .plus hg hh fun x => by
    have h1 := hD.lin_muT (v, e, s) hg x
    have h2 := hD.lin_muT (v', e', s') hh x
    rw [heq] at h1
    exact h1.symm.trans h2
  subst hs
  have h2 : Φ (toVec4 v) * (if e then t else 1) = Φ (toVec4 v') * (if e' then t else 1) :=
    mul_right_cancel (b := ℓ s) heq
  have he : e = e' := by
    by_contra hne
    apply hD.t_not_mem
    cases e <;> cases e'
    · exact absurd rfl hne
    · simp only [Bool.false_eq_true, ite_false, mul_one, ite_true] at h2
      have : t = (Φ (toVec4 v'))⁻¹ * Φ (toVec4 v) := by rw [h2]; group
      rw [this]
      exact mul_mem (inv_mem (hD.coord.mem _)) (hD.coord.mem _)
    · simp only [ite_true, Bool.false_eq_true, ite_false, mul_one] at h2
      have : t = (Φ (toVec4 v))⁻¹ * Φ (toVec4 v') := by rw [← h2]; group
      rw [this]
      exact mul_mem (inv_mem (hD.coord.mem _)) (hD.coord.mem _)
    · exact absurd rfl hne
  subst he
  have h3 : Φ (toVec4 v) = Φ (toVec4 v') := mul_right_cancel h2
  rw [eq_of_toVec4_eq' hg6 hh6 hg4 hh4 (hD.coord.injective h3)]

end T0Data

end Model

section Complement

variable {G : Type*} [Group G] {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p u : Fin 6 → G}

theorem twoV_vecBits (r : V6) :
    toVec4 (twoV (vecBits r)) = liftV r + liftV r := by
  ext j
  simp only [toVec4, twoV, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, j.isLt, dite_true,
    Option.getD_some, testBit_vecBits, liftV, Pi.add_apply]
  rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) (r j) with h | h <;> rw [h] <;> decide

theorem Coord4.phi_two {A : Subgroup G} {Φ : (Fin 6 → ZMod 4) → G} (hΦ : Coord4 A ψ Φ) (r : V6) :
    Φ (toVec4 (twoV (vecBits r))) = ψ r := by
  rw [twoV_vecBits, hΦ.add, hΦ.sq, red_liftV]

theorem UData.exists_mem_closure
    (hR : RadicalData ε L U Q P a ψ p) (hu : UData ε U Q ψ u) {i : ℕ} (hi : i < 64) :
    ∃ x ∈ closure (Set.range u), ∀ v, lin ψ x v = s0Mat ε i *ᵥ v := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact ⟨1, one_mem _, fun v => by rw [hR.lin_one, s0Mat_zero, one_mulVec]⟩
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have ht := (s0_facts ε).2.2.2.2.2.2 i' (by omega)
      simp only [treeOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ht
      obtain ⟨⟨hj, hk⟩, he⟩ := ht
      obtain ⟨x, hxU, hx⟩ := ih _ hj (by omega)
      refine ⟨u ⟨_, hk⟩ * x, mul_mem (subset_closure ⟨_, rfl⟩) hxU, fun v => ?_⟩
      have hUle := (closure_le U).2 (Set.range_subset_iff.2 hu.u_mem)
      have hNu := hR.P_le_normalizer (hR.U_le_P (hu.u_mem ⟨_, hk⟩))
      have hNx := hR.P_le_normalizer (hR.U_le_P (hUle hxU))
      rw [hR.lin_mul hNu hNx, hx]
      have hlu : ∀ w, lin ψ (u ⟨_, hk⟩) w =
          toMat 6 6 (uRows ε ((s0Tree ε).getD (i' + 1) (0, 0)).1) *ᵥ w := fun w => by
        rw [hR.lin_eq_iff hNu]
        exact hu.u_act _ _
      rw [hlu, mulVec_mulVec, s0Mat, s0Mat, ← toMat_bmul, he]

theorem eq_of_lin_eq_closure (hS : Setup ε t L U Q P a ψ p) (hu : UData ε U Q ψ u)
    (hU6 : closure (Set.range u) ⊓ Q = ⊥) {x y : G} (hx : x ∈ closure (Set.range u))
    (hy : y ∈ closure (Set.range u)) (h : ∀ v, lin ψ x v = lin ψ y v) : x = y := by
  have hUle := (closure_le U).2 (Set.range_subset_iff.2 hu.u_mem)
  have hq := mul_inv_mem_Q_of_lin_eq hS (hS.rad.U_le_P (hUle hx)) (hS.rad.U_le_P (hUle hy)) h
  have h1 : x * y⁻¹ ∈ closure (Set.range u) ⊓ Q :=
    Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hy), hq⟩
  rw [hU6, mem_bot] at h1
  exact mul_inv_eq_one.1 h1

end Complement

section Kill

variable {G : Type*} [Group G] {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p u : Fin 6 → G}

theorem vecBits_single (j : Fin 6) : vecBits (Pi.single j 1 : V6) = 2 ^ (j : ℕ) := by
  have h : 2 ^ (j : ℕ) < 64 :=
    calc 2 ^ (j : ℕ) < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) j.isLt
      _ = 64 := by norm_num
  rw [← toVec_two_pow' j, vecBits_toVec h]

theorem homocyclic_false_plus [Finite G]
    (hS : Setup .plus t L U Q P a ψ p) (hu : UData .plus U Q ψ u)
    (hU6 : closure (Set.range u) ⊓ Q = ⊥)
    (hn3 : ∃ n ∈ normalizer ((U ⊔ zpowers t : Subgroup G) : Set G), n * t * n⁻¹ = t * a ∧
      ∀ y ∈ closure ({ψ (Pi.single 0 1), ψ (Pi.single 1 1), ψ (Pi.single 2 1), u 3, u 4, u 5} :
        Set G), n * y = y * n)
    (hNH : ∀ x ∈ normalizer ((U ⊔ zpowers t : Subgroup G) : Set G), x * t = t * x →
      x ∈ U ⊔ zpowers t)
    {W : Subgroup G} (hW : Premises t Q W) (hinv : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) : False := by
  have hR := hS.rad
  have hL := hW.level_two hS hinv
  obtain ⟨Φ, hΦ, hrepW⟩ := exists_coord_lift (ε := .plus) hS hL
    fun x hx y hy => hW.P_conj_mem hS hx hy
  have hUle : closure (Set.range u) ≤ U := (closure_le U).2 (Set.range_subset_iff.2 hu.u_mem)
  choose ℓ' hℓ'U hℓ'l using fun i : Fin 64 => hu.exists_mem_closure hR i.isLt
  let ℓ : ℕ → G := fun i => if h : i < 64 then ℓ' ⟨i, h⟩ else 1
  have hℓU : ∀ i, ℓ i ∈ closure (Set.range u) := fun i => by
    by_cases h : i < 64
    · simp only [ℓ, dite_eq_left h]; exact hℓ'U _
    · simp only [ℓ, dite_eq_right h]; exact one_mem _
  have hℓl : ∀ i < 64, ∀ v, lin ψ (ℓ i) v = s0Mat .plus i *ᵥ v := fun i hi v => by
    simp only [ℓ, dite_eq_left hi]; exact hℓ'l _ v
  have hℓP : ∀ i, ℓ i ∈ P := fun i => hR.U_le_P (hUle (hℓU i))
  have hℓN : ∀ i, ℓ i ∈ normalizer (Q : Set G) := fun i => hR.P_le_normalizer (hℓP i)
  have hℓuniq : ∀ i < 64, ∀ x ∈ closure (Set.range u),
      (∀ v, lin ψ x v = s0Mat .plus i *ᵥ v) → x = ℓ i :=
    fun i hi x hx h => eq_of_lin_eq_closure hS hu hU6 hx (hℓU i) fun v => by rw [h, hℓl i hi]
  have hℓ0 : ℓ 0 = 1 := (hℓuniq 0 (by norm_num) 1 (one_mem _) fun v => by
    rw [hR.lin_one, s0Mat_zero, one_mulVec]).symm
  have htN : t ∈ normalizer (Q : Set G) := mem_normalizer_of_conj_mem fun q hq => by
    rw [← hS.shape.commute_of_mem (hR.Q_le_L hq), mul_inv_cancel_right]
    exact hq
  have htl : ∀ v, lin ψ t v = v := fun v => by
    rw [hR.lin_eq_iff htN, ← hS.shape.commute_of_mem (hR.Q_le_L (hR.ψ_mem v)),
      mul_inv_cancel_right]
  have hWN : ∀ x ∈ W, x ∈ normalizer (Q : Set G) := fun x hx =>
    mem_normalizer_of_conj_mem fun q hq => by
      rw [hW.comm x hx q (hW.Q_le hq), mul_inv_cancel_right]
      exact hq
  have hWl : ∀ x ∈ W, ∀ v, lin ψ x v = v := fun x hx v => by
    rw [hR.lin_eq_iff (hWN x hx), hW.comm x hx _ (hW.Q_le (hR.ψ_mem v)), mul_inv_cancel_right]
  have hℓmul : ∀ i < 64, ∀ j < 64, ℓ i * ℓ j = ℓ (tabGet (mulTab .plus) i j) :=
    fun i hi j hj => hℓuniq _ (tab_lt .plus hi hj) _ (mul_mem (hℓU i) (hℓU j)) fun v => by
      rw [hR.lin_mul (hℓN i) (hℓN j), hℓl j hj, hℓl i hi, mulVec_mulVec, s0Mat_mul .plus hi hj]
  have hwords : ∀ i < 64, wordRows .plus (s0Words.getD i []) = s0Get .plus i := by
    have h := wordsCheck_spec
    simp only [wordsCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at h
    exact h
  have hℓrep : ∀ i < 64, Rep Φ (ℓ i) (toMat4 (liftTab.getD i #[])) := by
    intro i hi
    have hlt : liftTab.getD i #[] = prod4 .plus (s0Words.getD i []) := by
      simp [liftTab, Array.getD_eq_getD_getElem?, hi]
    rw [hlt, toMat4_prod4]
    have hq := mul_inv_mem_Q_of_lin_eq hS (hℓP i) (hR.wordElt_mem (s0Words.getD i []))
      fun v => by rw [hℓl i hi, lin_wordElt_eq hR, hwords i hi, s0Mat]
    have h1 := Coord4.rep_mul (hΦ.rep_of_mem_A hL.comm (hL.Q_le hq))
      (hrepW (s0Words.getD i []))
    rwa [one_mul, inv_mul_cancel_right] at h1
  have hD : T0Data hR W t Φ ℓ := ⟨hΦ, hinv, hW.t_not_mem, hS.shape.mul_self, hWN, hWl, htN, htl,
    hℓN, hℓl, hℓmul, fun i => hS.shape.commute_of_mem (hR.P_le_L (hℓP i)), hℓrep⟩
  have haQ : a ∈ Q := hR.a_eq ▸ hR.ψ_mem _
  have hat : a * t = t * a := hS.shape.commute_of_mem (hR.Q_le_L haQ)
  have hn₁W : Φ (Pi.single 0 1) ∈ W := hΦ.mem _
  have hn₁sq : Φ (Pi.single 0 1) * Φ (Pi.single 0 1) = a := by
    rw [hΦ.sq, hR.a_eq]
    congr 1
    ext j
    by_cases hj : j = 0
    · subst hj; simp [show red4 1 = 1 by decide]
    · simp [hj]
  have hn₁t : Φ (Pi.single 0 1) * t * (Φ (Pi.single 0 1))⁻¹ = t * a := by
    have h1 : t * (Φ (Pi.single 0 1))⁻¹ * t⁻¹ = Φ (Pi.single 0 1) := by
      rw [hinv _ (inv_mem hn₁W), inv_inv]
    calc Φ (Pi.single 0 1) * t * (Φ (Pi.single 0 1))⁻¹ =
        Φ (Pi.single 0 1) * (t * (Φ (Pi.single 0 1))⁻¹ * t⁻¹) * t := by group
      _ = t * a := by rw [h1, hn₁sq, hat]
  have hfix : ∀ i < 64, s0Mat .plus i *ᵥ (Pi.single 0 1 : V6) = Pi.single 0 1 := by
    intro i hi
    have h := e0Check_spec
    simp only [e0Check, List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have h1 := mulVec_toVec (s0Get .plus i) 1
    rw [h i hi, show (1 : ℕ) = 2 ^ ((0 : Fin 6) : ℕ) from rfl, toVec_two_pow'] at h1
    exact h1
  have hUn₁ : ∀ y ∈ U, Φ (Pi.single 0 1) * y * (Φ (Pi.single 0 1))⁻¹ ∈ U := by
    intro y hy
    have hyP := hR.U_le_P hy
    have hyN := hR.P_le_normalizer hyP
    obtain ⟨F, hF⟩ := hΦ.exists_rep fun x hx => hW.P_conj_mem hS hyP hx
    obtain ⟨i, hi, hyi⟩ := hu.exists_s0 hR hy
    have hred := hΦ.map_red4_of_rep hF hR.ψ_inj fun v => (hR.lin_eq_iff hyN v _).1 (hyi v)
    set d := F *ᵥ Pi.single 0 1 - Pi.single 0 1 with hd
    have hdr : (fun j => red4 (d j)) = 0 := by
      have h1 := map_red4_mulVec F (Pi.single 0 1)
      rw [hred] at h1
      have h2 : (fun j => red4 ((Pi.single 0 1 : Fin 6 → ZMod 4) j)) = (Pi.single 0 1 : V6) := by
        ext j
        by_cases hj : j = 0
        · subst hj; simp [show red4 1 = 1 by decide]
        · simp [hj]
      rw [h2, hfix i hi] at h1
      ext j
      have h3 := congrFun h1 j
      have h4 := congrFun h2 j
      simp only [hd, Pi.sub_apply, Pi.zero_apply]
      rw [map_sub, h3, h4]
      exact sub_eq_zero.2 rfl
    have hdQ : Φ d ∈ Q := hL.mem_Q _ (hΦ.mem d) (by rw [hΦ.sq, hdr, hR.ψ_zero])
    have h1 : y * Φ (Pi.single 0 1) * y⁻¹ = Φ (Pi.single 0 1) * Φ d := by
      rw [hF, ← hΦ.add, hd, add_sub_cancel]
    have hc := hW.comm _ hn₁W _ (inv_mem (hΦ.mem d))
    have e : Φ (Pi.single 0 1) * y * (Φ (Pi.single 0 1))⁻¹ = (Φ d)⁻¹ * y := by
      calc Φ (Pi.single 0 1) * y * (Φ (Pi.single 0 1))⁻¹ =
          Φ (Pi.single 0 1) * (y * Φ (Pi.single 0 1) * y⁻¹)⁻¹ * y := by group
        _ = Φ (Pi.single 0 1) * (Φ d)⁻¹ * (Φ (Pi.single 0 1))⁻¹ * y := by rw [h1]; group
        _ = (Φ d)⁻¹ * y := by rw [hc]; group
    rw [e]
    exact mul_mem (inv_mem (hR.Q_le_U hdQ)) hy
  have hn₁N : Φ (Pi.single 0 1) ∈ normalizer ((U ⊔ zpowers t : Subgroup G) : Set G) :=
    mem_normalizer_of_conj_mem fun x hx => by
      obtain ⟨y, hy, hxy | hxy⟩ := (hS.shape.mem_sup_iff hR.U_le_L).1 hx
      · rw [hxy]
        exact mem_sup_left (hUn₁ y hy)
      · rw [hxy, show Φ (Pi.single 0 1) * (y * t) * (Φ (Pi.single 0 1))⁻¹ =
          (Φ (Pi.single 0 1) * y * (Φ (Pi.single 0 1))⁻¹) *
            (Φ (Pi.single 0 1) * t * (Φ (Pi.single 0 1))⁻¹) by group, hn₁t]
        exact mul_mem (mem_sup_left (hUn₁ y hy))
          (mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left (hR.Q_le_U haQ)))
  obtain ⟨n₃, hn₃N, hn₃t, hn₃c⟩ := hn3
  have hxN : (Φ (Pi.single 0 1))⁻¹ * n₃ ∈ normalizer ((U ⊔ zpowers t : Subgroup G) : Set G) :=
    mul_mem (inv_mem hn₁N) hn₃N
  have hxt : (Φ (Pi.single 0 1))⁻¹ * n₃ * t = t * ((Φ (Pi.single 0 1))⁻¹ * n₃) := by
    have h1 : t * Φ (Pi.single 0 1) * t⁻¹ = (Φ (Pi.single 0 1))⁻¹ := hinv _ hn₁W
    have h2 : (Φ (Pi.single 0 1))⁻¹ * t * Φ (Pi.single 0 1) = t * a := by
      calc (Φ (Pi.single 0 1))⁻¹ * t * Φ (Pi.single 0 1) =
          (Φ (Pi.single 0 1))⁻¹ * (t * Φ (Pi.single 0 1) * t⁻¹) * t := by group
        _ = ((Φ (Pi.single 0 1) * Φ (Pi.single 0 1)))⁻¹ * t := by rw [h1]; group
        _ = t * a := by rw [hn₁sq, ← hat, show a⁻¹ = a from inv_eq_of_mul_eq_one_left
              (by rw [← hn₁sq]; exact hR.Q_mul_self (hn₁sq ▸ haQ))]
    have h3 : n₃ * t = t * a * n₃ := by rw [← hn₃t]; group
    have ha2 : a * a = 1 := hR.Q_mul_self haQ
    calc (Φ (Pi.single 0 1))⁻¹ * n₃ * t = (Φ (Pi.single 0 1))⁻¹ * (t * a * n₃) := by
          rw [mul_assoc, h3]
      _ = (Φ (Pi.single 0 1))⁻¹ * t * Φ (Pi.single 0 1) * ((Φ (Pi.single 0 1))⁻¹ * a * n₃) := by
          group
      _ = t * a * ((Φ (Pi.single 0 1))⁻¹ * a * n₃) := by rw [h2]
      _ = t * (a * (Φ (Pi.single 0 1))⁻¹ * a) * n₃ := by group
      _ = t * ((Φ (Pi.single 0 1))⁻¹ * (a * a)) * n₃ := by
          rw [hW.comm a (hW.Q_le haQ) _ (inv_mem hn₁W)]; group
      _ = t * ((Φ (Pi.single 0 1))⁻¹ * n₃) := by rw [ha2]; group
  have hxTH := hNH _ hxN hxt
  obtain ⟨q, e, s, hq, hs, hxμ⟩ : ∃ (q : ℕ) (e : Bool) (s : ℕ), q < 64 ∧ s < 64 ∧
      (Φ (Pi.single 0 1))⁻¹ * n₃ = muT Φ t ℓ (twoV q, e, s) := by
    obtain ⟨y, hy, hxy⟩ := (hS.shape.mem_sup_iff hR.U_le_L).1 hxTH
    obtain ⟨s, hs, hys⟩ := hu.exists_s0 hR hy
    have hyq := mul_inv_mem_Q_of_lin_eq hS (hR.U_le_P hy) (hℓP s) fun v => by rw [hys, hℓl s hs]
    obtain ⟨r, hr⟩ := hR.mem_ψ _ hyq
    have hy' : y = Φ (toVec4 (twoV (vecBits r))) * ℓ s := by
      rw [hΦ.phi_two, hr]; group
    rcases hxy with hxy | hxy
    · exact ⟨vecBits r, false, s, vecBits_lt r, hs, by rw [hxy, hy']; simp [muT]⟩
    · refine ⟨vecBits r, true, s, vecBits_lt r, hs, ?_⟩
      rw [hxy, hy']
      simp only [muT, ite_true]
      rw [mul_assoc, hS.shape.commute_of_mem (hR.P_le_L (hℓP s)), ← mul_assoc]
  have hn₁μ : muT Φ t ℓ (dig4 1, false, 0) = Φ (Pi.single 0 1) := by
    simp [muT, toVec4_dig4_one, hℓ0]
  have hZ : n₃ = muT Φ t ℓ (tmul (mulTab .plus) liftTab (dig4 1, false, 0) (twoV q, e, s)) := by
    rw [← hD.muT_mul _ _ (by norm_num) hs, hn₁μ, ← hxμ]
    group
  have hidx : ∀ k, (k = 3 ∨ k = 4 ∨ k = 5) → ∀ hk : k < 6,
      s0Get .plus (k + 1) = uRows .plus k := by
    have h := uIdxCheck_spec
    simp only [uIdxCheck, Bool.and_eq_true, beq_iff_eq] at h
    rintro k (rfl | rfl | rfl) _
    · exact h.1.1
    · exact h.1.2
    · exact h.2
  have hgens : ∀ y ∈ t0Gens, y.2.2 < 64 ∧ muT Φ t ℓ y ∈ closure ({ψ (Pi.single 0 1),
      ψ (Pi.single 1 1), ψ (Pi.single 2 1), u 3, u 4, u 5} : Set G) := by
    have hψj : ∀ j : Fin 6, muT Φ t ℓ (twoV (2 ^ (j : ℕ)), false, 0) = ψ (Pi.single j 1) := by
      intro j
      simp only [muT, Bool.false_eq_true, ite_false, mul_one, hℓ0]
      rw [← vecBits_single j, hΦ.phi_two]
    have huk : ∀ k : Fin 6, (k = 3 ∨ k = 4 ∨ k = 5) →
        muT Φ t ℓ (dig4 0, false, (k : ℕ) + 1) = u k := by
      intro k hk
      simp only [muT, Bool.false_eq_true, ite_false, mul_one, toVec4_dig4_zero, hΦ.zero,
        one_mul]
      refine (hℓuniq _ (by omega) _ (subset_closure ⟨k, rfl⟩) fun v => ?_).symm
      rw [hR.lin_eq_iff (hR.P_le_normalizer (hR.U_le_P (hu.u_mem k))), hu.u_act, s0Mat,
        hidx k (by rcases hk with rfl | rfl | rfl <;> simp) k.isLt]
    intro y hy
    simp only [t0Gens, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨by norm_num, ?_⟩
      change muT Φ t ℓ (twoV (2 ^ ((0 : Fin 6) : ℕ)), false, 0) ∈ _
      rw [hψj]
      exact subset_closure (by simp)
    · refine ⟨by norm_num, ?_⟩
      change muT Φ t ℓ (twoV (2 ^ ((1 : Fin 6) : ℕ)), false, 0) ∈ _
      rw [hψj]
      exact subset_closure (by simp)
    · refine ⟨by norm_num, ?_⟩
      change muT Φ t ℓ (twoV (2 ^ ((2 : Fin 6) : ℕ)), false, 0) ∈ _
      rw [hψj]
      exact subset_closure (by simp)
    · refine ⟨by norm_num, ?_⟩
      change muT Φ t ℓ (dig4 0, false, ((3 : Fin 6) : ℕ) + 1) ∈ _
      rw [huk 3 (by decide)]
      exact subset_closure (by simp)
    · refine ⟨by norm_num, ?_⟩
      change muT Φ t ℓ (dig4 0, false, ((4 : Fin 6) : ℕ) + 1) ∈ _
      rw [huk 4 (by decide)]
      exact subset_closure (by simp)
    · refine ⟨by norm_num, ?_⟩
      change muT Φ t ℓ (dig4 0, false, ((5 : Fin 6) : ℕ) + 1) ∈ _
      rw [huk 5 (by decide)]
      exact subset_closure (by simp)
  have hc := t0Check_spec
  simp only [t0Check, List.all_eq_true, List.mem_range, List.any_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq] at hc
  obtain ⟨y, hy, hne⟩ := hc q hq e (by cases e <;> simp) s hs
  apply hne
  obtain ⟨hy64, hyQ⟩ := hgens y hy
  have hZ64 : (tmul (mulTab .plus) liftTab (dig4 1, false, 0) (twoV q, e, s)).2.2 < 64 :=
    tab_lt .plus (by norm_num) hs
  have hcomm := hn₃c _ hyQ
  rw [hZ, hD.muT_mul _ _ hZ64 hy64, hD.muT_mul _ _ hy64 hZ64] at hcomm
  exact hD.muT_inj (tab_lt .plus hZ64 hy64) (tab_lt .plus hy64 hZ64) (addV4_size _ _)
    (addV4_size _ _) (addV4_lt _ _) (addV4_lt _ _) hcomm

end Kill

end CFSG.EvenSmallLie.OmegaEight.Chain
