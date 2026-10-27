module

public import CFSG.Certificates.Kernel.J4TreeCol.Rank
public import CFSG.Certificates.Kernel.J4TreeCol.Pair
public import CFSG.Certificates.Kernel.J4Q.RepQT2B
public import CFSG.Milestones.ASVolI.C31.J4NP.VerdictColSpec
public import CFSG.Milestones.ASVolI.C31.J4NP.TreeDefs
public import CFSG.Sporadic.J4.QT2AMod

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.J4TreeCol

open CFSG.KC.J4Q CFSG.KC.Loop CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
open CFSG.Sporadic.J4.QT2A CFSG.ASVolI CFSG.J4Tree.Native

@[expose] def PRc (g : J) (m : ℕ) : Prop := ∃ X : Array V2, WfA X ∧ encR X = m ∧ Mx g = rowsMatrix X

structure MatsOK (G : Mats) : Prop where
  consts : ∃ t0 t1 t2 t3 t4 t5 t6, Consts G.c G.rm G.one G.pad t0 t1 t2 t3 t4 t5 t6
  us_len : G.us.length = 11
  us : ∀ j < 11, PRc (uJ j) (getN G.one G.us j)
  ks_len : G.ks.length = 4
  ks : ∀ i, PRc (kJ i) (getN G.one G.ks i)
  g5 : ∀ i, PRc (gen5 i) (getN G.one G.g5 i)
  g5i : ∀ i, PRc (gen5 i)⁻¹ (getN G.one G.g5i i)

theorem getN_eq_getD (d : Nat) : ∀ (l : List Nat) (i : Nat), getN d l i = l.getD i d
  | [], i => by cases i <;> rfl
  | x :: l, 0 => rfl
  | x :: l, i + 1 => by
    change getN d l i = _
    rw [getN_eq_getD d l i]
    rfl

section Model

variable {G : Mats} (hG : MatsOK G)
include hG

theorem prc_one : PRc 1 G.one := by
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, hK⟩ := hG.consts
  obtain ⟨h1, h2⟩ := id_enc hK
  exact ⟨_, h1, h2, by rw [map_one, rowsMatrix_idRows]⟩

theorem prc_mul {g h : J} {a b : ℕ} (hg : PRc g a) (hh : PRc h b) :
    PRc (g * h) (mulJ G.c G.rm a b) := by
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, hK⟩ := hG.consts
  obtain ⟨X, hX, ha, hgX⟩ := hg
  obtain ⟨Y, hY, hb, hhY⟩ := hh
  obtain ⟨h1, h2⟩ := mul_enc hK ⟨hX, ha⟩ ⟨hY, hb⟩
  exact ⟨_, h1, h2, by rw [map_mul, hgX, hhY, rowsMatrix_mulRows]⟩

omit hG in
theorem prc_eq {g h : J} {a : ℕ} (hg : PRc g a) (hh : PRc h a) : g = h := by
  obtain ⟨X, hX, ha, hgX⟩ := hg
  obtain ⟨Y, hY, hb, hhY⟩ := hh
  have e : eqRows X Y = true := by
    rw [eqRows_of ⟨hX, ha⟩ ⟨hY, hb⟩]
    exact Nat.beq_refl a
  apply Mx_injective
  rw [hgX, hhY, eqRows_iff.1 e]

omit hG in
theorem prc_beq {g h : J} {a b : ℕ} (hg : PRc g a) (hh : PRc h b) (e : Nat.beq a b = true) :
    g = h := by
  rw [Nat.eq_of_beq_eq_true e] at hg
  exact prc_eq hg hh

theorem inv_of_canon {g : J} {a n : ℕ} (hg : PRc g a) (hn : canonJ G.pad n = true)
    (h : Nat.beq (mulJ G.c G.rm a n) G.one = true) : PRc g⁻¹ n := by
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, hK⟩ := hG.consts
  obtain ⟨X, hX, ha, hgX⟩ := hg
  subst ha
  obtain ⟨hY, hYn⟩ := invRows_enc hK hX hn h
  refine ⟨_, hY, hYn, ?_⟩
  obtain ⟨hm1, hm2⟩ := mul_enc hK ⟨hX, rfl⟩ ⟨hY, hYn⟩
  obtain ⟨hi1, hi2⟩ := id_enc hK
  have e : eqRows (mulRows X (invRows X)) (idRows ()) = true := by
    rw [eqRows_of ⟨hm1, hm2⟩ ⟨hi1, hi2⟩]
    exact h
  have h1 := congrArg rowsMatrix (eqRows_iff.1 e)
  rw [rowsMatrix_mulRows, rowsMatrix_idRows, ← hgX] at h1
  calc Mx g⁻¹ = Mx g⁻¹ * (Mx g * rowsMatrix (invRows X)) := by rw [h1, Matrix.mul_one]
    _ = rowsMatrix (invRows X) := by
      rw [← Matrix.mul_assoc, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mul]

omit hG in
theorem etaFrom_cons (c rm M : Nat) (L : List Nat) (m j acc : Nat) :
    etaFrom c rm (M :: L) m j acc = Bool.rec (motive := fun _ => Nat) (etaFrom c rm L m (j + 1) acc)
      (strictN (mulJ c rm acc M) (etaFrom c rm L m (j + 1)))
      (Nat.blt (nat_lit 0) (Nat.land m (Nat.shiftLeft (nat_lit 1) j))) := rfl

omit hG in
theorem blt_bit (m j : Nat) :
    Nat.blt (nat_lit 0) (Nat.land m (Nat.shiftLeft (nat_lit 1) j)) = m.testBit j := by
  change Nat.blt 0 (m &&& 1 <<< j) = _
  have e : m &&& 1 <<< j = if m.testBit j then 2 ^ j else 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases e : j = i
    · subst e
      cases h : m.testBit j <;> simp [Nat.testBit_two_pow_self]
    · cases h : m.testBit j <;> simp [e, Nat.testBit_two_pow_of_ne e]
  rw [e]
  cases m.testBit j
  · rfl
  · simp only [↓reduceIte]
    exact Nat.blt_eq.mpr (Nat.two_pow_pos j)

theorem etaFrom_spec (u : ℕ → J) (m : ℕ) :
    ∀ (Ts : List Nat) (j acc : Nat), (∀ i < Ts.length, PRc (u (j + i)) (Ts.getD i G.one)) →
      PRc (eta u j m) acc → PRc (eta u (j + Ts.length) m) (etaFrom G.c G.rm Ts m j acc)
  | [], j, acc, _, h => h
  | M :: L, j, acc, hT, h => by
    have h0 := hT 0 (by simp)
    rw [Nat.add_zero] at h0
    have hT' : ∀ i < L.length, PRc (u (j + 1 + i)) (L.getD i G.one) := by
      intro i hi
      have := hT (i + 1) (by simp; omega)
      rw [show j + (i + 1) = j + 1 + i by omega] at this
      exact this
    rw [etaFrom_cons, blt_bit, List.length_cons, show j + (L.length + 1) = j + 1 + L.length by omega]
    by_cases hb : m.testBit j
    · simp only [hb]
      rw [strictN_eq]
      refine etaFrom_spec u m L (j + 1) _ hT' ?_
      rw [eta_succ, if_pos hb]
      exact prc_mul hG h h0
    · simp only [hb]
      refine etaFrom_spec u m L (j + 1) _ hT' ?_
      rw [eta_succ, if_neg hb, mul_one]
      exact h

theorem etaK_spec (c : ℕ) : PRc (eta uJ 11 c) (etaK G.c G.rm G.one G.us c) := by
  have h := etaFrom_spec hG uJ c G.us 0 G.one (fun i hi => by
    rw [Nat.zero_add, ← getN_eq_getD]
    exact hG.us i (by rw [← hG.us_len]; exact hi)) (by rw [eta]; exact prc_one hG)
  rw [Nat.zero_add, hG.us_len] at h
  exact h

theorem kelJ_foldl : ∀ (l : List ℕ) (g : J) (acc : ℕ), PRc g acc →
    PRc (g * (l.map kJ).prod)
      (l.foldl (fun a i => strictN a fun a' => mulJ G.c G.rm a' (getN G.one G.ks i)) acc)
  | [], g, acc, h => by rw [List.map_nil, List.prod_nil, mul_one]; exact h
  | i :: l, g, acc, h => by
    rw [List.foldl_cons, strictN_eq, List.map_cons, List.prod_cons, ← mul_assoc]
    exact kelJ_foldl l _ _ (prc_mul hG h (hG.ks i))

theorem kelJ_spec (e : ℕ) : PRc (Kel e) (kelJ G e) := by
  have h := kelJ_foldl hG (pcSeqT e) 1 G.one (prc_one hG)
  rw [one_mul] at h
  exact h

theorem eltJ_spec (ce : ℕ × ℕ) : PRc (burnsideJ4NP_treeElt ce) (eltJ G ce) := by
  unfold eltJ
  rw [strictN_eq, strictN_eq]
  exact prc_mul hG (etaK_spec hG ce.1) (kelJ_spec hG ce.2)

end Model

theorem dbl_step {α : Type*} (R : J → α → Prop) (op : α → α → α)
    (hop : ∀ {g h : J} {x y : α}, R g x → R h y → R (g * h) (op x y)) (u : ℕ → J) {k : ℕ}
    {Cs : List α} {d b : α} (hlen : Cs.length = 2 ^ k)
    (hC : ∀ m < 2 ^ k, R (eta u k m) (Cs.getD m d)) (hb : R (u k) b) :
    (Cs ++ Cs.map fun x => op x b).length = 2 ^ (k + 1) ∧
      ∀ m < 2 ^ (k + 1), R (eta u (k + 1) m) ((Cs ++ Cs.map fun x => op x b).getD m d) := by
  refine ⟨by rw [List.length_append, List.length_map, hlen, pow_succ]; ring, fun m hm => ?_⟩
  rw [eta_succ]
  by_cases hmk : m < 2 ^ k
  · have hbit : m.testBit k = false := Nat.testBit_lt_two_pow hmk
    rw [if_neg (by rw [hbit]; exact Bool.false_ne_true), mul_one, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [hlen]; exact hmk), ← List.getD_eq_getElem?_getD]
    exact hC m hmk
  · have hm2 : m < 2 * 2 ^ k := by rw [← pow_succ']; exact hm
    have hbit : m.testBit k = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]
      have : m / 2 ^ k = 1 := by
        apply Nat.div_eq_of_lt_le <;> omega
      rw [this]
    rw [if_pos hbit, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [hlen]; omega), List.getElem?_map, hlen]
    have hlt : m - 2 ^ k < Cs.length := by rw [hlen]; omega
    rw [List.getElem?_eq_getElem hlt, Option.map_some, Option.getD_some]
    have he : eta u k m = eta u k (m - 2 ^ k) := by
      apply burnsideJ4NP_col_eta_congr
      intro j hj
      have e : m - 2 ^ k = m % 2 ^ k := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [e, Nat.testBit_mod_two_pow]
      simp [hj]
    rw [he]
    refine hop ?_ hb
    have := hC (m - 2 ^ k) (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some] at this
    exact this

theorem dbl_spec {α : Type*} (R : J → α → Prop) (op : α → α → α)
    (hop : ∀ {g h : J} {x y : α}, R g x → R h y → R (g * h) (op x y)) (u : ℕ → J) (d : α) :
    ∀ (l : List α) (k : ℕ) (Cs : List α), Cs.length = 2 ^ k →
      (∀ m < 2 ^ k, R (eta u k m) (Cs.getD m d)) → (∀ i < l.length, R (u (k + i)) (l.getD i d)) →
      (l.foldl (fun Cs b => Cs ++ Cs.map fun x => op x b) Cs).length = 2 ^ (k + l.length) ∧
        ∀ m < 2 ^ (k + l.length),
          R (eta u (k + l.length) m) ((l.foldl (fun Cs b => Cs ++ Cs.map fun x => op x b) Cs).getD m d)
  | [], k, Cs, hlen, hC, _ => ⟨hlen, hC⟩
  | b :: l, k, Cs, hlen, hC, hl => by
    have hb := hl 0 (by simp)
    rw [Nat.add_zero, List.getD_cons_zero] at hb
    obtain ⟨h1, h2⟩ := dbl_step R op hop u hlen hC hb
    have hl' : ∀ i < l.length, R (u (k + 1 + i)) (l.getD i d) := by
      intro i hi
      have := hl (i + 1) (by simp; omega)
      rw [show k + (i + 1) = k + 1 + i by omega, List.getD_cons_succ] at this
      exact this
    rw [List.foldl_cons, List.length_cons, show k + (l.length + 1) = k + 1 + l.length by omega]
    exact dbl_spec R op hop u d l (k + 1) _ h1 h2 hl'

@[expose] noncomputable def bvOf (wv : List (ℕ × ℕ)) (i : ℕ) : J :=
  burnsideJ4NP_treeElt (wv.getD i (0, 0))

theorem matsOf_spec {G : Mats} (hG : MatsOK G) (wv : List (ℕ × ℕ)) :
    (matsOf G wv).length = 2 ^ wv.length ∧
      ∀ m < 2 ^ wv.length, PRc (eta (bvOf wv) wv.length m) ((matsOf G wv).getD m G.one) := by
  have e : matsOf G wv = (wv.map (eltJ G)).foldl
      (fun Ms b => Ms ++ Ms.map fun x => mulJ G.c G.rm x b) [G.one] := by
    unfold matsOf
    rw [List.foldl_map]
    congr 1
    funext Ms ce
    rw [strictL_eq, smapK_eq]
  have h := dbl_spec PRc (mulJ G.c G.rm) (fun hg hh => prc_mul hG hg hh) (bvOf wv) G.one
    (wv.map (eltJ G)) 0 [G.one] rfl (fun m hm => by
      rw [pow_zero] at hm
      obtain rfl : m = 0 := by omega
      rw [eta_zero]
      exact prc_one hG) (fun i hi => by
      rw [List.length_map] at hi
      rw [Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some, bvOf,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact eltJ_spec hG _)
  rw [Nat.zero_add, List.length_map] at h
  rw [e]
  exact h

theorem encR_lt {X : Array V2} (hX : WfA X) : encR X < 1 <<< 14336 := by
  rw [Nat.one_shiftLeft]
  apply Nat.lt_pow_two_of_testBit
  intro p hp
  rw [encR_bit]
  have : ¬ p / 128 < 112 := by omega
  simp [this]

theorem char2_pair (x y : Matrix (Fin 112) (Fin 112) (ZMod 2)) :
    x * y + x + y + 1 = (x - 1) * (y - 1) := by
  have h2 : (1 : Matrix (Fin 112) (Fin 112) (ZMod 2)) + 1 = 0 := by
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have hs : ∀ a : Matrix (Fin 112) (Fin 112) (ZMod 2), a - 1 = a + 1 := by
    intro a
    rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left h2]
  rw [hs, hs]
  noncomm_ring

theorem pairP_label {G : Mats} (hG : MatsOK G) {wv : List (ℕ × ℕ)}
    (hE : Elem (bvOf wv) wv.length) {a b q : ℕ}
    (ha : a < 2 ^ wv.length) (hb : b < 2 ^ wv.length)
    (h : q + gRank G (pairP G (packMs (matsOf G wv)) a b) = 112) :
    q = burnsideJ4NP_colPair (eta (bvOf wv) wv.length a) (eta (bvOf wv) wv.length b) := by
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, hK⟩ := hG.consts
  obtain ⟨hc, hrm⟩ := consts_c hK
  obtain ⟨hlen, hMs⟩ := matsOf_spec hG wv
  have hab : a ^^^ b < 2 ^ wv.length := Nat.xor_lt_two_pow ha hb
  have hbound : ∀ x ∈ matsOf G wv, x < 1 <<< 14336 := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hx
    have := hMs m (by rw [← hlen]; exact hm)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some] at this
    obtain ⟨X, hX, hXe, -⟩ := this
    rw [← hXe]
    exact encR_lt hX
  have hget : ∀ m < 2 ^ wv.length, getP (packMs (matsOf G wv)) m = (matsOf G wv).getD m G.one := by
    intro m hm
    rw [getP_packMs hbound, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [hlen]; exact hm), Option.getD_some, Option.getD_some]
  obtain ⟨X1, hX1, e1, m1⟩ := hMs _ hab
  obtain ⟨X2, hX2, e2, m2⟩ := hMs _ ha
  obtain ⟨X3, hX3, e3, m3⟩ := hMs _ hb
  obtain ⟨hI, eI⟩ := id_enc hK
  obtain ⟨hA, eA⟩ := enc_addRows hX1 hX2
  obtain ⟨hB, eB⟩ := enc_addRows hA hX3
  obtain ⟨hC, eC⟩ := enc_addRows hB hI
  have hP : pairP G (packMs (matsOf G wv)) a b =
      encR (addRows (addRows (addRows X1 X2) X3) (idRows ())) := by
    unfold pairP
    rw [show Nat.xor a b = a ^^^ b from rfl, hget _ hab, hget _ ha, hget _ hb, eC, eB, eA, e1, e2, e3, eI]
  rw [hP, gRank_spec hc hrm hC, rowsMatrix_addRows, rowsMatrix_addRows, rowsMatrix_addRows,
    rowsMatrix_idRows, ← m1, ← m2, ← m3, eta_xor hE le_rfl, map_mul, char2_pair] at h
  have h2 := fixDim_add_rank ((Mx (eta (bvOf wv) wv.length a) - 1) *
    (Mx (eta (bvOf wv) wv.length b) - 1))
  unfold burnsideJ4NP_colPair
  omega

end CFSG.KC.J4TreeCol

end
