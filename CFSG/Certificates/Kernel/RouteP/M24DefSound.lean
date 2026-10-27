module

public import CFSG.Certificates.Kernel.RouteP.M24DefMath

public section

namespace CFSG.KC.M24Def

open Certificates.RouteP.M24Defect CFSG.Quasithin.H.Mathieu CFSG.Monster.Code
  CFSG.Sporadic.Bridge CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

theorem ln_eq (w P j : Nat) : ln w P j = P / 2 ^ (w * j) % 2 ^ w := by
  change (P >>> (w * j)) &&& ((1 <<< w) - 1) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem lettersTabOK_spec {LI LD LM : Nat → Nat} (h : lettersTabOK LI LD LM = true) :
    ∀ c < 4, (∀ k < 24, ln 5 (LI c) k = (letArr (c / 2) (c % 2 != 0))[k]!) ∧
      (∀ j < 11, ln 11 (LD c) j = dualAct (matA (letArr (c / 2) (c % 2 == 0))) (2 ^ j)) ∧
      (∀ j < 11, ln 11 (LM c) j = act11 (letArr (c / 2) (c % 2 == 0)) (2 ^ j)) := by
  unfold lettersTabOK at h
  rw [List.all_eq_true] at h
  intro c hc
  have h1 := h c (List.mem_range.2 hc)
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h1
  exact ⟨h1.1.1, h1.1.2, h1.2⟩

theorem wordA_size : ∀ w : List (ℕ × Bool), (wordA w).size = 24
  | [] => by simp [wordA, idA]
  | _ :: _ => by simp [wordA, compA]

theorem wordA_lt {w : List (ℕ × Bool)} (hw : ∀ l ∈ w, l.1 < 2) {k : ℕ} (hk : k < 24) :
    (wordA w)[k]! < 24 := by
  have h : (((wordProd gens w : ↥AutPerm) : Equiv.Perm (Fin 24)) ⟨k, hk⟩ : ℕ) = (wordA w)[k]! :=
    hasArr_wordProd w hw ⟨k, hk⟩
  rw [← h]
  exact Fin.isLt _

theorem decR_length (W : Nat) : (decR W).length = ln 6 W 0 := by
  simp [decR, ln_eq]

theorem decR_getElem (W : Nat) {k : Nat} (hk : k < (decR W).length) :
    (decR W)[k] = (ln 6 W (k + 1) / 2, ln 6 W (k + 1) % 2 == 0) := by
  simp [decR, ln_eq]

theorem letArr_xor_one {c : Nat} (hc : c < 4) :
    letArr (Nat.xor c 1 / 2) (Nat.xor c 1 % 2 != 0) = letArr (c / 2) (c % 2 == 0) := by
  interval_cases c <;> rfl

theorem relPt_eq {LI : Nat → Nat}
    (hLI : ∀ c < 4, ∀ k < 24, ln 5 (LI c) k = (letArr (c / 2) (c % 2 != 0))[k]!)
    (W : Nat) (hw : ∀ l ∈ decR W, l.1 < 2) (k : Nat) (hk : k < 24) :
    relPt LI W k = (wordA (decR W))[k]! := by
  have hlen := decR_length W
  have key : ∀ j ≤ ln 6 W 0, Nat.rec (motive := fun _ => Nat) k
      (fun j acc => ln 5 (LI (Nat.xor (ln 6 W (Nat.sub (ln 6 W 0) j)) 1)) acc) j =
      (wordA ((decR W).drop (ln 6 W 0 - j)))[k]! := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [Nat.sub_zero, ← hlen, List.drop_length, wordA, idA_getElem_bang hk]
      rfl
    | succ j ih =>
      intro hj
      have hjl : ln 6 W 0 - (j + 1) < (decR W).length := by omega
      have hd : (decR W).drop (ln 6 W 0 - (j + 1)) =
          (decR W)[ln 6 W 0 - (j + 1)] :: (decR W).drop (ln 6 W 0 - j) := by
        rw [List.drop_eq_getElem_cons hjl]
        congr 2
        omega
      have hidx : ln 6 W 0 - (j + 1) + 1 = Nat.sub (ln 6 W 0) j := by
        change _ = ln 6 W 0 - j
        omega
      have hget := decR_getElem W hjl
      rw [hidx] at hget
      have hmem : (decR W)[ln 6 W 0 - (j + 1)] ∈ decR W := List.getElem_mem hjl
      have hc2 := hw _ hmem
      rw [hget] at hc2
      have hc : ln 6 W (Nat.sub (ln 6 W 0) j) < 4 := by
        simp only at hc2
        omega
      have hrest : ∀ l ∈ (decR W).drop (ln 6 W 0 - j), l.1 < 2 :=
        fun l hl => hw l (List.mem_of_mem_drop hl)
      rw [Nat.rec_add_one, ih (by omega), hd, wordA, compA_getElem_bang _ _ hk, hget,
        hLI _ (by
          have := Nat.xor_lt_two_pow (n := 2) hc (by norm_num : 1 < 2 ^ 2)
          simpa using this) _ (wordA_lt hrest hk), letArr_xor_one hc]
  rw [relPt, key _ le_rfl, Nat.sub_self, List.drop_zero]

@[expose] def keyTab (L : List (Nat × Nat)) : Nat :=
  L.foldl (fun A c => A ^^^ (c.2 <<< (11 * c.1))) 0

theorem allLt_eq_true {n : Nat} {f : Nat → Bool} : allLt n f = true ↔ ∀ j < n, f j = true := by
  induction n with
  | zero => simp [allLt]
  | succ n ih =>
    change (Bool.rec false (allLt n f) (f n) : Bool) = true ↔ _
    cases hf : f n
    · simp only [Bool.false_eq_true, false_iff, not_forall]
      exact ⟨n, Nat.lt_succ_self n, by simp [hf]⟩
    · simp only
      rw [ih]
      constructor
      · intro h j hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact h j hj
        · exact hf
      · intro h j hj
        exact h j (Nat.lt_succ_of_lt hj)

theorem tword_tabOf_letters (TW : Nat → Nat) (p : Nat) : ∀ l ∈ tword (tabOf TW) p, l.1 < 2 := by
  intro l hl
  by_cases hp : p < 576
  · have h : tword (tabOf TW) p = decW (TW p) := by simp [tword, tabOf, hp]
    rw [h] at hl
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hl
    exact Nat.mod_lt _ (by norm_num)
  · have h : tword (tabOf TW) p = [] := by
      simp [tword, tabOf, hp]
      rfl
    rw [h] at hl
    exact absurd hl List.not_mem_nil

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem brec_eq (e t c : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = (bif c then t else e) := by
  cases c <;> rfl

theorem bif_false (a b : Bool) : (bif a then b else false) = (a && b) := by cases a <;> rfl

theorem bif_not (a : Bool) : (bif a then false else true) = !a := by cases a <;> rfl

theorem land31 (a : Nat) : a &&& 31 = a % 32 := Nat.and_two_pow_sub_one_eq_mod a 5

theorem wordAInv_size : ∀ w : List (ℕ × Bool), (wordAInv w).size = 24
  | [] => by simp [wordAInv, idA]
  | _ :: _ => by simp [wordAInv, compA]

theorem compA_size (a b : Array ℕ) : (compA a b).size = 24 := by simp [compA]

theorem arr_eq_of_hasArr {σ : Equiv.Perm (Fin 24)} {a b : Array ℕ} (ha : HasArr σ a)
    (hb : HasArr σ b) (hsa : a.size = 24) (hsb : b.size = 24) : a = b := by
  refine Array.ext (by rw [hsa, hsb]) fun i h1 h2 => ?_
  have e := (ha ⟨i, hsa ▸ h1⟩).symm.trans (hb ⟨i, hsa ▸ h1⟩)
  rwa [getElem!_pos a i h1, getElem!_pos b i h2] at e

theorem wordProd_snoc (w : List (ℕ × Bool)) (y : ℕ × Bool) :
    wordProd gens (w ++ [y]) = wordProd gens w * letterVal gens y := by
  induction w with
  | nil => rw [List.nil_append, wordProd_cons, wordProd_nil, mul_one, one_mul]
  | cons l w ih => rw [List.cons_append, wordProd_cons, wordProd_cons, ih, mul_assoc]

theorem wordAInv_snoc {w : List (ℕ × Bool)} (hw : ∀ l ∈ w, l.1 < 2) {y : ℕ × Bool} (hy : y.1 < 2) :
    wordAInv (w ++ [y]) = compA (letArr y.1 (!y.2)) (wordAInv w) := by
  have hW : ∀ l ∈ w ++ [y], l.1 < 2 := by
    intro l hl
    rcases List.mem_append.1 hl with hl | hl
    · exact hw l hl
    · rw [List.mem_singleton.1 hl]
      exact hy
  refine arr_eq_of_hasArr (hasArr_wordProd_inv _ hW) ?_ (wordAInv_size _) (compA_size _ _)
  rw [wordProd_snoc, Subgroup.coe_mul, mul_inv_rev]
  exact HasArr.mul (hasArr_letterVal_inv y hy) (hasArr_wordProd_inv w hw)

theorem wordA_snoc {w : List (ℕ × Bool)} (hw : ∀ l ∈ w, l.1 < 2) {y : ℕ × Bool} (hy : y.1 < 2) :
    wordA (w ++ [y]) = compA (wordA w) (letArr y.1 y.2) := by
  have hW : ∀ l ∈ w ++ [y], l.1 < 2 := by
    intro l hl
    rcases List.mem_append.1 hl with hl | hl
    · exact hw l hl
    · rw [List.mem_singleton.1 hl]
      exact hy
  refine arr_eq_of_hasArr (hasArr_wordProd _ hW) ?_ (wordA_size _) (compA_size _ _)
  rw [wordProd_snoc, Subgroup.coe_mul]
  exact HasArr.mul (hasArr_wordProd w hw) (hasArr_letterVal y hy)

theorem act11_idA {w : ℕ} (hw : w < 2 ^ 11) : act11 idA w = w := by
  have h := rho11_toW AutPerm le_rfl 1 (a := idA) (by rw [Subgroup.coe_one]; exact hasArr_one) w
  rw [map_one, MulAut.one_apply] at h
  exact toW_inj (act11_lt _ _) hw h.symm

theorem dualAct_matA_idA {m : ℕ} (hm : m < 2 ^ 11) : dualAct (matA idA) m = m :=
  eq_of_bp (by simpa [length_matA] using dualAct_lt (matA idA) m) hm fun w hw => by
    rw [bp_dualAct (length_matA _), actM_matA _ hw, act11_idA hw]

theorem tword_tabOf (TW : Nat → Nat) {q : Nat} (hq : q < 576) :
    tword (tabOf TW) q = decW (TW q) := by
  simp [tword, tabOf, hq]

theorem decW_snoc (t tp : Nat) (h1 : t % 32 = tp % 32 + 1)
    (h2 : ∀ k < tp % 32, t / 32 / 2 ^ k % 2 = tp / 32 / 2 ^ k % 2) :
    decW t = decW tp ++ [(t / 32 / 2 ^ (tp % 32) % 2, true)] := by
  unfold decW
  rw [h1, List.range_succ, List.map_append, List.map_singleton]
  congr 1
  exact List.map_congr_left fun k hk => by rw [h2 k (List.mem_range.1 hk)]

theorem bits_low (a X n k : Nat) (hk : k < n) : (a + X * 2 ^ n) / 2 ^ k % 2 = a / 2 ^ k % 2 := by
  obtain ⟨d, rfl⟩ : ∃ d, n = k + 1 + d := ⟨n - k - 1, by omega⟩
  have e : X * 2 ^ (k + 1 + d) = 2 ^ k * (2 * (X * 2 ^ d)) := by ring
  rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.add_mul_mod_self_left]

theorem lanes_of {D : Nat} {f : Nat → Nat} (h : lanesIs D f = true) : ∀ j < 11, ln 11 D j = f j :=
  fun j hj => Nat.eq_of_beq_eq_true (allLt_eq_true.1 h j hj)

theorem tree_aux (TW PA GQ FP LD LI LM : Nat → Nat) (hlet : lettersTabOK LI LD LM = true)
    (htree : ∀ q < 576, treeQ TW PA GQ FP LD LI q = true) (n : Nat) :
    ∀ q, TW q % 32 = n → q < 576 → q / 24 ≠ q % 24 →
      (wordAInv (tword (tabOf TW) q))[0]! = q / 24 ∧ (wordAInv (tword (tabOf TW) q))[1]! = q % 24 ∧
      ∀ j < 11, ln 11 (GQ q) j = dualAct (matA (wordAInv (tword (tabOf TW) q))) (2 ^ j) ∧
        ln 11 (FP q) j = dualAct (matA (wordA (tword (tabOf TW) q))) (2 ^ j) := by
  have hl := lettersTabOK_spec hlet
  have hcol : ∀ (a : Array ℕ) (j : ℕ), dualAct (matA a) (2 ^ j) < 2 ^ 11 := fun a j => by
    simpa [length_matA] using dualAct_lt (matA a) (2 ^ j)
  induction n with
  | zero =>
    intro q hn hq huv
    have h := htree q hq
    simp only [treeQ, strictB_eq, brec_eq] at h
    have hb1 : Nat.beq (q.div 24) (q.mod 24) = false := by
      cases e : Nat.beq (q.div 24) (q.mod 24)
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) huv
    have hb2 : Nat.beq ((TW q).land 31) 0 = true := by
      have e : (TW q).land 31 = TW q % 32 := land31 _
      rw [e, hn]
      rfl
    rw [hb1, cond_false, hb2, cond_true] at h
    simp only [bif_false, Bool.and_eq_true] at h
    obtain ⟨h1, hG, hF⟩ := h
    have hq1 : q = 1 := Nat.eq_of_beq_eq_true h1
    have hw : tword (tabOf TW) q = [] := by
      rw [tword_tabOf TW hq]
      unfold decW
      rw [hn]
      rfl
    rw [hw, hq1]
    simp only [wordAInv, wordA]
    refine ⟨by rw [idA_getElem_bang (by norm_num)], by rw [idA_getElem_bang (by norm_num)],
      fun j hj => ?_⟩
    rw [dualAct_matA_idA (Nat.pow_lt_pow_right (by norm_num) hj), ← hq1]
    refine ⟨?_, ?_⟩
    · rw [lanes_of hG j hj]
      exact Nat.one_shiftLeft j
    · rw [lanes_of hF j hj]
      exact Nat.one_shiftLeft j
  | succ n ih =>
    intro q hn hq huv
    have h := htree q hq
    simp only [treeQ, strictB_eq, brec_eq] at h
    have hb1 : Nat.beq (q.div 24) (q.mod 24) = false := by
      cases e : Nat.beq (q.div 24) (q.mod 24)
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) huv
    have hb2 : Nat.beq ((TW q).land 31) 0 = false := by
      have e : (TW q).land 31 = TW q % 32 := land31 _
      rw [e, hn]
      rfl
    rw [hb1, cond_false, hb2, cond_false] at h
    simp only [bif_false, bif_not, Bool.and_eq_true] at h
    obtain ⟨hp, hpd, heq, hu, hv, hF, hG⟩ := h
    have hx : ((TW q).shiftRight (((TW (PA q)).land 31).add 5)).land 1 =
        TW q / 32 / 2 ^ (TW (PA q) % 32) % 2 := by
      change (TW q >>> ((TW (PA q) &&& 31) + 5)) &&& 1 = _
      rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, land31, pow_add, mul_comm,
        ← Nat.div_div_eq_div_mul]
      rfl
    rw [hx] at heq hu hv hF hG
    generalize hxd : TW q / 32 / 2 ^ (TW (PA q) % 32) % 2 = x at heq hu hv hF hG
    have hx2 : x < 2 := hxd ▸ Nat.mod_lt _ (by norm_num)
    have hp' : PA q < 576 := by simpa using hp
    have hpd' : PA q / 24 ≠ PA q % 24 := by
      intro e
      have e' : Nat.beq ((PA q).div 24) ((PA q).mod 24) = true := Nat.beq_eq_true_eq _ _ ▸ e
      rw [e'] at hpd
      exact absurd hpd (by decide)
    have heq' := Nat.eq_of_beq_eq_true heq
    change TW q = TW (PA q) + 1 + x <<< ((TW (PA q) &&& 31) + 5) at heq'
    rw [Nat.shiftLeft_eq, land31, pow_add] at heq'
    have e1 : TW q = TW (PA q) + 1 + 32 * (x * 2 ^ (TW (PA q) % 32)) := by
      rw [heq']
      ring
    have hn' : TW (PA q) % 32 = n := by omega
    have hdiv : TW q / 32 = TW (PA q) / 32 + x * 2 ^ (TW (PA q) % 32) := by omega
    have hd : decW (TW q) = decW (TW (PA q)) ++ [(x, true)] := by
      rw [← hxd]
      exact decW_snoc _ _ (by omega) fun k hk => by rw [hdiv, bits_low _ _ _ _ hk]
    have hw : ∀ l ∈ decW (TW (PA q)), l.1 < 2 := by
      rw [← tword_tabOf TW hp']
      exact tword_tabOf_letters TW _
    obtain ⟨i0, i1, icol⟩ := ih (PA q) hn' hp' hpd'
    rw [tword_tabOf TW hp'] at i0 i1 icol
    rw [tword_tabOf TW hq, hd, wordAInv_snoc hw (y := (x, true)) hx2,
      wordA_snoc hw (y := (x, true)) hx2]
    have e2 : 2 * x / 2 = x := by omega
    have e3 : (2 * x + 1) / 2 = x := by omega
    have e4 : (2 * x % 2 != 0) = false := by simp
    have e5 : (2 * x % 2 == 0) = true := by simp
    have e6 : ((2 * x + 1) % 2 == 0) = false := by simp [Nat.add_mod]
    have hLI := (hl (2 * x) (by omega)).1
    have hLD := (hl (2 * x) (by omega)).2.1
    have hLD' := (hl (2 * x + 1) (by omega)).2.1
    rw [e2, e4] at hLI
    rw [e2, e5] at hLD
    rw [e3, e6] at hLD'
    have hu' := Nat.eq_of_beq_eq_true hu
    have hv' := Nat.eq_of_beq_eq_true hv
    change ln 5 (LI (2 * x)) (PA q / 24) = q / 24 at hu'
    change ln 5 (LI (2 * x)) (PA q % 24) = q % 24 at hv'
    simp only [Bool.not_true]
    refine ⟨?_, ?_, fun j hj => ⟨?_, ?_⟩⟩
    · rw [compA_getElem_bang _ _ (by norm_num), i0, ← hu', hLI _ (by omega)]
    · rw [compA_getElem_bang _ _ (by norm_num), i1, ← hv', hLI _ (by omega)]
    · have hG' := lanes_of hG j hj
      change ln 11 (GQ q) j = dapp (GQ (PA q)) (ln 11 (LD (2 * x + 1)) j) at hG'
      rw [hG', hLD' j hj, dapp_eq_dualAct (fun j hj => (icol j hj).1) (hcol _ _),
        dualAct_matA_compA (a := letArr x false) (b := wordAInv (decW (TW (PA q))))
          (AutPerm.inv_mem (Subtype.prop _)) (AutPerm.inv_mem (Subtype.prop _))
          (hasArr_letterVal_inv (x, true) hx2) (hasArr_wordProd_inv _ hw)]
    · have hF' := lanes_of hF j hj
      change ln 11 (FP q) j = dapp (LD (2 * x)) (ln 11 (FP (PA q)) j) at hF'
      rw [hF', (icol j hj).2, dapp_eq_dualAct hLD (hcol _ _),
        dualAct_matA_compA (a := wordA (decW (TW (PA q)))) (b := letArr x true)
          (Subtype.prop _) (Subtype.prop _) (hasArr_wordProd _ hw) (hasArr_letterVal (x, true) hx2)]

theorem treeOK_of (TW PA GQ FP LD LI LM : Nat → Nat) (hlet : lettersTabOK LI LD LM = true)
    (htree : ∀ q < 576, treeQ TW PA GQ FP LD LI q = true) :
    treeOK (tabOf TW) = true ∧ treeLetters (tabOf TW) = true ∧
      ∀ q < 576, q / 24 ≠ q % 24 → ∀ j < 11,
        ln 11 (GQ q) j = dualAct (matA (wordAInv (tword (tabOf TW) q))) (2 ^ j) ∧
        ln 11 (FP q) j = dualAct (matA (wordA (tword (tabOf TW) q))) (2 ^ j) := by
  have aux := fun q => tree_aux TW PA GQ FP LD LI LM hlet htree _ q rfl
  refine ⟨?_, ?_, fun q hq huv j hj => (aux q hq huv).2.2 j hj⟩
  · unfold treeOK
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true]
    refine ⟨by simp [tabOf], fun u hu v hv => ?_⟩
    by_cases huv : u = v
    · exact Or.inl huv
    · right
      have e1 : (24 * u + v) / 24 = u := by omega
      have e2 : (24 * u + v) % 24 = v := by omega
      obtain ⟨h0, h1, -⟩ := aux (24 * u + v) (by omega) (by omega)
      rw [e1] at h0
      rw [e2] at h1
      exact ⟨h0, h1⟩
  · unfold treeLetters tabOf
    rw [List.all_toArray, List.all_eq_true]
    intro w hw
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hw
    rw [List.all_eq_true]
    intro l hl
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hl
    simp only [Bool.and_true, decide_eq_true_eq]
    exact Nat.mod_lt _ (by norm_num)

theorem relsOK_of (RW LI LD LM : Nat → Nat) (hlet : lettersTabOK LI LD LM = true)
    (hw : ((List.range 7).map fun i => decR (RW i)) = relWords)
    (hrel : ∀ i < 7, relQ LI (RW i) = true) : relsOK = true := by
  have hl := lettersTabOK_spec hlet
  unfold relsOK
  rw [List.all_eq_true]
  intro w hwm
  have hwm' := hwm
  rw [← hw] at hwm'
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hwm'
  have hi7 := List.mem_range.1 hi
  have hlet2 := relWords_letters _ hwm
  have hrel' := allLt_eq_true.1 (hrel i hi7)
  have hpt : ∀ k < 24, (wordA (decR (RW i)))[k]! = k := fun k hk => by
    rw [← relPt_eq (fun c hc => (hl c hc).1) _ hlet2 k hk]
    exact Nat.eq_of_beq_eq_true (hrel' k hk)
  rw [beq_iff_eq]
  refine Array.ext (by rw [wordA_size]; simp [idA]) fun k h1 h2 => ?_
  rw [wordA_size] at h1
  have := hpt k h1
  rw [getElem!_pos _ _ (by rw [wordA_size]; exact h1)] at this
  rw [this]
  simp [idA]

theorem foldl_keyTab_start : ∀ (L : List (Nat × Nat)) (A : Nat),
    L.foldl (fun A c => A ^^^ (c.2 <<< (11 * c.1))) A = A ^^^ keyTab L
  | [], A => by simp [keyTab]
  | c :: L, A => by
    simp only [List.foldl_cons, keyTab]
    rw [foldl_keyTab_start L, foldl_keyTab_start L (0 ^^^ _), Nat.zero_xor, Nat.xor_assoc]

theorem keyTab_append (L₁ L₂ : List (Nat × Nat)) : keyTab (L₁ ++ L₂) = keyTab L₁ ^^^ keyTab L₂ := by
  unfold keyTab
  rw [List.foldl_append]
  exact foldl_keyTab_start L₂ _

theorem comboContribs_append (tab : Array (List (ℕ × Bool))) (a b : List (Nat × Nat × Nat)) :
    comboContribs tab (a ++ b) = comboContribs tab a ++ comboContribs tab b := by
  simp [comboContribs, List.flatMap_append]

theorem strictN_eq (y : Nat) (k : Nat → Nat) : Loop.strictN y k = k y := by cases y <;> rfl

theorem r_land (a b : Nat) : Nat.land a b = a &&& b := rfl
theorem r_shr (a b : Nat) : Nat.shiftRight a b = a >>> b := rfl
theorem r_shl (a b : Nat) : Nat.shiftLeft a b = a <<< b := rfl
theorem r_add (a b : Nat) : Nat.add a b = a + b := rfl
theorem r_mul (a b : Nat) : Nat.mul a b = a * b := rfl
theorem r_sub (a b : Nat) : Nat.sub a b = a - b := rfl
theorem r_div (a b : Nat) : Nat.div a b = a / b := rfl
theorem r_mod (a b : Nat) : Nat.mod a b = a % b := rfl
theorem r_xor (a b : Nat) : Nat.xor a b = a ^^^ b := rfl

def lowOf (m : Nat) (st : HA) : Nat := st.bwd[0]! + 32 * st.bwd[1]! + 1024 * dualAct (matA st.fwd) m

def enc (m B : Nat) (st : HA) : Nat := B <<< 21 + lowOf m st

theorem HAOK.bwd_lt {st : HA} {h : ↥AutPerm} (hs : HAOK st h) {i : Nat} (hi : i < 24) :
    st.bwd[i]! < 24 := by
  have e : ((((h : Equiv.Perm (Fin 24))⁻¹ ⟨i, hi⟩ : Fin 24)) : ℕ) = st.bwd[i]! := hs.2 ⟨i, hi⟩
  rw [← e]
  exact Fin.isLt _

theorem HAOK.bwd_ne {st : HA} {h : ↥AutPerm} (hs : HAOK st h) : st.bwd[0]! ≠ st.bwd[1]! := by
  intro e
  have e0 : ((((h : Equiv.Perm (Fin 24))⁻¹ 0 : Fin 24)) : ℕ) = st.bwd[0]! := hs.2 0
  have e1 : ((((h : Equiv.Perm (Fin 24))⁻¹ 1 : Fin 24)) : ℕ) = st.bwd[1]! := hs.2 1
  have : ((h : Equiv.Perm (Fin 24))⁻¹ 0 : Fin 24) = (h : Equiv.Perm (Fin 24))⁻¹ 1 :=
    Fin.ext (by rw [e0, e1, e])
  exact absurd ((h : Equiv.Perm (Fin 24))⁻¹.injective this) (by decide)

theorem dualAct_matA_lt (a : Array ℕ) (m : ℕ) : dualAct (matA a) m < 2048 := by
  simpa [length_matA] using dualAct_lt (matA a) m

theorem lowOf_lt {st : HA} {h : ↥AutPerm} (hs : HAOK st h) (m : Nat) : lowOf m st < 2 ^ 21 := by
  have h0 := HAOK.bwd_lt hs (i := 0) (by norm_num)
  have h1 := HAOK.bwd_lt hs (i := 1) (by norm_num)
  have hc := dualAct_matA_lt st.fwd m
  unfold lowOf
  norm_num
  omega

theorem enc_low {st : HA} {h : ↥AutPerm} (hs : HAOK st h) (m B : Nat) :
    enc m B st &&& 2097151 = lowOf m st := by
  have e : enc m B st &&& 2097151 = enc m B st % 2 ^ 21 := Nat.and_two_pow_sub_one_eq_mod _ 21
  rw [e, enc, Nat.shiftLeft_eq, Nat.add_comm, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (lowOf_lt hs m)]

theorem enc_hi {st : HA} {h : ↥AutPerm} (hs : HAOK st h) (m B : Nat) : enc m B st >>> 21 = B := by
  rw [enc, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.add_comm,
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos 21), Nat.div_eq_of_lt (lowOf_lt hs m), Nat.zero_add]

theorem lowOf_u {st : HA} {h : ↥AutPerm} (hs : HAOK st h) (m : Nat) :
    lowOf m st &&& 31 = st.bwd[0]! := by
  have h0 := HAOK.bwd_lt hs (i := 0) (by norm_num)
  rw [land31, lowOf]
  omega

theorem lowOf_v {st : HA} {h : ↥AutPerm} (hs : HAOK st h) (m : Nat) :
    lowOf m st >>> 5 &&& 31 = st.bwd[1]! := by
  have h1 := HAOK.bwd_lt hs (i := 1) (by norm_num)
  have h0 := HAOK.bwd_lt hs (i := 0) (by norm_num)
  rw [land31, Nat.shiftRight_eq_div_pow, lowOf]
  norm_num
  omega

theorem lowOf_c {st : HA} {h : ↥AutPerm} (hs : HAOK st h) (m : Nat) :
    lowOf m st >>> 10 = dualAct (matA st.fwd) m := by
  have h1 := HAOK.bwd_lt hs (i := 1) (by norm_num)
  have h0 := HAOK.bwd_lt hs (i := 0) (by norm_num)
  rw [Nat.shiftRight_eq_div_pow, lowOf]
  norm_num
  omega

theorem xor_hi (B X low t : Nat) (hlow : low < 2 ^ 21) :
    (B <<< 21 + low) ^^^ (X <<< (21 + t)) = (B ^^^ (X <<< t)) <<< 21 + low := by
  have e1 : ∀ Y, Y <<< 21 + low = 2 ^ 21 * Y + low := fun Y => by rw [Nat.shiftLeft_eq, mul_comm]
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [e1, e1, Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ hlow,
    Nat.testBit_two_pow_mul_add _ hlow, Nat.testBit_shiftLeft, Nat.testBit_xor,
    Nat.testBit_shiftLeft]
  by_cases hi : i < 21
  · have : ¬ (i ≥ 21 + t) := by omega
    simp [hi, this]
  · have e2 : (i ≥ 21 + t) ↔ (i - 21 ≥ t) := by omega
    simp only [hi, if_false, Nat.sub_sub, e2]

def GQOK (tab : Array (List (ℕ × Bool))) (GQ : Nat → Nat) : Prop :=
  ∀ q < 576, q / 24 ≠ q % 24 → ∀ j < 11,
    ln 11 (GQ q) j = dualAct (matA (wordAInv (tword tab q))) (2 ^ j)

theorem emit_eq {tab : Array (List (ℕ × Bool))} (hL : ∀ p, ∀ l ∈ tword tab p, l.1 < 2)
    {GQ : Nat → Nat} (hGQ : GQOK tab GQ) {st : HA} {h : ↥AutPerm} (hs : HAOK st h) (x m B : Nat) :
    emit GQ x (enc m B st) =
      enc m (B ^^^ (dualAct (matA (kArr tab st)) m <<< (11 * keyOf st x))) st := by
  simp only [emit, strictN_eq, r_land, r_shr, r_shl, r_add, r_mul, r_xor]
  rw [enc_low hs, lowOf_u hs, lowOf_v hs, lowOf_c hs]
  have h0 := HAOK.bwd_lt hs (i := 0) (by norm_num)
  have h1 := HAOK.bwd_lt hs (i := 1) (by norm_num)
  have hne := HAOK.bwd_ne hs
  have hq : 24 * st.bwd[0]! + st.bwd[1]! < 576 := by omega
  have hq1 : (24 * st.bwd[0]! + st.bwd[1]!) / 24 ≠ (24 * st.bwd[0]! + st.bwd[1]!) % 24 := by omega
  have hc : dualAct (matA st.fwd) m < 2 ^ 11 := dualAct_matA_lt _ _
  rw [dapp_eq_dualAct (hGQ _ hq hq1) hc]
  have ek : dualAct (matA (kArr tab st)) m =
      dualAct (matA (wordAInv (tword tab (24 * st.bwd[0]! + st.bwd[1]!))))
        (dualAct (matA st.fwd) m) :=
    dualAct_matA_compA (Subtype.prop h) (AutPerm.inv_mem (Subtype.prop _)) hs.1
      (hasArr_wordProd_inv _ (hL _)) m
  rw [ek, enc, enc, xor_hi _ _ _ _ (lowOf_lt hs m)]
  rfl

def LetOK (LD LI : Nat → Nat) : Prop :=
  ∀ c < 4, (∀ k < 24, ln 5 (LI c) k = (letArr (c / 2) (c % 2 != 0))[k]!) ∧
    (∀ j < 11, ln 11 (LD c) j = dualAct (matA (letArr (c / 2) (c % 2 == 0))) (2 ^ j))

theorem move_eq {LD LI : Nat → Nat} (hl : LetOK LD LI) {st : HA} {h : ↥AutPerm} (hs : HAOK st h)
    {c : Nat} (hc : c < 4) (m B : Nat) :
    move LD LI c (enc m B st) = enc m B (st.step (c / 2) (c % 2 == 0)) := by
  simp only [move, strictN_eq, r_land, r_shr, r_shl, r_add, r_mul, r_sub]
  rw [enc_low hs, lowOf_u hs, lowOf_v hs, lowOf_c hs, (hl c hc).1 _ (HAOK.bwd_lt hs (by norm_num)),
    (hl c hc).1 _ (HAOK.bwd_lt hs (by norm_num)),
    dapp_eq_dualAct (hl c hc).2 (by simpa using dualAct_matA_lt st.fwd m)]
  have hc2 : c / 2 < 2 := by omega
  have ef : dualAct (matA (st.step (c / 2) (c % 2 == 0)).fwd) m =
      dualAct (matA (letArr (c / 2) (c % 2 == 0))) (dualAct (matA st.fwd) m) :=
    dualAct_matA_compA (Subtype.prop h) (Subtype.prop _) hs.1
      (hasArr_letterVal (c / 2, c % 2 == 0) hc2) m
  have e0 : (st.step (c / 2) (c % 2 == 0)).bwd[0]! = (letArr (c / 2) (c % 2 != 0))[st.bwd[0]!]! :=
    compA_getElem_bang _ _ (by norm_num)
  have e1 : (st.step (c / 2) (c % 2 == 0)).bwd[1]! = (letArr (c / 2) (c % 2 != 0))[st.bwd[1]!]! :=
    compA_getElem_bang _ _ (by norm_num)
  rw [enc, enc, lowOf, lowOf, ef, e0, e1]
  have := Nat.sub_add_cancel (Nat.le_add_left (lowOf m st) (B <<< 21))
  unfold lowOf at this
  omega

theorem HAOK.step' {st : HA} {h : ↥AutPerm} (hs : HAOK st h) {c : Nat} (hc : c < 4) :
    HAOK (st.step (c / 2) (c % 2 == 0)) (h * letterVal gens (c / 2, c % 2 == 0)) :=
  hs.step (c / 2, c % 2 == 0) (by simp only; omega)

def contribOf (tab : Array (List (ℕ × Bool))) (m : Nat) (e : HA × Nat) : Nat × Nat :=
  (keyOf e.1 e.2, dualAct (matA (kArr tab e.1)) m)

theorem walk_codes {tab : Array (List (ℕ × Bool))} (hL : ∀ p, ∀ l ∈ tword tab p, l.1 < 2)
    {LD LI GQ : Nat → Nat} (hl : LetOK LD LI) (hGQ : GQOK tab GQ) (m : Nat) :
    ∀ (codes : List Nat) (st : HA) (h : ↥AutPerm) (B : Nat), HAOK st h → (∀ c ∈ codes, c < 4) →
      ∃ st' : HA, ∃ h' : ↥AutPerm, HAOK st' h' ∧
        codes.foldl (fun S c => letK LD LI GQ c S) (enc m B st) =
          enc m (((edgeStates (codes.map fun c => (c / 2, c % 2 == 0)) st).map
            (contribOf tab m)).foldl (fun A c => A ^^^ (c.2 <<< (11 * c.1))) B) st'
  | [], st, h, B, hs, _ => ⟨st, h, hs, by simp [edgeStates]⟩
  | c :: codes, st, h, B, hs, hc => by
    have hc0 := hc c List.mem_cons_self
    have hrest : ∀ c ∈ codes, c < 4 := fun c' h' => hc c' (List.mem_cons_of_mem _ h')
    have hx : Nat.shiftRight c 1 = c / 2 := by
      rw [r_shr, Nat.shiftRight_eq_div_pow, pow_one]
    rw [List.foldl_cons, List.map_cons, edgeStates, List.map_cons, List.foldl_cons]
    by_cases hb : c % 2 = 0
    · have hb' : (c % 2 == 0) = true := by simp [hb]
      have hk : letK LD LI GQ c (enc m B st) =
          move LD LI c (emit GQ (c / 2) (enc m B st)) := by
        have e : Nat.beq (Nat.land c 1) 0 = true := by
          rw [Nat.beq_eq, r_land, Nat.and_one_is_mod, hb]
        simp only [letK, e, hx]
      rw [hk, emit_eq hL hGQ hs, move_eq hl hs hc0]
      obtain ⟨st', h', hs', e⟩ := walk_codes hL hl hGQ m codes _ _ _ (HAOK.step' hs hc0) hrest
      refine ⟨st', h', hs', ?_⟩
      rw [e]
      simp only [hb', if_true, contribOf]
    · have hb' : (c % 2 == 0) = false := by simp [hb]
      have hk : letK LD LI GQ c (enc m B st) =
          emit GQ (c / 2) (move LD LI c (enc m B st)) := by
        have e : Nat.beq (Nat.land c 1) 0 = false := by
          cases e' : Nat.beq (Nat.land c 1) 0
          · rfl
          · rw [Nat.beq_eq, r_land, Nat.and_one_is_mod] at e'
            exact absurd e' hb
        simp only [letK, e, hx]
      rw [hk, move_eq hl hs hc0, emit_eq hL hGQ (HAOK.step' hs hc0)]
      obtain ⟨st', h', hs', e⟩ := walk_codes hL hl hGQ m codes _ _ _ (HAOK.step' hs hc0) hrest
      refine ⟨st', h', hs', ?_⟩
      rw [e]
      simp only [hb', Bool.false_eq_true, if_false, contribOf]

theorem rec_foldl (g : Nat → Nat → Nat) (L : Nat → Nat) (N : Nat) :
    ∀ (len lo S : Nat), lo + len = N →
    Nat.rec (motive := fun _ => Nat → Nat) (fun S => S)
      (fun k ih S => Loop.strictN (g (L (Nat.sub N k)) S) ih) len S =
      ((List.range len).map fun k => L (lo + 1 + k)).foldl (fun S c => g c S) S
  | 0, _, _, _ => rfl
  | len + 1, lo, S, hN => by
    rw [List.range_succ_eq_map, List.map_cons, List.foldl_cons, List.map_map]
    change Loop.strictN (g (L (Nat.sub N len)) S)
      (Nat.rec (motive := fun _ => Nat → Nat) (fun S => S)
        (fun k ih S => Loop.strictN (g (L (Nat.sub N k)) S) ih) len) = _
    have e : N - len = lo + 1 + 0 := by omega
    rw [strictN_eq, rec_foldl g L N len (lo + 1) _ (by omega), r_sub, e]
    congr 2
    funext k
    simp only [Function.comp_apply]
    congr 1
    omega

theorem decR_codes (W : Nat) :
    ((List.range (ln 6 W 0)).map fun k => ln 6 W (0 + 1 + k)).map (fun c => (c / 2, c % 2 == 0)) =
      decR W := by
  rw [List.map_map]
  refine List.ext_getElem (by simp [decR_length]) fun k h1 h2 => ?_
  rw [decR_getElem W h2]
  simp [Nat.add_comm]

theorem entK_eq {tab : Array (List (ℕ × Bool))} (hL : ∀ p, ∀ l ∈ tword tab p, l.1 < 2)
    {LD LI GQ FP RW : Nat → Nat} (hl : LetOK LD LI)
    (hT : treeOK tab = true) (hGQ : GQOK tab GQ)
    (hFP : ∀ q < 576, q / 24 ≠ q % 24 → ∀ j < 11,
      ln 11 (FP q) j = dualAct (matA (wordA (tword tab q))) (2 ^ j))
    (hw : ((List.range 7).map fun i => decR (RW i)) = relWords) (e A : Nat)
    (hp0 : e % 1024 / 24 < 24) (hp1 : e % 1024 % 24 < 24) (hp2 : e % 1024 / 24 ≠ e % 1024 % 24)
    (hi : e / 1024 % 8 < 7) (hm : e / 8192 < 2048) :
    entK LD LI GQ FP RW e A =
      A ^^^ keyTab (contribs tab (e % 1024) (e / 1024 % 8) (e / 8192)) := by
  have e1 : Nat.land e 1023 = e % 1024 := Nat.and_two_pow_sub_one_eq_mod e 10
  have e2 : Nat.land (Nat.shiftRight e 10) 7 = e / 1024 % 8 :=
    (Nat.and_two_pow_sub_one_eq_mod (e >>> 10) 3).trans (by rw [Nat.shiftRight_eq_div_pow])
  have e3 : Nat.shiftRight e 13 = e / 8192 := Nat.shiftRight_eq_div_pow e 13
  simp only [entK, strictN_eq]
  rw [e1, e2, e3]
  generalize e % 1024 = p at *
  generalize e / 1024 % 8 = i at *
  generalize e / 8192 = m at *
  have hp : p < 576 := by omega
  have hpt := treeOK_spec hT (p / 24) hp0 (p % 24) hp1 hp2
  rw [Nat.div_add_mod] at hpt
  have hstart : HAOK (startHA tab p) (wordProd gens (tword tab p)) :=
    ⟨hasArr_wordProd _ (hL p), hasArr_wordProd_inv _ (hL p)⟩
  have hS : Nat.add (Nat.shiftLeft A 21) (Nat.add (Nat.div p 24)
      (Nat.add (Nat.mul 32 (Nat.mod p 24)) (Nat.mul 1024 (dapp (FP p) m)))) =
      enc m A (startHA tab p) := by
    rw [dapp_eq_dualAct (hFP p hp hp2) (by norm_num; omega)]
    simp only [enc, lowOf, startHA, r_add, r_shl, r_div, r_mod, r_mul, hpt.1, hpt.2]
    ring
  rw [hS]
  unfold walkK
  rw [rec_foldl _ _ _ (ln 6 (RW i) 0) 0 _ (Nat.zero_add _)]
  have hmem : decR (RW i) ∈ relWords := by
    rw [← hw]
    exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
  have hrw : relWords[i]! = decR (RW i) := by
    rw [getElem!_pos relWords i (by rw [← hw, List.length_map, List.length_range]; exact hi)]
    simp only [← hw, List.getElem_map, List.getElem_range]
  have hcodes : ∀ c ∈ (List.range (ln 6 (RW i) 0)).map (fun k => ln 6 (RW i) (0 + 1 + k)),
      c < 4 := by
    intro c hc
    have h1 : (c / 2, c % 2 == 0) ∈ decR (RW i) := by
      rw [← decR_codes]
      exact List.mem_map.2 ⟨c, hc, rfl⟩
    have := relWords_letters _ hmem _ h1
    simp only at this
    omega
  obtain ⟨st', h', hs', hwalk⟩ := walk_codes hL hl hGQ m _ _ _ A hstart hcodes
  rw [hwalk, decR_codes, r_shr, enc_hi hs', foldl_keyTab_start, contribs, hrw]
  rfl

theorem runE_list {tab : Array (List (ℕ × Bool))} (hL : ∀ p, ∀ l ∈ tword tab p, l.1 < 2)
    {LD LI GQ FP RW : Nat → Nat} (hl : LetOK LD LI)
    (hT : treeOK tab = true) (hGQ : GQOK tab GQ)
    (hFP : ∀ q < 576, q / 24 ≠ q % 24 → ∀ j < 11,
      ln 11 (FP q) j = dualAct (matA (wordA (tword tab q))) (2 ^ j))
    (hw : ((List.range 7).map fun i => decR (RW i)) = relWords)
    (C : Nat) (hent : entriesOK (decC C) = true) :
    ∀ len lo A, lo + len ≤ (decC C).length →
      ((List.range len).map fun k => ln 24 C (lo + 1 + k)).foldl
        (fun S c => entK LD LI GQ FP RW c S) A =
      A ^^^ keyTab (comboContribs tab (((decC C).drop lo).take len))
  | 0, lo, A, _ => by simp [comboContribs, keyTab]
  | len + 1, lo, A, hlen => by
    have hlo : lo < (decC C).length := by omega
    rw [List.range_succ_eq_map, List.map_cons, List.foldl_cons, List.map_map]
    have e : ((fun k => ln 24 C (lo + 1 + k)) ∘ Nat.succ) = fun k => ln 24 C (lo + 1 + 1 + k) := by
      funext k
      simp only [Function.comp_apply]
      congr 1
      omega
    rw [e, runE_list hL hl hT hGQ hFP hw C hent len (lo + 1) _ (by omega),
      List.drop_eq_getElem_cons hlo, List.take_succ_cons]
    have hcons : ∀ (a : Nat × Nat × Nat) (L : List (Nat × Nat × Nat)), comboContribs tab (a :: L) =
        contribs tab a.1 a.2.1 a.2.2 ++ comboContribs tab L := by
      intro a L
      simp [comboContribs, List.flatMap_cons]
    rw [hcons, keyTab_append, ← Nat.xor_assoc, Nat.add_zero]
    congr 1
    have hx := List.getElem_mem hlo
    have hd : (decC C)[lo] = (ln 24 C (lo + 1) % 1024, ln 24 C (lo + 1) / 1024 % 8,
        ln 24 C (lo + 1) / 8192) := by
      simp [decC, ln_eq]
    have hok := List.all_eq_true.1 hent _ hx
    rw [hd] at hok ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hok
    obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hok
    exact entK_eq hL hl hT hGQ hFP hw _ A h0 h1 h2 h3 h4

theorem runE_eq (TW PA GQ FP LD LI LM RW : Nat → Nat) (hlet : lettersTabOK LI LD LM = true)
    (htree : ∀ q < 576, treeQ TW PA GQ FP LD LI q = true)
    (hw : ((List.range 7).map fun i => decR (RW i)) = relWords)
    (C : Nat) (hent : entriesOK (decC C) = true) (lo len A : Nat) (hlen : lo + len ≤ C % 2 ^ 24) :
    runE LD LI GQ FP RW C lo len A =
      A ^^^ keyTab (comboContribs (tabOf TW) (((decC C).drop lo).take len)) := by
  have hl := lettersTabOK_spec hlet
  obtain ⟨hT, -, hcols⟩ := treeOK_of TW PA GQ FP LD LI LM hlet htree
  have hdl : (decC C).length = C % 2 ^ 24 := by simp [decC]
  unfold runE
  rw [rec_foldl (entK LD LI GQ FP RW) (ln 24 C) (Nat.add lo len) len lo A rfl]
  exact runE_list (tword_tabOf_letters TW) (fun c hc => ⟨(hl c hc).1, (hl c hc).2.1⟩) hT
    (fun q hq huv j hj => (hcols q hq huv j hj).1) (fun q hq huv j hj => (hcols q hq huv j hj).2)
    hw C hent len lo A (by rw [hdl]; exact hlen)

theorem bucket_cons (c : Nat × Nat) (L : List (Nat × Nat)) (κ : Nat) :
    bucket (c :: L) κ = if c.1 = κ then c.2 ^^^ bucket L κ else bucket L κ := by
  unfold bucket
  by_cases h : c.1 = κ
  · simp [h, List.filter_cons, xorMasks]
  · simp [h, List.filter_cons]

theorem testBit_shift_lane {v : Nat} (hv : v < 2 ^ 11) (k κ : Nat) {b : Nat} (hb : b < 11) :
    (v <<< (11 * k)).testBit (11 * κ + b) = if k = κ then v.testBit b else false := by
  rw [Nat.testBit_shiftLeft]
  by_cases hk : k = κ
  · subst hk
    simp [show 11 * k + b - 11 * k = b by omega]
  · rw [if_neg hk]
    by_cases hle : 11 * k ≤ 11 * κ + b
    · have hlt : k < κ := by omega
      have : v.testBit (11 * κ + b - 11 * k) = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num)
          (by omega)))
      simp [hle, this]
    · simp [hle]

theorem testBit_foldl_keyTab : ∀ (L : List (Nat × Nat)), (∀ c ∈ L, c.2 < 2 ^ 11) → ∀ (A κ b : Nat),
    b < 11 → (L.foldl (fun A c => A ^^^ (c.2 <<< (11 * c.1))) A).testBit (11 * κ + b) =
      (A.testBit (11 * κ + b) ^^ (bucket L κ).testBit b)
  | [], _, A, κ, b, _ => by simp [bucket, xorMasks]
  | c :: L, hv, A, κ, b, hb => by
    rw [List.foldl_cons, testBit_foldl_keyTab L (fun d hd => hv d (List.mem_cons_of_mem c hd))
      _ κ b hb, Nat.testBit_xor, testBit_shift_lane (hv c List.mem_cons_self) c.1 κ hb,
      bucket_cons]
    by_cases h : c.1 = κ
    · simp only [h, if_true, Nat.testBit_xor, Bool.xor_assoc]
    · simp only [h, if_false, Bool.xor_false]

theorem bucketsZero_of_keyTab_bounds (L : List (Nat × Nat)) (hk : ∀ c ∈ L, c.1 < 1152)
    (hv : ∀ c ∈ L, c.2 < 2 ^ 11) (h0 : keyTab L = 0) : bucketsZero L = true := by
  unfold bucketsZero
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range, beq_iff_eq]
  refine ⟨hk, fun κ _ => ?_⟩
  have hlt : bucket L κ < 2 ^ 11 := by
    unfold bucket
    refine xorMasks_lt fun m hm => ?_
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hm
    exact hv c (List.mem_filter.1 hc).1
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [Nat.zero_testBit]
  by_cases hb : b < 11
  · have h := testBit_foldl_keyTab L hv 0 κ b hb
    unfold keyTab at h0
    rw [h0] at h
    simp only [Nat.zero_testBit, Bool.false_xor] at h
    exact h.symm
  · exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num)
      (by omega)))

theorem mem_of_forall₂ {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b, R a b
  | [], [], _, a, ha => absurd ha List.not_mem_nil
  | _ :: _, _ :: _, List.Forall₂.cons hr h, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, hr⟩
    · exact mem_of_forall₂ h a ha

theorem entriesOK_spec' {ents : List (Nat × Nat × Nat)} (h : entriesOK ents = true) :
    ∀ e ∈ ents, e.2.1 < 7 := by
  intro e he
  unfold entriesOK at h
  have := List.all_eq_true.1 h e he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1.2

theorem comboContribs_bounds (tab : Array (List (ℕ × Bool)))
    (hL : ∀ p, ∀ l ∈ tword tab p, l.1 < 2) (ents : List (Nat × Nat × Nat))
    (hent : entriesOK ents = true) :
    ∀ c ∈ comboContribs tab ents, c.1 < 1152 ∧ c.2 < 2 ^ 11 := by
  intro c hc
  obtain ⟨e, he, hce⟩ := List.mem_flatMap.1 hc
  obtain ⟨st, hst, rfl⟩ := List.mem_map.1 hce
  have hi := entriesOK_spec' hent e he
  have hrw : relWords[e.2.1]! ∈ relWords := by
    rw [getElem!_pos relWords e.2.1 (by simp [relWords]; omega)]
    exact List.getElem_mem _
  have hstart : HAOK (startHA tab e.1) (wordProd gens (tword tab e.1)) :=
    ⟨hasArr_wordProd _ (hL e.1), hasArr_wordProd_inv _ (hL e.1)⟩
  obtain ⟨st', hR, -, hx⟩ := mem_of_forall₂
    (edgeStates_forall₂ _ (relWords_letters _ hrw) _ _ hstart) st hst
  have h0 := hR.2 ⟨0, by norm_num⟩
  have h1 := hR.2 ⟨1, by norm_num⟩
  have hb0 : st.1.bwd[0]! < 24 := by
    have : (0 : Fin 24).val = 0 := rfl
    rw [← h0]
    exact Fin.isLt _
  have hb1 : st.1.bwd[1]! < 24 := by
    rw [← h1]
    exact Fin.isLt _
  refine ⟨?_, ?_⟩
  · simp only [keyOf, ptIdx]
    omega
  · simpa [length_matA] using dualAct_lt (matA (kArr tab st.1)) e.2.2

theorem bucketsZero_of_keyTab (TW : Nat → Nat) (ents : List (Nat × Nat × Nat))
    (hent : entriesOK ents = true) (h0 : keyTab (comboContribs (tabOf TW) ents) = 0) :
    bucketsZero (comboContribs (tabOf TW) ents) = true :=
  bucketsZero_of_keyTab_bounds _
    (fun c hc => (comboContribs_bounds _ (tword_tabOf_letters TW) ents hent c hc).1)
    (fun c hc => (comboContribs_bounds _ (tword_tabOf_letters TW) ents hent c hc).2) h0

theorem testBit_ln (w P j b : Nat) :
    (ln w P j).testBit b = (decide (b < w) && P.testBit (w * j + b)) := by
  rw [ln_eq, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm b]

theorem ln_xor (w a b j : Nat) : ln w (a ^^^ b) j = ln w a j ^^^ ln w b j :=
  Nat.eq_of_testBit_eq fun i => by
    simp only [testBit_ln, Nat.testBit_xor]
    cases decide (i < w) <;> simp

theorem ln_or (w a b j : Nat) : ln w (a ||| b) j = ln w a j ||| ln w b j :=
  Nat.eq_of_testBit_eq fun i => by
    simp only [testBit_ln, Nat.testBit_or]
    cases decide (i < w) <;> simp

theorem ln_shift {v : Nat} (hv : v < 2 ^ 11) (k j : Nat) :
    ln 11 (v <<< (11 * k)) j = if k = j then v else 0 :=
  Nat.eq_of_testBit_eq fun b => by
    rw [testBit_ln]
    by_cases hb : b < 11
    · rw [testBit_shift_lane hv k j hb]
      split_ifs <;> simp [hb]
    · have hvb : v.testBit b = false := Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega)))
      split_ifs <;> simp [hb, hvb]

theorem ln_shift121 {M : Nat} (hM : M < 2 ^ 121) (x y : Nat) {j : Nat} (hj : j < 11) :
    ln 11 (M <<< (121 * x)) (11 * y + j) = if x = y then ln 11 M j else 0 := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [testBit_ln, Nat.testBit_shiftLeft]
  by_cases hb : b < 11
  · by_cases hxy : x = y
    · subst hxy
      have e : 11 * (11 * x + j) + b - 121 * x = 11 * j + b := by omega
      have e2 : 11 * (11 * x + j) + b ≥ 121 * x := by omega
      simp [hb, e, e2, testBit_ln]
    · rw [if_neg hxy, Nat.zero_testBit]
      rcases Nat.lt_or_gt_of_ne hxy with h | h
      · have : M.testBit (11 * (11 * y + j) + b - 121 * x) = false := Nat.testBit_eq_false_of_lt
          (lt_of_lt_of_le hM (Nat.pow_le_pow_right (by norm_num) (by omega)))
        simp [this]
      · have : ¬ (11 * (11 * y + j) + b ≥ 121 * x) := by omega
        simp [this]
  · split_ifs <;> simp [hb, testBit_ln]

theorem ln_shr121 (L j : Nat) : ln 11 (L >>> 121) j = ln 11 L (11 * 1 + j) :=
  Nat.eq_of_testBit_eq fun b => by
    rw [testBit_ln, testBit_ln, Nat.testBit_shiftRight]
    congr 2
    ring

theorem land1023 (e : Nat) : Nat.land e 1023 = e % 1024 := Nat.and_two_pow_sub_one_eq_mod e 10

theorem lane_rel (e : Nat) : Nat.land (Nat.shiftRight e 10) 7 = e / 1024 % 8 :=
  (Nat.and_two_pow_sub_one_eq_mod (e >>> 10) 3).trans (by rw [Nat.shiftRight_eq_div_pow])

theorem shr13 (e : Nat) : Nat.shiftRight e 13 = e / 8192 := Nat.shiftRight_eq_div_pow e 13

theorem runF_succ (FP : Nat → Nat) (C lo n : Nat) :
    runF FP C lo (n + 1) = runF FP C lo n ^^^ (dapp (FP (ln 24 C (lo + n) % 1024))
      (ln 24 C (lo + n) / 8192) <<< (11 * (ln 24 C (lo + n) / 1024 % 8))) := by
  have e : runF FP C lo (n + 1) = Loop.strictN (ln 24 C (Nat.add lo n)) fun e =>
      Nat.xor (runF FP C lo n) (Nat.shiftLeft (dapp (FP (Nat.land e 1023)) (Nat.shiftRight e 13))
        (Nat.mul 11 (Nat.land (Nat.shiftRight e 10) 7))) := rfl
  rw [e, strictN_eq, land1023, lane_rel, shr13]
  rfl

theorem decC_getElem (C : Nat) {k : Nat} (hk : k < (decC C).length) :
    (decC C)[k] = (ln 24 C (k + 1) % 1024, ln 24 C (k + 1) / 1024 % 8, ln 24 C (k + 1) / 8192) := by
  simp [decC, ln_eq]

theorem entriesOK_getElem {ents : List (Nat × Nat × Nat)} (h : entriesOK ents = true) {k : Nat}
    (hk : k < ents.length) :
    ents[k].1 / 24 < 24 ∧ ents[k].1 % 24 < 24 ∧ ents[k].1 / 24 ≠ ents[k].1 % 24 ∧ ents[k].2.1 < 7 ∧
      ents[k].2.2 < 2048 := by
  have hok := List.all_eq_true.1 h _ (List.getElem_mem hk)
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hok
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hok
  exact ⟨h0, h1, h2, h3, h4⟩

theorem runF_spec {tab : Array (List (ℕ × Bool))} {FP : Nat → Nat}
    (hFP : ∀ q < 576, q / 24 ≠ q % 24 → ∀ j < 11,
      ln 11 (FP q) j = dualAct (matA (wordA (tword tab q))) (2 ^ j))
    (C : Nat) (hent : entriesOK (decC C) = true) :
    ∀ n ≤ (decC C).length, ∀ i, ln 11 (runF FP C 1 n) i = comboF tab ((decC C).take n) i
  | 0, _, i => by simp [runF, comboF, xorMasks, ln_eq]
  | n + 1, hn, i => by
    have hk : n < (decC C).length := by omega
    obtain ⟨h0, h1, h2, h3, h4⟩ := entriesOK_getElem hent hk
    rw [decC_getElem C hk] at h0 h1 h2 h3 h4
    rw [runF_succ, ln_xor, runF_spec hFP C hent n (by omega) i, ln_shift (dapp_lt _ _),
      List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, comboF, comboF,
      List.filter_append, List.map_append, xorMasks_append, decC_getElem C hk, Nat.add_comm 1 n]
    congr 1
    simp only [List.filter_cons, List.filter_nil, beq_iff_eq]
    split_ifs with hi
    · simp only [List.map_cons, List.map_nil, xorMasks, Nat.xor_zero, fpart]
      have hp : ln 24 C (n + 1) % 1024 < 576 := by omega
      exact dapp_eq_dualAct (hFP _ hp h2) (by norm_num; omega)
    · rfl

theorem fbit_eq {tab : Array (List (ℕ × Bool))} {FP CB FS : Nat → Nat}
    (hFP : ∀ q < 576, q / 24 ≠ q % 24 → ∀ j < 11,
      ln 11 (FP q) j = dualAct (matA (wordA (tword tab q))) (2 ^ j))
    (hent : (csOf CB).all entriesOK = true) (hfs : ∀ r < 67, fsQ FP (CB r) (FS r) = true)
    {r κ : Nat} (hr : r < 67) (hκ : κ < 77) :
    fbit ((csOf CB).map (comboFs tab))[r]! κ = (FS r).testBit κ := by
  have hlen : ((csOf CB).map (comboFs tab)).length = 67 := by simp [csOf]
  have e1 : ((csOf CB).map (comboFs tab))[r]! = comboFs tab (decC (CB r)) := by
    rw [getElem!_pos _ r (by rw [hlen]; exact hr)]
    simp [csOf]
  have hent' : entriesOK (decC (CB r)) = true := by
    have := List.all_eq_true.1 hent (decC (CB r)) (List.mem_map.2 ⟨r, List.mem_range.2 hr, rfl⟩)
    exact this
  have hF : runF FP (CB r) 1 (ln 24 (CB r) 0) = FS r := Nat.eq_of_beq_eq_true (hfs r hr)
  have hdl : (decC (CB r)).length = ln 24 (CB r) 0 := by simp [decC, ln_eq]
  have hl := runF_spec hFP (CB r) hent' _ (le_of_eq hdl.symm) (κ / 11)
  rw [hF, ← hdl, List.take_length] at hl
  rw [e1, fbit, getElem!_pos _ (κ / 11) (by simp [comboFs]; omega)]
  simp only [comboFs, List.getElem_map, List.getElem_range]
  rw [← hl, testBit_ln, Nat.div_add_mod]
  simp [Nat.mod_lt κ (by norm_num : 0 < 11)]

theorem rec_xor_filter (p : Nat → Bool) (g : Nat → Nat) : ∀ n,
    Nat.rec (motive := fun _ => Nat) 0
      (fun r acc => Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (g r)) (p r)) n =
      xorMasks (((List.range n).filter p).map g)
  | 0 => rfl
  | n + 1 => by
    change Bool.rec (motive := fun _ => Nat) _ _ (p n) = _
    rw [rec_xor_filter p g n, List.range_succ, List.filter_append,
      List.map_append, xorMasks_append, List.filter_cons, List.filter_nil]
    cases p n
    · simp [xorMasks]
    · simp only [if_true, List.map_cons, List.map_nil, xorMasks, Nat.xor_zero]
      rfl

theorem strictP_eq (y : Nat) (k : Nat → Nat × Nat) : strictP y k = k y := by cases y <;> rfl

def packN (f : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j acc => Nat.lor acc (Nat.shiftLeft (f j) (Nat.mul 11 j))) n

theorem packN_spec {f : Nat → Nat} (hf : ∀ j, f j < 2 ^ 11) : ∀ n,
    packN f n < 2 ^ (11 * n) ∧ ∀ j, ln 11 (packN f n) j = if j < n then f j else 0
  | 0 => ⟨by simp [packN], fun j => by simp [packN, ln_eq]⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := packN_spec hf n
    have e : packN f (n + 1) = packN f n ||| (f n <<< (11 * n)) := rfl
    refine ⟨?_, fun j => ?_⟩
    · rw [e]
      refine Nat.or_lt_two_pow
        (lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by omega))) ?_
      rw [Nat.shiftLeft_eq, Nat.mul_add, Nat.mul_one, pow_add, mul_comm (2 ^ (11 * n))]
      exact Nat.mul_lt_mul_of_pos_right (hf n) (Nat.two_pow_pos _)
    · rw [e, ln_or, h2, ln_shift (hf n)]
      by_cases hj : j < n
      · rw [if_pos hj, if_neg (by omega), if_pos (by omega), Nat.or_zero]
      · rw [if_neg hj, Nat.zero_or]
        by_cases hjn : n = j
        · rw [if_pos hjn, if_pos (by omega), hjn]
        · rw [if_neg hjn, if_neg (by omega)]

theorem lamStep_eq (LM : Nat → Nat) (c M A : Nat) :
    lamStep LM c (M, A) = (packN (fun j => dapp M (ln 11 (LM c) j)) 11,
      A ^^^ ((if c % 2 = 0 then M else packN (fun j => dapp M (ln 11 (LM c) j)) 11) <<<
        (121 * (c / 2)))) := by
  have hx : Nat.shiftRight c 1 = c / 2 := by rw [r_shr, Nat.shiftRight_eq_div_pow, pow_one]
  unfold lamStep
  simp only [strictP_eq]
  by_cases hc : c % 2 = 0
  · have e : Nat.beq (Nat.land c 1) 0 = true := by rw [Nat.beq_eq, r_land, Nat.and_one_is_mod, hc]
    rw [e, if_pos hc, hx]
    rfl
  · have e : Nat.beq (Nat.land c 1) 0 = false := by
      cases e' : Nat.beq (Nat.land c 1) 0
      · rfl
      · rw [Nat.beq_eq, r_land, Nat.and_one_is_mod] at e'
        exact absurd e' hc
    rw [e, if_neg hc, hx]
    rfl

def vecYJ (y j : Nat) : Nat × Nat := (if y = 0 then 2 ^ j else 0, if y = 0 then 0 else 2 ^ j)

def foxT (y j : Nat) (e : HA × Nat) : Nat :=
  actM (matA e.1.fwd) (if e.2 = 0 then (vecYJ y j).1 else (vecYJ y j).2)

theorem act11_zero (a : Array ℕ) : act11 a 0 = 0 := XorLin.map_zero (xorLin_act11 a)

theorem foxT_eq (st : HA) {x y j : Nat} (hx : x < 2) (hy : y < 2) (hj : j < 11) :
    foxT y j (st, x) = if x = y then act11 st.fwd (2 ^ j) else 0 := by
  have h0 : actM (matA st.fwd) 0 = 0 := by rw [actM_matA _ (by norm_num), act11_zero]
  have h1 : actM (matA st.fwd) (2 ^ j) = act11 st.fwd (2 ^ j) :=
    actM_matA _ (Nat.pow_lt_pow_right (by norm_num) hj)
  unfold foxT vecYJ
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;>
    rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl <;> simp [h0, h1]

theorem lam_codes {LM : Nat → Nat}
    (hLM : ∀ c < 4, ∀ j < 11, ln 11 (LM c) j = act11 (letArr (c / 2) (c % 2 == 0)) (2 ^ j)) :
    ∀ (codes : List Nat) (st : HA) (h : ↥AutPerm) (M A : Nat), HAOK st h → (∀ c ∈ codes, c < 4) →
      (∀ j < 11, ln 11 M j = act11 st.fwd (2 ^ j)) → M < 2 ^ 121 → A < 2 ^ 242 →
      (codes.foldl (fun acc c => lamStep LM c acc) (M, A)).2 < 2 ^ 242 ∧
      ∀ y < 2, ∀ j < 11, ln 11 (codes.foldl (fun acc c => lamStep LM c acc) (M, A)).2 (11 * y + j) =
        ln 11 A (11 * y + j) ^^^
          xorMasks ((edgeStates (codes.map fun c => (c / 2, c % 2 == 0)) st).map (foxT y j))
  | [], st, h, M, A, _, _, _, _, hA => ⟨hA, fun y _ j _ => by simp [edgeStates, xorMasks]⟩
  | c :: codes, st, h, M, A, hs, hc, hM, hMb, hA => by
    have hc0 := hc c List.mem_cons_self
    have hc2 : c / 2 < 2 := by omega
    have hrest : ∀ c ∈ codes, c < 4 := fun c' h' => hc c' (List.mem_cons_of_mem _ h')
    have hf : ∀ j, dapp M (ln 11 (LM c) j) < 2 ^ 11 := fun j => dapp_lt _ _
    obtain ⟨hM'b, hM'l⟩ := packN_spec hf 11
    have hM'c : ∀ j < 11, ln 11 (packN (fun j => dapp M (ln 11 (LM c) j)) 11) j =
        act11 (st.step (c / 2) (c % 2 == 0)).fwd (2 ^ j) := by
      intro j hj
      rw [hM'l, if_pos hj, hLM c hc0 j hj, dapp_eq_act11 hM (act11_lt _ _)]
      exact (act11_compA (Subtype.prop h) (Subtype.prop _) hs.1
        (hasArr_letterVal (c / 2, c % 2 == 0) hc2) _).symm
    have hX : (if c % 2 = 0 then M else packN (fun j => dapp M (ln 11 (LM c) j)) 11) < 2 ^ 121 := by
      split_ifs
      · exact hMb
      · exact hM'b
    have hA' : A ^^^ ((if c % 2 = 0 then M else packN (fun j => dapp M (ln 11 (LM c) j)) 11) <<<
        (121 * (c / 2))) < 2 ^ 242 := by
      refine Nat.xor_lt_two_pow hA ?_
      rw [Nat.shiftLeft_eq]
      calc _ < 2 ^ 121 * 2 ^ (121 * (c / 2)) := Nat.mul_lt_mul_of_pos_right hX (Nat.two_pow_pos _)
        _ ≤ 2 ^ 242 := by
          rw [← pow_add]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [List.foldl_cons, lamStep_eq, List.map_cons, edgeStates]
    obtain ⟨ihb, ihl⟩ := lam_codes hLM codes _ _ _ _ (HAOK.step' hs hc0) hrest hM'c hM'b hA'
    refine ⟨ihb, fun y hy j hj => ?_⟩
    rw [ihl y hy j hj, ln_xor, ln_shift121 hX _ _ hj, List.map_cons, xorMasks, ← Nat.xor_assoc]
    congr 2
    by_cases hb : c % 2 = 0
    · have he : (if (c % 2 == 0) = true then st else st.step (c / 2) (c % 2 == 0)) = st :=
        if_pos (by simp [hb])
      rw [he, foxT_eq st hc2 hy hj, if_pos hb]
      split_ifs
      · exact hM j hj
      · rfl
    · have he : (if (c % 2 == 0) = true then st else st.step (c / 2) (c % 2 == 0)) =
          st.step (c / 2) (c % 2 == 0) := if_neg (by simp [hb])
      rw [he, foxT_eq _ hc2 hy hj, if_neg hb]
      split_ifs
      · exact hM'c j hj
      · rfl

theorem rec_foldl2 (g : Nat → Nat × Nat → Nat × Nat) (L : Nat → Nat) (s : Nat × Nat) : ∀ n,
    Nat.rec (motive := fun _ => Nat × Nat) s (fun j acc => g (L (Nat.add j 1)) acc) n =
      ((List.range n).map fun j => L (Nat.add j 1)).foldl (fun acc c => g c acc) s
  | 0 => rfl
  | n + 1 => by
    rw [Nat.rec_add_one, rec_foldl2 g L s n, List.range_succ, List.map_append, List.foldl_append]
    rfl

theorem decR_codes2 (W : Nat) :
    ((List.range (ln 6 W 0)).map fun k => ln 6 W (Nat.add k 1)).map (fun c => (c / 2, c % 2 == 0)) =
      decR W := by
  rw [List.map_map]
  refine List.ext_getElem (by simp [decR_length]) fun k h1 h2 => ?_
  rw [decR_getElem W h2]
  simp

theorem idCols_lanes : ∀ j < 11, ln 11 idCols j = 2 ^ j := by decide

theorem idCols_lt : idCols < 2 ^ 121 := by decide

theorem lamOf_lanes {LM RW : Nat → Nat}
    (hLM : ∀ c < 4, ∀ j < 11, ln 11 (LM c) j = act11 (letArr (c / 2) (c % 2 == 0)) (2 ^ j))
    (hw : ((List.range 7).map fun i => decR (RW i)) = relWords) {i : Nat} (hi : i < 7)
    {y j : Nat} (hy : y < 2) (hj : j < 11) :
    ln 11 (lamOf LM (RW i)) (11 * y + j) = lamApply (vecYJ y j) i := by
  have hmem : decR (RW i) ∈ relWords := by
    rw [← hw]
    exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
  have hrw : relWords[i]! = decR (RW i) := by
    rw [getElem!_pos relWords i (by rw [← hw, List.length_map, List.length_range]; exact hi)]
    simp only [← hw, List.getElem_map, List.getElem_range]
  have hcodes : ∀ c ∈ (List.range (ln 6 (RW i) 0)).map (fun k => ln 6 (RW i) (Nat.add k 1)),
      c < 4 := by
    intro c hc
    have h1 : (c / 2, c % 2 == 0) ∈ decR (RW i) := by
      rw [← decR_codes2]
      exact List.mem_map.2 ⟨c, hc, rfl⟩
    have := relWords_letters _ hmem _ h1
    simp only at this
    omega
  have hid : ∀ j < 11, ln 11 idCols j = act11 HA.one.fwd (2 ^ j) := fun j hj => by
    rw [idCols_lanes j hj]
    exact (act11_idA (Nat.pow_lt_pow_right (by norm_num) hj)).symm
  obtain ⟨-, hl⟩ := lam_codes hLM _ HA.one 1 idCols 0 HAOK.one hcodes hid idCols_lt
    (Nat.two_pow_pos _)
  have e : lamOf LM (RW i) =
      (((List.range (ln 6 (RW i) 0)).map fun k => ln 6 (RW i) (Nat.add k 1)).foldl
        (fun acc c => lamStep LM c acc) (idCols, 0)).2 := by
    unfold lamOf
    rw [rec_foldl2 (lamStep LM) (ln 6 (RW i)) (idCols, 0)]
  have h0 : ln 11 0 (11 * y + j) = 0 := by simp [ln_eq]
  rw [e, hl y hy j hj, decR_codes2, lamApply, hrw, h0, Nat.zero_xor]
  rfl

theorem dapp_lam {L : Nat} {i : Nat} (hL : ∀ j < 11, ln 11 L j = lamApply (vecYJ 0 j) i)
    {a : Nat} (ha : a < 2 ^ 11) : dapp L a = lamApply (a, 0) i := by
  refine dapp_eq_of_lanes (f := fun a => lamApply (a, 0) i) (fun a b => ?_) (fun j hj => ?_) ha
  · have := lamApply_xor (a, 0) (b, 0) i
    simpa using this
  · rw [hL j hj]
    simp [vecYJ]

theorem dapp_lam1 {L : Nat} {i : Nat} (hL : ∀ j < 11, ln 11 L j = lamApply (vecYJ 1 j) i)
    {a : Nat} (ha : a < 2 ^ 11) : dapp L a = lamApply (0, a) i := by
  refine dapp_eq_of_lanes (f := fun a => lamApply (0, a) i) (fun a b => ?_) (fun j hj => ?_) ha
  · have := lamApply_xor (0, a) (0, b) i
    simpa using this
  · rw [hL j hj]
    simp [vecYJ]

theorem bezoutOK_of (TW PA GQ FP LD LI LM RW CB FS LA SD TD : Nat → Nat)
    (hlet : lettersTabOK LI LD LM = true) (htree : ∀ q < 576, treeQ TW PA GQ FP LD LI q = true)
    (hw : ((List.range 7).map fun i => decR (RW i)) = relWords)
    (hent : (csOf CB).all entriesOK = true)
    (hfs : ∀ r < 67, fsQ FP (CB r) (FS r) = true)
    (hlam : ∀ i < 7, lamOf LM (RW i) = LA i)
    (hsd : ∀ κ < 77, SD κ < 2 ^ 22)
    (hbez : ∀ κ < 77, ∀ i < 7, bezQ LA FS SD TD κ i = true) :
    bezoutOK ((csOf CB).map (comboFs (tabOf TW))) (sOf SD) (tOf TD) = true := by
  have hl := lettersTabOK_spec hlet
  obtain ⟨-, -, hcols⟩ := treeOK_of TW PA GQ FP LD LI LM hlet htree
  have hFP := fun q hq huv j hj => (hcols q hq huv j hj).2
  have hLM : ∀ c < 4, ∀ j < 11, ln 11 (LM c) j = act11 (letArr (c / 2) (c % 2 == 0)) (2 ^ j) :=
    fun c hc => (hl c hc).2.2
  unfold bezoutOK
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    and_assoc]
  refine ⟨(by simp [csOf]), (by simp [sOf]), (by simp [tOf]), fun v hv => ?_, fun t ht => ?_,
    fun κ hκ i hi => ?_⟩
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hv
    have := hsd k (List.mem_range.1 hk)
    norm_num at this
    exact ⟨Nat.mod_lt _ (by norm_num), by omega⟩
  · obtain ⟨k, -, rfl⟩ := List.mem_map.1 ht
    simp
  · have hb : _ = _ := Nat.eq_of_beq_eq_true (hbez κ hκ i hi)
    simp only [rec_xor_filter] at hb
    have hS : (sOf SD)[κ]! = (SD κ % 2048, SD κ / 2048) := by
      rw [getElem!_pos _ κ (by simp [sOf]; exact hκ)]
      simp [sOf]
    have hsdκ := hsd κ hκ
    have hLA0 : ∀ j < 11, ln 11 (LA i) j = lamApply (vecYJ 0 j) i := fun j hj => by
      rw [← hlam i hi]
      have := lamOf_lanes hLM hw hi (y := 0) (by norm_num) hj
      simpa using this
    have hLA1 : ∀ j < 11, ln 11 (LA i >>> 121) j = lamApply (vecYJ 1 j) i := fun j hj => by
      rw [ln_shr121, ← hlam i hi]
      exact lamOf_lanes hLM hw hi (by norm_num) hj
    have hlamK : lamApply (SD κ % 2048, SD κ / 2048) i = lamK (LA i) (SD κ) := by
      have hz1 : Nat.land (SD κ) 2047 = SD κ % 2048 := Nat.and_two_pow_sub_one_eq_mod _ 11
      have hz2 : Nat.shiftRight (SD κ) 11 = SD κ / 2048 := Nat.shiftRight_eq_div_pow _ 11
      unfold lamK
      rw [hz1, hz2, r_shr, r_xor, dapp_lam (a := SD κ % 2048) hLA0 (by omega),
        dapp_lam1 (a := SD κ / 2048) hLA1 (by norm_num at hsdκ ⊢; omega), ← lamApply_xor]
      simp
    have hfil : ((List.range 67).filter fun r => fbit ((csOf CB).map (comboFs (tabOf TW)))[r]! κ) =
        ((List.range 67).filter fun r => Nat.blt 0 (Nat.land (FS r) (Nat.shiftLeft 1 κ))) :=
      List.filter_congr fun r hr => by
        rw [fbit_eq hFP hent hfs (List.mem_range.1 hr) hκ, blt_land_shiftLeft]
    have hmap :
        ((List.range 67).filter fun r => Nat.blt 0 (Nat.land (FS r) (Nat.shiftLeft 1 κ))).map
          (fun r => ((tOf TD)[r]!)[i]!) =
        ((List.range 67).filter fun r => Nat.blt 0 (Nat.land (FS r) (Nat.shiftLeft 1 κ))).map
          (fun r => ln 11 (TD r) i) := by
      refine List.map_congr_left fun r hr => ?_
      have hr' : r < 67 := List.mem_range.1 (List.mem_filter.1 hr).1
      rw [getElem!_pos _ r (by simp [tOf]; exact hr')]
      simp only [tOf, List.getElem_map, List.getElem_range]
      rw [getElem!_pos _ i (by simp; exact hi)]
      simp [ln_eq]
    have hunit : unitMask κ i =
        Bool.rec (motive := fun _ => Nat) 0 (Nat.shiftLeft 1 (Nat.mod κ 11))
          (Nat.beq (Nat.div κ 11) i) := by
      unfold unitMask
      by_cases h : κ / 11 = i
      · have e : Nat.beq (Nat.div κ 11) i = true := Nat.beq_eq_true_eq _ _ ▸ h
        rw [if_pos h, e]
        exact (Nat.one_shiftLeft _).symm
      · have e : Nat.beq (Nat.div κ 11) i = false := by
          cases e' : Nat.beq (Nat.div κ 11) i
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true e') h
        rw [if_neg h, e]
    rw [hS, hlamK, hfil, hmap, hunit]
    exact hb

theorem keyTab_slice_split (tab : Array (List (ℕ × Bool))) (L : List (Nat × Nat × Nat))
    (lo a b : Nat) :
    keyTab (comboContribs tab ((L.drop lo).take (a + b))) =
      keyTab (comboContribs tab ((L.drop lo).take a)) ^^^
        keyTab (comboContribs tab ((L.drop (lo + a)).take b)) := by
  rw [List.take_add, comboContribs_append, keyTab_append, List.drop_drop]

theorem decC_length (C : Nat): (decC C).length = ln 24 C 0 := by
  simp [decC, ln_eq]

theorem bucketsZero_of_comboK (TW PA GQ FP LD LI LM RW : Nat → Nat)
    (hlet : lettersTabOK LI LD LM = true) (htree : ∀ q < 576, treeQ TW PA GQ FP LD LI q = true)
    (hw : ((List.range 7).map fun i => decR (RW i)) = relWords)
    (C : Nat) (hent : entriesOK (decC C) = true) (hk : comboK LD LI GQ FP RW C = true) :
    bucketsZero (comboContribs (tabOf TW) (decC C)) = true := by
  refine bucketsZero_of_keyTab TW _ hent ?_
  have h0 : runE LD LI GQ FP RW C 0 (ln 24 C 0) 0 = 0 := Nat.eq_of_beq_eq_true hk
  rw [runE_eq TW PA GQ FP LD LI LM RW hlet htree hw C hent 0 (ln 24 C 0) 0
    (by rw [ln_eq]; simp), Nat.zero_xor, List.drop_zero, ← decC_length,
    List.take_length] at h0
  exact h0

end CFSG.KC.M24Def

end
