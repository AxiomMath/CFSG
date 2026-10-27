module

public import CFSG.Certificates.Kernel.LocalQTCovTEqns
public import CFSG.Certificates.Kernel.LocalQTCovGe

public section

namespace CFSG.KC.LQT.Cov.T

open CFSG.KC.LQT.Cov CFSG.KC.Enum CFSG.KC.Ord CFSG.QuasithinUnique.Ch1.TitsCover

theorem xorR_eq (F : List Nat) : ∀ ks : List Nat,
    xorR (rowsG F) ks = ks.foldr (fun k acc => F.getD k 0 ^^^ acc) 0
  | [] => rfl
  | k :: ks => by
    change Nat.xor (getRG (rowsG F) k 0) (xorR (rowsG F) ks) = _
    rw [getRG_rowsG, xorR_eq F ks, List.foldr_cons]
    rfl

theorem xorR_append (F : List Nat) (a b : List Nat) :
    xorR (rowsG F) (a ++ b) = xorR (rowsG F) a ^^^ xorR (rowsG F) b := by
  induction a with
  | nil => exact (Nat.zero_xor _).symm
  | cons k a ih =>
    change Nat.xor (getRG (rowsG F) k 0) (xorR (rowsG F) (a ++ b)) = _
    rw [ih]
    change Nat.xor (getRG (rowsG F) k 0) (xorR (rowsG F) a ^^^ xorR (rowsG F) b) =
      Nat.xor (Nat.xor (getRG (rowsG F) k 0) (xorR (rowsG F) a)) (xorR (rowsG F) b)
    exact (Nat.xor_assoc _ _ _).symm

private noncomputable def triGo (FR : List (List Nat)) : List (List Nat) → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun h _ ih e => strictB e fun e =>
      CFSG.KC.Ord.andB (Nat.beq (Nat.shiftRight (xorR FR h) e) 1) (ih (Nat.succ e)))

private theorem triT_eq (FR : List (List Nat)) (H : List (List Nat)) :
    triT FR H = triGo FR H 0 := rfl

private theorem triGo_spec (FR : List (List Nat)) (H : List (List Nat)) :
    ∀ e, triGo FR H e = true → ∀ k < H.length,
      Nat.shiftRight (xorR FR (H.getD k [])) (e + k) = 1 := by
  induction H with
  | nil => intro e he k hk; exact absurd hk (Nat.not_lt_zero k)
  | cons h H ih =>
    intro e he k hk
    have hstep : triGo FR (h :: H) e = strictB e (fun e =>
        CFSG.KC.Ord.andB (Nat.beq (Nat.shiftRight (xorR FR h) e) 1) (triGo FR H (Nat.succ e))) := by
      change List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
        (fun h _ ih e => strictB e fun e =>
          CFSG.KC.Ord.andB (Nat.beq (Nat.shiftRight (xorR FR h) e) 1) (ih (Nat.succ e)))
        (h :: H) e = _
      rfl
    rw [hstep, CFSG.KS.PF.strictB_eqP, CFSG.KC.LQT.Cov.Parse.andB_eq',
      Bool.and_eq_true, Nat.beq_eq] at he
    obtain ⟨h0, hrest⟩ := he
    rcases k with _ | k
    · simpa using h0
    · have hk' : k < H.length := by simpa using hk
      have := ih (Nat.succ e) hrest k hk'
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

private noncomputable def bitList (ks : Nat → List Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | e + 1, r => bitList ks e r ++ (if r.testBit e then ks e else [])

private theorem mod_two_pow_testBit_false (r N j : Nat) (h : N ≤ j) :
    (r % 2 ^ N).testBit j = false := by
  apply Nat.testBit_lt_two_pow
  exact Nat.lt_of_lt_of_le (Nat.mod_lt r (Nat.two_pow_pos N))
    (Nat.pow_le_pow_right (n := 2) (by norm_num) h)

private theorem xorR_bitList (F : List Nat) (ks : Nat → List Nat) {e : Nat}
    (hks : ∀ i < e, xorR (rowsG F) (ks i) = 2 ^ i) (r : Nat) :
    xorR (rowsG F) (bitList ks e r) = r % 2 ^ e := by
  induction e generalizing r with
  | zero =>
    simp [bitList, xorR, Nat.mod_one]
  | succ e ih =>
    rw [bitList]
    by_cases hb : r.testBit e
    · rw [if_pos hb, xorR_append, ih (fun i hi => hks i (by omega)), hks e (by omega)]
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
        Nat.testBit_two_pow]
      by_cases hj : j < e
      · have hje : e ≠ j := by omega
        have hle : j ≤ e := Nat.le_of_lt hj
        simp [hje, hle]
        intro _; exact hj
      · by_cases hje : j = e
        · subst j
          have hlow := Nat.testBit_lt_two_pow (Nat.mod_lt r (Nat.two_pow_pos e))
          simp [hlow, hb]
        · have hge : e < j := by omega
          have h1 := mod_two_pow_testBit_false r (e + 1) j (by omega)
          have h2 := mod_two_pow_testBit_false r e j (by omega)
          have hj' : ¬ j < e := by omega
          have hle' : ¬ j ≤ e := by omega
          have hje' : e ≠ j := by omega
          simp [hj', hle', hje']
    · rw [if_neg hb, xorR_append, ih (fun i hi => hks i (by omega))]
      simp only [xorR, List.foldr_nil, Nat.xor_zero]
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
      by_cases hj : j < e
      · have hle : j ≤ e := Nat.le_of_lt hj
        simp [hj]
        intro _; exact hle
      · by_cases hje : j = e
        · subst j
          have hlow := Nat.testBit_lt_two_pow (Nat.mod_lt r (Nat.two_pow_pos e))
          simp [hlow, hb]
        · have hge : e < j := by omega
          have hj' : ¬ j < e := by omega
          have hle' : ¬ j ≤ e := by omega
          simp [hj', hle']

private theorem xor_mod_two_pow (x e : Nat) (hx : x >>> e = 1) :
    x ^^^ (x % 2 ^ e) = 2 ^ e := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_two_pow]
  have hxbit : x.testBit e = true := by
    have := Nat.testBit_shiftRight x (i := e) (j := 0)
    rw [hx] at this
    simpa using this.symm
  have hxlt : x < 2 ^ (e + 1) := by
    have hxdiv : x / 2 ^ e = 1 := by
      simpa [Nat.shiftRight_eq_div_pow] using hx
    have hdm := Nat.div_add_mod x (2 ^ e)
    simp only [hxdiv, one_mul] at hdm
    have hr := Nat.mod_lt x (Nat.two_pow_pos e)
    omega
  by_cases hj : j < e
  · have hje : ¬ e = j := by omega
    simp [hj, hje]
  · by_cases hje : j = e
    · subst j
      simp [Nat.testBit_lt_two_pow (Nat.mod_lt x (Nat.two_pow_pos e)), hxbit]
    · have hge : e < j := by omega
      have hxfalse : x.testBit j = false := by
        apply Nat.testBit_lt_two_pow
        exact Nat.lt_of_lt_of_le hxlt (Nat.pow_le_pow_right (n := 2) (by norm_num) (i := e + 1) (j := j) (by omega))
      have hrfalse : (x % 2 ^ e).testBit j = false := by
        apply Nat.testBit_lt_two_pow
        exact Nat.lt_of_lt_of_le (Nat.mod_lt x (Nat.two_pow_pos e))
          (Nat.pow_le_pow_right (n := 2) (by norm_num) (i := e) (j := j) (by omega))
      have hje' : ¬ e = j := by omega
      simp [hj, hje, hge, hxfalse, hrfalse, hje']

theorem tri_pow (F : List Nat) (H : List (List Nat))
    (hH : triT (rowsG F) H = true) :
    ∀ e < H.length, ∃ ks : List Nat, xorR (rowsG F) ks = 2 ^ e := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro he
    have hx : Nat.shiftRight (xorR (rowsG F) (H.getD e [])) e = 1 :=
      by simpa using triGo_spec (rowsG F) H 0 (by rwa [← triT_eq]) e he
    let x := xorR (rowsG F) (H.getD e [])
    have hxdef : x = xorR (rowsG F) (H.getD e []) := rfl
    let ksFun : Nat → List Nat := fun i => if h : i < e then Classical.choose (ih i h (by omega)) else []
    have hksFun : ∀ i < e, xorR (rowsG F) (ksFun i) = 2 ^ i := by
      intro i hi
      simp [ksFun, hi, Classical.choose_spec (ih i hi (by omega))]
    let r := x % 2 ^ e
    have hbit := xorR_bitList F ksFun hksFun r
    refine ⟨H.getD e [] ++ bitList ksFun e r, ?_⟩
    rw [xorR_append, hbit]
    have hx' : x >>> e = 1 := by simpa [x] using hx
    have := xor_mod_two_pow x e hx'
    simpa [x, r, Nat.xor_comm] using this

theorem tri_geFinal {d : CT} (H : List (List Nat))
    (hw : ∀ w ∈ d.words, ∀ l ∈ w, l < 2)
    (hlen : CFSG.KC.LQT.Syl.lenK H = 2 * d.nV)
    (htri : triT (rowsG (List.map Prod.snd
      (eqnsT d (rowsG d.words) (rowsG d.tgt) (rowsG d.back)))) H = true)
    (hfs : ∀ f ∈ (ofCT d).forms,
      f < 2 ^ (2 * d.nV + 32 * (ofCT d).blocks.length)) :
    geFinal (ofCT d) = true := by
  rw [geFinal, CFSG.Monster.B.Co2.allLt_iff]
  intro e he
  have hlen' : e < H.length := by
    rw [← CFSG.KC.LQT.Cov.Parse.lenK_length H, hlen]
    exact he
  obtain ⟨ks, hks⟩ := tri_pow _ H htri e hlen'
  rw [← hks, xorR_eq, ← TEqns.eqnsT_forms (d := d) hw]
  have hred := CFSG.KC.LQT.Cov.Ge.reduceF_gePivots_xor
    (M := 2 * d.nV + 32 * (ofCT d).blocks.length)
    (fuel := 2 * d.nV + 32 * (ofCT d).blocks.length + 5) hfs (by omega) ks
  rw [← TEqns.eqnsT_forms (d := d) hw] at hred
  simpa [CovData.M, ofCT, beq_iff_eq, List.getElem?_map] using hred

end CFSG.KC.LQT.Cov.T

end
