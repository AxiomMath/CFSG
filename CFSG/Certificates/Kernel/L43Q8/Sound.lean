module

public import Certificates.Data.Kernel.L43Q8.Defs
public import Certificates.Data.L43TwinQ8
public import CFSG.Certificates.Kernel.U43Pk.Sound
import CFSG.Certificates.Kernel.PackSetSound
import CFSG.Certificates.Kernel.SporSch.LyLoop

public section

namespace CFSG.KS.L43Q8

open CFSG.KD.L43Q8 CFSG.KD.U43Pk CFSG.KC.Enum CFSG.KC.Pack CFSG.KS.ArrBfsSim
open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Loc

@[expose] noncomputable def dec (P : ℕ) : Array ℕ := Array.ofFn (n := 33) fun j => dg P j

theorem dec_size (P : ℕ) : (dec P).size = 33 := by simp [dec]

theorem dec_get (P : ℕ) {k : ℕ} (hk : k < 33) : (dec P)[k]! = dg P k := by
  unfold dec
  rw [CFSG.KS.U43Pk.ofFn_get _ hk]

theorem eq_dec {x : Array ℕ} {P : ℕ} (hs : x.size = 33) (h : ∀ k < 33, x[k]! = dg P k) :
    x = dec P := by
  apply Array.ext
  · rw [hs, dec_size]
  · intro k h1 h2
    have hk : k < 33 := by rw [hs] at h1; exact h1
    rw [← getElem!_pos x k h1, h k hk]
    exact (Array.getElem_ofFn (f := fun j : Fin 33 => dg P j) h2).symm

theorem pkQ_eq (f : ℕ → ℕ) : pkQ f = CFSG.KS.U43Pk.packN f 33 := rfl

theorem dg_pkQ {f : ℕ → ℕ} (hf : ∀ k, f k < 16) (j : ℕ) :
    dg (pkQ f) j = if j < 33 then f j else 0 := by
  rw [pkQ_eq]
  exact (CFSG.KS.U43Pk.packK_go hf 33).2 j

theorem dec_pkQ {f : ℕ → ℕ} (hf : ∀ k, f k < 16) {x : Array ℕ} (hs : x.size = 33)
    (h : ∀ k < 33, x[k]! = f k) : x = dec (pkQ f) :=
  eq_dec hs fun k hk => by rw [h k hk, dg_pkQ hf, if_pos hk]

theorem sumLt_four (f : ℕ → ℕ) : sumLt 4 f = sum4 f := by
  simp [sumLt, sum4, List.range_succ]
  ring

theorem sz_eltMul (n : ℕ) (x y : Array ℕ) : (eltMul n x y).size = 2 * (n * n) + 1 := by
  simp [eltMul]

theorem get_eltMul {n : ℕ} {x y : Array ℕ} {k : ℕ} (hk : k < 2 * (n * n) + 1) :
    (eltMul n x y)[k]! = if k < n * n then
      sumLt n (fun l => eA n x (k / n) l *
        (if eE n x = 1 then eB n y l (k % n) else eA n y l (k % n))) % 3
    else if k < 2 * (n * n) then
      sumLt n (fun l => eB n x ((k - n * n) / n) l *
        (if eE n x = 1 then eA n y l ((k - n * n) % n) else eB n y l ((k - n * n) % n))) % 3
    else (eE n x + eE n y) % 2 := by
  rw [getElem!_pos _ _ (by rw [sz_eltMul]; exact hk)]
  simp [eltMul]

theorem sz_eltInv (n : ℕ) (x : Array ℕ) : (eltInv n x).size = 2 * (n * n) + 1 := by
  simp [eltInv]

theorem get_eltInv {n : ℕ} {x : Array ℕ} {k : ℕ} (hk : k < 2 * (n * n) + 1) :
    (eltInv n x)[k]! = if k < n * n then
      (if eE n x = 1 then eA n x (k % n) (k / n) else eB n x (k % n) (k / n))
    else if k < 2 * (n * n) then
      (if eE n x = 1 then eB n x ((k - n * n) % n) ((k - n * n) / n)
        else eA n x ((k - n * n) % n) ((k - n * n) / n))
    else eE n x := by
  rw [getElem!_pos _ _ (by rw [sz_eltInv]; exact hk)]
  simp [eltInv]

theorem mulE_lt (P Q k : ℕ) : mulE P Q k < 16 := by
  unfold mulE
  split_ifs <;> omega

theorem mul_dec (P Q : ℕ) : eltMul 4 (dec P) (dec Q) = dec (mulQ P Q) := by
  apply dec_pkQ (mulE_lt P Q) (sz_eltMul _ _ _)
  intro k hk
  rw [get_eltMul (by omega)]
  unfold mulE
  simp only [Nat.reduceMul]
  rcases Nat.lt_or_ge k 16 with h1 | h1
  · rw [if_pos h1, if_pos h1]
    simp (disch := omega) only [eA, eB, eE, sumLt_four, sum4, dec_get, Nat.reduceMul,
      Nat.reduceAdd, Nat.add_zero, Nat.zero_add, Nat.mul_zero]
  · have h1' : ¬ k < 16 := by omega
    rcases Nat.lt_or_ge k 32 with h2 | h2
    · rw [if_neg h1', if_neg h1', if_pos h2, if_pos h2]
      simp (disch := omega) only [eA, eB, eE, sumLt_four, sum4, dec_get, Nat.reduceMul,
        Nat.reduceAdd, Nat.add_zero, Nat.zero_add, Nat.mul_zero]
    · have h2' : ¬ k < 32 := by omega
      rw [if_neg h1', if_neg h1', if_neg h2', if_neg h2']
      simp (disch := omega) only [eE, dec_get, Nat.reduceMul]

theorem invE_lt (P k : ℕ) : invE P k < 16 := by
  unfold invE
  split_ifs <;> exact CFSG.KS.U43Pk.dg_lt _ _

theorem inv_dec (P : ℕ) : eltInv 4 (dec P) = dec (invQ P) := by
  apply dec_pkQ (invE_lt P) (sz_eltInv _ _)
  intro k hk
  rw [get_eltInv (by omega)]
  unfold invE
  simp only [Nat.reduceMul]
  rcases Nat.lt_or_ge k 16 with h1 | h1
  · rw [if_pos h1, if_pos h1]
    simp (disch := omega) only [eA, eB, eE, dec_get, Nat.reduceMul]
  · have h1' : ¬ k < 16 := by omega
    rcases Nat.lt_or_ge k 32 with h2 | h2
    · rw [if_neg h1', if_neg h1', if_pos h2, if_pos h2]
      simp (disch := omega) only [eA, eB, eE, dec_get, Nat.reduceMul]
    · have h2' : ¬ k < 32 := by omega
      rw [if_neg h1', if_neg h1', if_neg h2', if_neg h2']
      simp (disch := omega) only [eE, dec_get, Nat.reduceMul]

theorem one_dec : eltOne 4 = dec ONEQ := by decide +kernel

theorem mone_dec : eltMinusOne 4 = dec MONEQ := by decide +kernel

theorem allC {l : List ℕ} {f g : ℕ → Bool} (h : ∀ x ∈ l, f x = g x) : l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a (by simp), ih fun x hx => h x (by simp [hx])]

theorem findC {l : List ℕ} {f g : ℕ → Bool} (h : ∀ x ∈ l, f x = g x) : l.find? f = l.find? g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.find?_cons, List.find?_cons, h a (by simp), ih fun x hx => h x (by simp [hx])]

theorem eq_dec' (P Q : ℕ) : eltEq 4 (dec P) (dec Q) = eqQ P Q := by
  have hA : ∀ k ∈ List.range 16, ((dec P)[k]! % 3 == (dec Q)[k]! % 3) =
      (dg P k % 3 == dg Q k % 3) := fun k hk => by
    rw [List.mem_range] at hk
    rw [dec_get P (by omega), dec_get Q (by omega)]
  have hN : ∀ k ∈ List.range 16, (((dec P)[k]! + (dec Q)[k]!) % 3 == 0) =
      ((dg P k + dg Q k) % 3 == 0) := fun k hk => by
    rw [List.mem_range] at hk
    rw [dec_get P (by omega), dec_get Q (by omega)]
  unfold eltEq eqQ eE
  simp only [Nat.reduceMul]
  rw [dec_get P (by norm_num), dec_get Q (by norm_num), allC hA, allC hN]

theorem fnz_dec (P : ℕ) : firstNZ 4 (dec P) = fnzQ P := by
  have hF : ∀ k ∈ List.range 16, ((dec P)[k]! % 3 != 0) = (dg P k % 3 != 0) := fun k hk => by
    rw [List.mem_range] at hk
    rw [dec_get P (by omega)]
  unfold firstNZ fnzQ
  simp only [Nat.reduceMul]
  rw [findC hF]
  cases hf : (List.range 16).find? (fun k => dg P k % 3 != 0) with
  | none => rfl
  | some k =>
    have hk := List.mem_of_find?_eq_some hf
    rw [List.mem_range] at hk
    dsimp only
    rw [dec_get P (by omega)]

theorem norm_dec (P : ℕ) : eltNorm 4 (dec P) = dec (normQ P) := by
  unfold eltNorm normQ
  rw [fnz_dec, mone_dec, mul_dec]
  by_cases h : (fnzQ P == 2) = true <;> simp [h]

theorem ofDigits_map (f : ℕ → ℕ) (l : List ℕ) :
    Nat.ofDigits 3 (l.map f) = l.foldr (fun k acc => f k + 3 * acc) 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, Nat.ofDigits_cons, ih, List.foldr_cons, Nat.cast_id]

theorem key_dec (P : ℕ) : eltKey 4 (dec P) = keyQ P := by
  have h1 : (List.range 16).map (fun k => (dec P)[k]! % 3) =
      (List.range 16).map (fun k => dg P k % 3) := List.map_congr_left fun k hk => by
    rw [List.mem_range] at hk
    rw [dec_get P (by omega)]
  have h2 : (List.range 16).map (fun k => (3 - (dec P)[k]! % 3) % 3) =
      (List.range 16).map (fun k => (3 - dg P k % 3) % 3) := List.map_congr_left fun k hk => by
    rw [List.mem_range] at hk
    rw [dec_get P (by omega)]
  unfold eltKey kA kN eE keyQ b3
  simp only [Nat.reduceMul]
  rw [h1, h2, ofDigits_map, ofDigits_map, dec_get P (by norm_num)]

theorem valid_dec (P : ℕ) : eltValid 4 (dec P) = validQ P := by
  have hD : ∀ k ∈ List.range 32, decide ((dec P)[k]! < 3) = decide (dg P k < 3) := fun k hk => by
    rw [List.mem_range] at hk
    rw [dec_get P (by omega)]
  unfold eltValid validQ
  rw [dec_size]
  simp only [Nat.reduceMul, Nat.reduceAdd, beq_self_eq_true, Bool.true_and]
  have hS : ∀ i ∈ List.range 4, ((List.range 4).all fun j =>
      sumLt 4 (fun l => eA 4 (dec P) i l * eB 4 (dec P) j l) % 3 == if i == j then 1 else 0) =
      ((List.range 4).all fun j =>
        sum4 (fun l => dg P (4 * i + l) * dg P (16 + (4 * j + l))) % 3 ==
          if i == j then 1 else 0) := fun i hi => allC fun j hj => by
    rw [List.mem_range] at hi hj
    rw [sumLt_four]
    simp (disch := omega) only [eA, eB, sum4, dec_get, Nat.reduceMul]
  rw [dec_get P (by norm_num), allC hD, allC hS]

theorem conj_dec (S X : ℕ) : eltConj 4 (dec S) (dec X) = dec (conjQ S X) := by
  unfold eltConj conjQ
  rw [mul_dec, inv_dec, mul_dec]

theorem memQ8_dec (X A B : ℕ) :
    Certificates.L43TwinQ8.memQ8 (dec X) (dec A) (dec B) = memQ X A B := by
  unfold Certificates.L43TwinQ8.memQ8 Certificates.L43TwinQ8.q8Words memQ
  simp only [one_dec, mul_dec, inv_dec, List.any_cons, List.any_nil, eq_dec']

theorem commutes_dec (X Y : ℕ) :
    Certificates.L43TwinQ8.commutes (dec X) (dec Y) = commQ X Y := by
  unfold Certificates.L43TwinQ8.commutes commQ
  rw [mul_dec, mul_dec, eq_dec']

theorem sameQ8_dec (A B X Y : ℕ) :
    Certificates.L43TwinQ8.sameQ8 (dec A) (dec B) (dec X) (dec Y) = sameQ A B X Y := by
  unfold Certificates.L43TwinQ8.sameQ8 sameQ
  rw [memQ8_dec, memQ8_dec, memQ8_dec, memQ8_dec]

theorem pairOK_dec {X1 X2 X3 X4 W : ℕ} (h1 : Certificates.L43TwinQ8.q1a = dec X1)
    (h2 : Certificates.L43TwinQ8.q1b = dec X2) (h3 : Certificates.L43TwinQ8.q2a = dec X3)
    (h4 : Certificates.L43TwinQ8.q2b = dec X4) (hw : Certificates.L43TwinQ8.wc = dec W)
    (A B : ℕ) : Certificates.L43TwinQ8.pairOK (dec A) (dec B) = pairQ X1 X2 X3 X4 W A B := by
  unfold Certificates.L43TwinQ8.pairOK Certificates.L43TwinQ8.omega4Wit pairQ omegaQ
  rw [h1, h2, h3, h4, hw, CFSG.KC.Pack.strictB_eq, CFSG.KC.Pack.strictB_eq]
  simp only [conj_dec, inv_dec, eq_dec', sameQ8_dec, memQ8_dec, commutes_dec]

theorem ptQ_spec {n N : ℕ} {G T : ℕ → ℕ} {E : ℕ → ℕ → ℕ} {PA LA SO SOI : ℕ → ℕ} {i : ℕ}
    (h : ptQ n N G T E PA LA SO SOI i = true) :
    validQ (T i) = true ∧ CFSG.KS.SporSch.LyM.sortB (fun j => keyQ (T j)) SO SOI N i = true ∧
      (∀ k < n, E i k < N ∧ actQ (G k) (T i) = T (E i k) ∧
        (E i k = 0 ∨ posQ n PA LA (E i k) ≤ n * i + k)) ∧
      (i = 0 → T 0 = ONEQ ∧ PA 0 = 0 ∧ LA 0 = 0) ∧
      (i ≠ 0 → PA i < i ∧ LA i < n ∧ E (PA i) (LA i) = i ∧
        (i + 1 ≠ N → posQ n PA LA i < posQ n PA LA (i + 1))) := by
  unfold ptQ at h
  rw [CFSG.KC.Pack.strictB_eq] at h
  obtain ⟨h1, h⟩ := CFSG.KS.U43Pk.bAnd_spec h
  obtain ⟨h2, h⟩ := CFSG.KS.U43Pk.bAnd_spec h
  obtain ⟨h3, h4⟩ := CFSG.KS.U43Pk.bAnd_spec h
  refine ⟨h1, h2, fun k hk => ?_, fun hi => ?_, fun hi => ?_⟩
  · have e := CFSG.KC.Pack.allBlk_spec h3 k hk
    rw [Nat.add_eq, Nat.zero_add, CFSG.KC.Pack.strictB_eq] at e
    obtain ⟨e1, e⟩ := CFSG.KS.U43Pk.bAnd_spec e
    obtain ⟨e2, e3⟩ := CFSG.KS.U43Pk.bAnd_spec e
    refine ⟨Eq.mp Nat.blt_eq e1, Nat.eq_of_beq_eq_true e2, ?_⟩
    rw [CFSG.KS.U43Pk.bIf_eq] at e3
    by_cases h0 : E i k = 0
    · exact Or.inl h0
    · have hb : Nat.beq (E i k) 0 = false :=
        Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
      rw [hb] at e3
      simp only [Bool.false_eq_true, ↓reduceIte] at e3
      exact Or.inr (Nat.le_of_ble_eq_true e3)
  · subst hi
    rw [CFSG.KS.U43Pk.bIf_eq] at h4
    simp only [Nat.beq_refl, ↓reduceIte] at h4
    obtain ⟨e1, e⟩ := CFSG.KS.U43Pk.bAnd_spec h4
    obtain ⟨e2, e3⟩ := CFSG.KS.U43Pk.bAnd_spec e
    exact ⟨Nat.eq_of_beq_eq_true e1, Nat.eq_of_beq_eq_true e2, Nat.eq_of_beq_eq_true e3⟩
  · have hb : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun h => hi (Nat.eq_of_beq_eq_true h)
    rw [CFSG.KS.U43Pk.bIf_eq, hb] at h4
    simp only [Bool.false_eq_true, ↓reduceIte] at h4
    obtain ⟨e1, e⟩ := CFSG.KS.U43Pk.bAnd_spec h4
    obtain ⟨e2, e⟩ := CFSG.KS.U43Pk.bAnd_spec e
    obtain ⟨e3, e4⟩ := CFSG.KS.U43Pk.bAnd_spec e
    refine ⟨Eq.mp Nat.blt_eq e1, Eq.mp Nat.blt_eq e2, Nat.eq_of_beq_eq_true e3, fun hi' => ?_⟩
    rw [CFSG.KS.U43Pk.bIf_eq] at e4
    have hb' : Nat.beq (Nat.succ i) N = false :=
      Bool.eq_false_iff.2 fun h => hi' (Nat.eq_of_beq_eq_true h)
    rw [hb'] at e4
    simp only [Bool.false_eq_true, ↓reduceIte] at e4
    exact Eq.mp Nat.blt_eq e4

theorem act_dec (gens : Array (Array ℕ)) {k G P : ℕ} (hG : gens[k]! = dec G) :
    locAct 4 gens k (dec P) = dec (actQ G P) := by
  unfold locAct actQ
  rw [hG, mul_dec, norm_dec, CFSG.KC.Pack.strictN_eq]

theorem tables_of {n N : ℕ} {gens : Array (Array ℕ)} {G T : ℕ → ℕ} {E : ℕ → ℕ → ℕ}
    {PA LA SO SOI : ℕ → ℕ} (hN : 2 ≤ N) (hG : ∀ k < n, gens[k]! = dec (G k))
    (hpt : ∀ i < N, ptQ n N G T E PA LA SO SOI i = true) :
    Tables n N (locAct 4 gens) (eltKey 4) (fun i => dec (T i)) E PA LA ∧
      (∀ i < N, eltValid 4 (dec (T i)) = true) ∧ dec (T 0) = eltOne 4 := by
  have hs : ∀ i < N, CFSG.KS.SporSch.LyM.sortB (fun j => keyQ (T j)) SO SOI N i = true :=
    fun i hi => (ptQ_spec (hpt i hi)).2.1
  have hinj := CFSG.KS.SporSch.LyLoop.sortB_inj hs
  refine ⟨⟨hN, fun i hi k hk => ?_, fun a ha b hb e => ?_, ?_, ?_, fun j hj1 hjN => ?_,
    fun j hj1 hjN => ?_, fun i hi k hk => ?_⟩, fun i hi => ?_, ?_⟩
  · obtain ⟨e1, e2, -⟩ := (ptQ_spec (hpt i hi)).2.2.1 k hk
    exact ⟨e1, by rw [act_dec gens (hG k hk), e2]⟩
  · refine hinj a ha b hb ?_
    have e' : eltKey 4 (dec (T a)) = eltKey 4 (dec (T b)) := e
    rwa [key_dec, key_dec] at e'
  · exact ((ptQ_spec (hpt 0 (by omega))).2.2.2.1 rfl).2.1
  · exact ((ptQ_spec (hpt 0 (by omega))).2.2.2.1 rfl).2.2
  · obtain ⟨h1, h2, h3, -⟩ := (ptQ_spec (hpt j hjN)).2.2.2.2 (by omega)
    exact ⟨h1, h2, h3⟩
  · obtain ⟨-, -, -, h4⟩ := (ptQ_spec (hpt j (by omega))).2.2.2.2 (by omega)
    exact h4 (by omega)
  · exact ((ptQ_spec (hpt i hi)).2.2.1 k hk).2.2
  · rw [valid_dec]
    exact (ptQ_spec (hpt i hi)).1
  · rw [((ptQ_spec (hpt 0 (by omega))).2.2.2.1 rfl).1, one_dec]

end CFSG.KS.L43Q8

end
