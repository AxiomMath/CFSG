module

public import Certificates.Data.Kernel.U43Pk.Defs
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocU43Check
public import CFSG.Certificates.Kernel.ArrBfsSim
import CFSG.Certificates.Kernel.PackSetSound
import CFSG.Certificates.Kernel.SporSch.LyLoop

public section

namespace CFSG.KS.U43Pk

open CFSG.KD.U43Pk CFSG.KC.Enum CFSG.KC.Pack CFSG.KS.ArrBfsSim
open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check

@[expose] noncomputable def dec (P : ℕ) : Array ℕ := Array.ofFn (n := 17) fun j => dg P j

theorem dg_eq (P j : ℕ) : dg P j = P / 16 ^ j % 16 := by
  have h1 : Nat.shiftLeft j 2 = 4 * j := by
    change j <<< 2 = _
    rw [Nat.shiftLeft_eq]
    ring
  have h2 : (16 : ℕ) ^ j = 2 ^ (4 * j) := by
    rw [pow_mul]
    norm_num
  unfold dg
  rw [h1, h2]
  change (P >>> (4 * j)) &&& (2 ^ 4 - 1) = _
  rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]

theorem dg_lt (P j : ℕ) : dg P j < 16 := by
  rw [dg_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem dg_of_lt {a m j : ℕ} (ha : a < 16 ^ m) (hj : m ≤ j) : dg a j = 0 := by
  rw [dg_eq, Nat.div_eq_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hj))]

theorem dg_add_mul {a n : ℕ} (b j : ℕ) (ha : a < 16 ^ n) :
    dg (a + 16 ^ n * b) j = if j < n then dg a j else dg b (j - n) := by
  have h16 : 0 < (16 : ℕ) ^ j := by positivity
  split_ifs with hj
  · rw [dg_eq, dg_eq]
    obtain ⟨t, rfl⟩ : ∃ t, n = j + 1 + t := ⟨n - j - 1, by omega⟩
    have e : a + 16 ^ (j + 1 + t) * b = a + 16 ^ j * (16 * (16 ^ t * b)) := by ring
    rw [e, Nat.add_mul_div_left _ _ h16, Nat.add_mul_mod_self_left]
  · rw [dg_eq, dg_eq]
    obtain ⟨t, rfl⟩ : ∃ t, j = n + t := ⟨j - n, by omega⟩
    rw [Nat.add_sub_cancel_left, pow_add, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt ha, Nat.zero_add]

theorem dg_shr (X m d : ℕ) : dg (Nat.shiftRight X (Nat.shiftLeft m 2)) d = dg X (m + d) := by
  have h1 : Nat.shiftLeft m 2 = 4 * m := by
    change m <<< 2 = _
    rw [Nat.shiftLeft_eq]
    ring
  have h2 : (2 : ℕ) ^ (4 * m) = 16 ^ m := by
    rw [pow_mul]
    norm_num
  rw [dg_eq, dg_eq, h1]
  change X >>> (4 * m) / 16 ^ d % 16 = _
  rw [Nat.shiftRight_eq_div_pow, h2, Nat.div_div_eq_div_mul, ← pow_add]

theorem digits_eq : ∀ (n P Q : ℕ), P < 16 ^ n → Q < 16 ^ n → (∀ j < n, dg P j = dg Q j) → P = Q
  | 0, P, Q, hP, hQ, _ => by simp at hP hQ; omega
  | n + 1, P, Q, hP, hQ, h => by
    have h0 := h 0 (by omega)
    rw [dg_eq, dg_eq, pow_zero, Nat.div_one, Nat.div_one] at h0
    have hd : P / 16 = Q / 16 := digits_eq n (P / 16) (Q / 16)
      (by rw [pow_succ] at hP; omega) (by rw [pow_succ] at hQ; omega) fun j hj => by
        have e := h (j + 1) (by omega)
        rwa [dg_eq, dg_eq, pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
          ← dg_eq, ← dg_eq] at e
    omega

theorem shl_eq (a k : ℕ) : Nat.shiftLeft a (Nat.shiftLeft k 2) = 16 ^ k * a := by
  have h1 : Nat.shiftLeft k 2 = 4 * k := by
    change k <<< 2 = _
    rw [Nat.shiftLeft_eq]
    ring
  rw [h1]
  change a <<< (4 * k) = _
  rw [Nat.shiftLeft_eq, pow_mul]
  norm_num
  ring

@[expose] noncomputable def packN (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun k acc => strictN acc fun a => Nat.add a (Nat.shiftLeft (f k) (Nat.shiftLeft k 2))) n

theorem packN_succ (f : ℕ → ℕ) (n : ℕ) : packN f (n + 1) = packN f n + 16 ^ n * f n := by
  change strictN (packN f n) (fun a => Nat.add a (Nat.shiftLeft (f n) (Nat.shiftLeft n 2))) = _
  rw [CFSG.KC.Pack.strictN_eq, Nat.add_eq, shl_eq]

theorem packK_go {f : ℕ → ℕ} (hf : ∀ k, f k < 16) : ∀ n,
    packN f n < 16 ^ n ∧ ∀ j, dg (packN f n) j = if j < n then f j else 0
  | 0 => ⟨by simp [packN], fun j => by simp [packN, dg_eq]⟩
  | n + 1 => by
    obtain ⟨hlt, hdg⟩ := packK_go hf n
    rw [packN_succ]
    refine ⟨?_, fun j => ?_⟩
    · have h1 : 16 ^ n * f n ≤ 16 ^ n * 15 := Nat.mul_le_mul_left _ (by have := hf n; omega)
      rw [pow_succ]
      generalize 16 ^ n = X at *
      omega
    · rw [dg_add_mul _ _ hlt, hdg]
      by_cases hj : j < n
      · simp [hj, show j < n + 1 by omega]
      · simp only [hj, ↓reduceIte]
        by_cases hjn : j = n
        · subst hjn
          simp [dg_eq, Nat.mod_eq_of_lt (hf j)]
        · rw [if_neg (by omega), dg_of_lt (m := 1) (by simpa using hf n) (by omega)]

theorem packK_lt {f : ℕ → ℕ} (hf : ∀ k, f k < 16) : packK f < 16 ^ 16 := (packK_go hf 16).1

theorem dg_packK {f : ℕ → ℕ} (hf : ∀ k, f k < 16) (j : ℕ) :
    dg (packK f) j = if j < 16 then f j else 0 := (packK_go hf 16).2 j

theorem dg_pack16 {f : ℕ → ℕ} (hf : ∀ k, f k < 16) {e : ℕ} (he : e < 16) (j : ℕ) :
    dg (Nat.add (packK f) (Nat.shiftLeft e 64)) j =
      if j < 16 then f j else if j = 16 then e else 0 := by
  have h : Nat.shiftLeft e 64 = 16 ^ 16 * e := by
    have := shl_eq e 16
    rwa [show Nat.shiftLeft 16 2 = 64 from rfl] at this
  rw [Nat.add_eq, h, dg_add_mul _ _ (packK_lt hf)]
  split_ifs with h1 h2
  · rw [dg_packK hf j, if_pos h1]
  · subst h2
    simp [dg_eq, Nat.mod_eq_of_lt he]
  · exact dg_of_lt (m := 1) (by simpa using he) (by omega)

theorem ofFn_get {n : ℕ} (f : Fin n → ℕ) {k : ℕ} (hk : k < n) : (Array.ofFn f)[k]! = f ⟨k, hk⟩ := by
  rw [getElem!_pos (Array.ofFn f) k (by rw [Array.size_ofFn]; exact hk), Array.getElem_ofFn]

theorem push_get_lt (A : Array ℕ) (v : ℕ) {k : ℕ} (hk : k < A.size) : (A.push v)[k]! = A[k]! := by
  rw [getElem!_pos (A.push v) k (by rw [Array.size_push]; omega), getElem!_pos A k hk,
    Array.getElem_push_lt]

theorem push_get_eq (A : Array ℕ) (v : ℕ) {k : ℕ} (hk : k = A.size) : (A.push v)[k]! = v := by
  subst hk
  rw [getElem!_pos (A.push v) A.size (by rw [Array.size_push]; omega), Array.getElem_push_eq]

theorem dec_size (P : ℕ) : (dec P).size = 17 := by simp [dec]

theorem dec_get (P : ℕ) {k : ℕ} (hk : k < 17) : (dec P)[k]! = dg P k := by
  unfold dec
  rw [ofFn_get _ hk]

theorem eq_dec {x : Array ℕ} {P : ℕ} (hs : x.size = 17) (h : ∀ k < 17, x[k]! = dg P k) :
    x = dec P := by
  apply Array.ext
  · rw [hs, dec_size]
  · intro k h1 h2
    have hk : k < 17 := by rw [hs] at h1; exact h1
    rw [← getElem!_pos x k h1, h k hk]
    exact (Array.getElem_ofFn (f := fun j : Fin 17 => dg P j) h2).symm

theorem mT_eq : ∀ c < 9, ∀ d < 9, mT c d = mulC c d := by decide +kernel

theorem aT_eq : ∀ c < 9, ∀ d < 9, aT c d = addC c d := by decide +kernel

theorem bT_eq : ∀ c < 9, dg BT c = barC c := by decide +kernel

theorem mcT_eq : ∀ u < 9, dg MCT u = mC u := by decide +kernel

theorem mC_lt : ∀ u < 9, mC u < 9 := by decide +kernel

theorem mulC_lt (c d : ℕ) : mulC c d < 9 := by unfold mulC; omega

theorem addC_lt (c d : ℕ) : addC c d < 9 := by unfold addC; omega

theorem barC_lt (c : ℕ) : barC c < 9 := by unfold barC reC imC; omega

@[expose] def Dig (P : ℕ) : Prop := ∀ j < 16, dg P j < 9

theorem entK_eq {G Y : ℕ} (hG : Dig G) (hY : Dig Y) {i j : ℕ} (hi : i < 4) (hj : j < 4) :
    entK G Y i j = addC (addC (addC (mulC (dg G (4 * i)) (dg Y j))
      (mulC (dg G (4 * i + 1)) (dg Y (4 + j)))) (mulC (dg G (4 * i + 2)) (dg Y (8 + j))))
      (mulC (dg G (4 * i + 3)) (dg Y (12 + j))) := by
  unfold entK
  simp only [Nat.mul_eq, Nat.add_eq]
  rw [mT_eq _ (hG _ (by omega)) _ (hY _ (by omega)), mT_eq _ (hG _ (by omega)) _ (hY _ (by omega)),
    mT_eq _ (hG _ (by omega)) _ (hY _ (by omega)), mT_eq _ (hG _ (by omega)) _ (hY _ (by omega)),
    aT_eq _ (mulC_lt _ _) _ (mulC_lt _ _), aT_eq _ (addC_lt _ _) _ (mulC_lt _ _),
    aT_eq _ (addC_lt _ _) _ (mulC_lt _ _)]

theorem entK_lt (G Y i j : ℕ) : entK G Y i j < 16 := dg_lt _ _

theorem dg_matK {G Y : ℕ} (hG : Dig G) (hY : Dig Y) {k : ℕ} (hk : k < 16) :
    dg (matK G Y) k = addC (addC (addC (mulC (dg G (4 * (k / 4))) (dg Y (k % 4)))
      (mulC (dg G (4 * (k / 4) + 1)) (dg Y (4 + k % 4))))
      (mulC (dg G (4 * (k / 4) + 2)) (dg Y (8 + k % 4))))
      (mulC (dg G (4 * (k / 4) + 3)) (dg Y (12 + k % 4))) := by
  unfold matK
  rw [dg_packK (fun k => entK_lt _ _ _ _), if_pos hk]
  change entK G Y (k / 4) (k % 4) = _
  exact entK_eq hG hY (by omega) (by omega)

theorem matK_dig {G Y : ℕ} (hG : Dig G) (hY : Dig Y) : Dig (matK G Y) := fun k hk => by
  rw [dg_matK hG hY hk]
  exact addC_lt _ _

theorem matK_lt (G Y : ℕ) : matK G Y < 16 ^ 16 := packK_lt fun k => entK_lt _ _ _ _

theorem mulMat_dec {G P Y : ℕ} {sw : Bool} (hG : Dig G) (hY : Dig Y)
    (hsw : ∀ j < 16, (if sw then barC (dg P j) else dg P j) = dg Y j) :
    mulMat (dec G) (dec P) sw = Array.ofFn (n := 16) fun k => dg (matK G Y) k := by
  unfold mulMat
  congr 1
  funext k
  have hk := k.2
  rw [dg_matK hG hY hk]
  unfold mulEntry
  have g : ∀ t < 16, (dec G)[t]! = dg G t := fun t ht => dec_get G (by omega)
  have p : ∀ t < 16, (if sw then barC (dec P)[t]! else (dec P)[t]!) = dg Y t := fun t ht => by
    rw [dec_get P (by omega)]
    exact hsw t ht
  rw [g _ (by omega), g _ (by omega), g _ (by omega), g _ (by omega), p _ (by omega),
    p _ (by omega), p _ (by omega), p _ (by omega)]

theorem dig_mapBT {P : ℕ} (hP : Dig P) : Dig (mapK BT P) := fun j hj => by
  unfold mapK
  rw [dg_packK (fun k => dg_lt _ _), if_pos hj, bT_eq _ (hP j hj)]
  exact barC_lt _

theorem dg_mapBT {P : ℕ} (hP : Dig P) {j : ℕ} (hj : j < 16) : dg (mapK BT P) j = barC (dg P j) := by
  unfold mapK
  rw [dg_packK (fun k => dg_lt _ _), if_pos hj, bT_eq _ (hP j hj)]

theorem mulK_eq (G P : ℕ) : mulK G P =
    Nat.add (matK G (if dg G 16 = 1 then mapK BT P else P))
      (Nat.shiftLeft (Nat.mod (Nat.add (dg G 16) (dg P 16)) 2) 64) := by
  unfold mulK
  rw [CFSG.KC.Pack.strictN_eq]
  by_cases h : dg G 16 = 1
  · rw [if_pos h, h]
    rfl
  · rw [if_neg h]
    have : Nat.beq (dg G 16) 1 = false :=
      Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
    rw [this]

theorem mulRaw_dec {G P : ℕ} (hG : Dig G) (hP : Dig P) :
    mulRaw (dec G) (dec P) = dec (mulK G P) := by
  set Y := if dg G 16 = 1 then mapK BT P else P with hYd
  have hY : Dig Y := by
    rw [hYd]
    split_ifs
    · exact dig_mapBT hP
    · exact hP
  have hsw : ∀ j < 16, (if (dec G)[16]! == 1 then barC (dg P j) else dg P j) = dg Y j := by
    intro j hj
    rw [dec_get G (by omega), hYd]
    by_cases h : dg G 16 = 1
    · simp [h, dg_mapBT hP hj]
    · simp [h]
  have hm := mulMat_dec hG hY hsw
  have hdg := dg_pack16 (f := fun k => entK G Y (Nat.div k 4) (Nat.mod k 4))
    (fun k => entK_lt _ _ _ _) (e := (dg G 16 + dg P 16) % 2) (by omega)
  have hmul : mulK G P = Nat.add (packK fun k => entK G Y (Nat.div k 4) (Nat.mod k 4))
      (Nat.shiftLeft ((dg G 16 + dg P 16) % 2) 64) := by
    rw [mulK_eq]
    rfl
  apply eq_dec (by simp [mulRaw, mulMat])
  intro k hk
  unfold mulRaw
  rw [hm, hmul, hdg]
  by_cases h16 : k < 16
  · rw [push_get_lt _ _ (by simpa using h16), ofFn_get _ h16, if_pos h16]
    have := dg_matK hG hY h16
    unfold matK at this
    rw [dg_packK (fun k => entK_lt _ _ _ _), if_pos h16] at this
    rw [this, dg_matK hG hY h16]
  · have hk16 : k = 16 := by omega
    subst hk16
    rw [push_get_eq _ _ (by simp), dec_get G (by omega), dec_get P (by omega), if_neg (by omega),
      if_pos rfl]

theorem mulK_dig {G P : ℕ} (hG : Dig G) (hP : Dig P) : Dig (mulK G P) := fun j hj => by
  have h : (mulRaw (dec G) (dec P))[j]! = (dec (mulK G P))[j]! := by rw [mulRaw_dec hG hP]
  rw [dec_get _ (by omega)] at h
  rw [← h]
  unfold mulRaw
  rw [push_get_lt _ _ (by simp [mulMat]; omega)]
  unfold mulMat
  rw [ofFn_get _ hj]
  unfold mulEntry
  exact addC_lt _ _

theorem fnz_go (R : ℕ) : ∀ m ≤ 16,
    Nat.rec (motive := fun _ => ℕ) 0
      (fun k acc => strictN (dg R (Nat.sub 15 k)) fun v => Bool.rec (motive := fun _ => ℕ) v acc
        (Nat.beq v 0)) m =
      (((List.range' (16 - m) m).map (dg R)).find? fun w => decide (w ≠ 0)).getD 0
  | 0, _ => rfl
  | m + 1, hm => by
    change strictN _ _ = _
    rw [CFSG.KC.Pack.strictN_eq, fnz_go R m (by omega)]
    have e : 16 - (m + 1) = 15 - m := by omega
    have e' : 15 - m + 1 = 16 - m := by omega
    rw [e, List.range'_succ, e', List.map_cons, Nat.sub_eq]
    by_cases h : dg R (15 - m) = 0
    · have hb : Nat.beq (dg R (15 - m)) 0 = true := by rw [h]; rfl
      rw [hb]
      simp [List.find?_cons, h]
    · have hb : Nat.beq (dg R (15 - m)) 0 = false :=
        Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
      rw [hb]
      simp [List.find?_cons, h]

theorem fnzK_go (R : ℕ) :
    fnzK R = (((List.range' (16 - 16) 16).map (dg R)).find? fun w => decide (w ≠ 0)).getD 0 :=
  fnz_go R 16 le_rfl

theorem fnzK_eq (R : ℕ) : fnzK R = firstNZ (dec R) := by
  have h2 : ((List.range 16).map fun k => (dec R)[k]!) = (List.range' (16 - 16) 16).map (dg R) := by
    rw [Nat.sub_self, ← List.range_eq_range']
    exact List.map_congr_left fun k hk => dec_get R (by rw [List.mem_range] at hk; omega)
  rw [fnzK_go]
  unfold firstNZ
  rw [h2]

theorem fnzK_lt {R : ℕ} (hR : Dig R) : fnzK R < 9 := by
  rw [fnzK_go]
  cases h : ((List.range' (16 - 16) 16).map (dg R)).find? fun w => decide (w ≠ 0) with
  | none => simp
  | some a =>
    have hm := List.mem_of_find?_eq_some h
    simp only [List.mem_map, List.mem_range'] at hm
    obtain ⟨k, hk, rfl⟩ := hm
    exact hR k (by omega)

theorem normalize_dec {R : ℕ} (hR : Dig R) : normalize (dec R) = dec (nrmK R) := by
  have hc := fnzK_lt hR
  set c := mC (fnzK R) with hcd
  have hc9 : c < 9 := mC_lt _ hc
  have hn : nrmK R = Nat.add (mapK (Nat.shiftRight MT (Nat.shiftLeft (Nat.mul 9 c) 2)) R)
      (Nat.shiftLeft (dg R 16) 64) := by
    unfold nrmK
    rw [CFSG.KC.Pack.strictN_eq, mcT_eq _ hc]
  unfold normalize
  rw [← fnzK_eq, hn]
  apply eq_dec (by simp [smulCode])
  intro k hk
  unfold mapK
  rw [dg_pack16 (fun k => dg_lt _ _) (dg_lt _ _)]
  unfold smulCode
  rw [ofFn_get _ hk]
  by_cases h16 : k < 16
  · simp only [h16, ↓reduceIte, ← hcd]
    rw [dg_shr, dec_get R hk, ← mT_eq _ hc9 _ (hR k h16)]
    rfl
  · have : k = 16 := by omega
    subst this
    simp [dec_get R (show 16 < 17 by omega)]

theorem act_dec {G P : ℕ} (hG : Dig G) (hP : Dig P) :
    normalize (mulRaw (dec G) (dec P)) = dec (actK G P) := by
  rw [mulRaw_dec hG hP, normalize_dec (mulK_dig hG hP)]
  unfold actK
  rw [CFSG.KC.Pack.strictN_eq]

theorem conjT_dec {P : ℕ} (hP : Dig P) : conjT (dec P) = dec (conjTK P) := by
  apply eq_dec (by simp [conjT])
  intro k hk
  unfold conjT conjTK
  rw [ofFn_get _ hk, dg_packK (fun k => dg_lt _ _)]
  dsimp only
  have e : Nat.add (Nat.mul 4 (Nat.mod k 4)) (Nat.div k 4) = 4 * (k % 4) + k / 4 := rfl
  rw [e]
  by_cases h16 : k < 16
  · rw [if_pos h16, if_pos h16, dec_get P (by omega), bT_eq _ (hP _ (by omega))]
  · rw [if_neg h16, if_neg h16]

theorem conjTK_dig (P : ℕ) (hP : Dig P) : Dig (conjTK P) := fun j hj => by
  unfold conjTK
  rw [dg_packK (fun k => dg_lt _ _), if_pos hj]
  have e : Nat.add (Nat.mul 4 (Nat.mod j 4)) (Nat.div j 4) = 4 * (j % 4) + j / 4 := rfl
  rw [e, bT_eq _ (hP _ (by omega))]
  exact barC_lt _

theorem bAnd_spec {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := CFSG.KC.Pack.band_iff.1 h

theorem rawValidK_spec {P : ℕ} (h : rawValidK P = true) :
    P < 16 ^ 17 ∧ Dig P ∧ dg P 16 < 2 ∧ matK (conjTK P) P = IDK := by
  unfold rawValidK at h
  obtain ⟨h1, h⟩ := bAnd_spec h
  obtain ⟨h2, h⟩ := bAnd_spec h
  obtain ⟨h3, h4⟩ := bAnd_spec h
  refine ⟨?_, fun j hj => ?_, Eq.mp Nat.blt_eq h3, Nat.eq_of_beq_eq_true h4⟩
  · have e := Nat.eq_of_beq_eq_true h1
    change P >>> 68 = 0 at e
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff] at e
    rcases e with e | e
    · norm_num at e
    · have : (2 : ℕ) ^ 68 = 16 ^ 17 := by norm_num
      omega
  · have := CFSG.KC.Pack.allBlk_spec h2 j hj
    rw [Nat.add_eq, Nat.zero_add] at this
    exact Eq.mp Nat.blt_eq this

theorem idMat_eq : (Array.ofFn (n := 16) fun k => dg IDK k) = idMat := by decide +kernel

theorem rawValid_dec {P : ℕ} (h : rawValidK P = true) : rawValid (dec P) = true := by
  obtain ⟨-, hd, he, hm⟩ := rawValidK_spec h
  have hmm : mulMat (conjT (dec P)) (dec P) false = idMat := by
    rw [conjT_dec hd, mulMat_dec (conjTK_dig P hd) hd (fun j hj => by simp), hm, idMat_eq]
  unfold rawValid
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨dec_size P, fun k hk => ?_⟩, ?_⟩, hmm⟩
  · rw [dec_get P (by omega)]
    exact hd k hk
  · rw [dec_get P (by omega)]
    exact he

theorem validK_spec {P : ℕ} (h : validK P = true) :
    rawValidK P = true ∧ nrmK P = P := by
  unfold validK at h
  obtain ⟨h1, h2⟩ := bAnd_spec h
  exact ⟨h1, Nat.eq_of_beq_eq_true h2⟩

theorem valid_dec {P : ℕ} (h : validK P = true) : valid (dec P) = true := by
  obtain ⟨h1, h2⟩ := validK_spec h
  have hd := (rawValidK_spec h1).2.1
  unfold valid
  rw [rawValid_dec h1, normalize_dec hd, h2]
  simp

theorem dec_digits {P : ℕ} (h : rawValidK P = true) : ∀ l ∈ (dec P).toList, l < 9 := by
  obtain ⟨-, hd, he, -⟩ := rawValidK_spec h
  intro l hl
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
  have hi' : i < 17 := by simpa [dec_size] using hi
  rw [Array.getElem_toList, ← getElem!_pos (dec P) i (by rw [dec_size]; exact hi'),
    dec_get P hi']
  by_cases h16 : i < 16
  · exact hd i h16
  · have : i = 16 := by omega
    subst this
    omega

theorem keyOf_dec_inj {P Q : ℕ} (hP : rawValidK P = true) (hQ : rawValidK Q = true)
    (h : keyOf (dec P) = keyOf (dec Q)) : P = Q := by
  have hl := Nat.ofDigits_inj_of_len_eq (b := 9) (by norm_num)
    (by rw [Array.length_toList, Array.length_toList, dec_size, dec_size]) (dec_digits hP)
    (dec_digits hQ) h
  have ha : dec P = dec Q := Array.toList_inj.1 hl
  refine digits_eq 17 P Q (rawValidK_spec hP).1 (rawValidK_spec hQ).1 fun j hj => ?_
  rw [← dec_get P hj, ← dec_get Q hj, ha]

theorem bIf_eq (c t e : Bool) : Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem ptK_spec {n N : ℕ} {G T : ℕ → ℕ} {E : ℕ → ℕ → ℕ} {PA LA SO SOI : ℕ → ℕ} {i : ℕ}
    (h : ptK n N G T E PA LA SO SOI i = true) :
    validK (T i) = true ∧ CFSG.KS.SporSch.LyM.sortB T SO SOI N i = true ∧
      (∀ k < n, E i k < N ∧ actK (G k) (T i) = T (E i k) ∧
        (E i k = 0 ∨ posK n PA LA (E i k) ≤ n * i + k)) ∧
      (i = 0 → T 0 = IDK ∧ PA 0 = 0 ∧ LA 0 = 0) ∧
      (i ≠ 0 → PA i < i ∧ LA i < n ∧ E (PA i) (LA i) = i ∧
        (i + 1 ≠ N → posK n PA LA i < posK n PA LA (i + 1))) := by
  unfold ptK at h
  rw [CFSG.KC.Pack.strictB_eq] at h
  obtain ⟨h1, h⟩ := bAnd_spec h
  obtain ⟨h2, h⟩ := bAnd_spec h
  obtain ⟨h3, h4⟩ := bAnd_spec h
  refine ⟨h1, h2, fun k hk => ?_, fun hi => ?_, fun hi => ?_⟩
  · have e := CFSG.KC.Pack.allBlk_spec h3 k hk
    rw [Nat.add_eq, Nat.zero_add, CFSG.KC.Pack.strictB_eq] at e
    obtain ⟨e1, e⟩ := bAnd_spec e
    obtain ⟨e2, e3⟩ := bAnd_spec e
    refine ⟨Eq.mp Nat.blt_eq e1, Nat.eq_of_beq_eq_true e2, ?_⟩
    rw [bIf_eq] at e3
    by_cases h0 : E i k = 0
    · exact Or.inl h0
    · have hb : Nat.beq (E i k) 0 = false :=
        Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
      rw [hb] at e3
      simp only [Bool.false_eq_true, ↓reduceIte] at e3
      exact Or.inr (Nat.le_of_ble_eq_true e3)
  · subst hi
    rw [bIf_eq] at h4
    simp only [Nat.beq_refl, ↓reduceIte] at h4
    obtain ⟨e1, e⟩ := bAnd_spec h4
    obtain ⟨e2, e3⟩ := bAnd_spec e
    exact ⟨Nat.eq_of_beq_eq_true e1, Nat.eq_of_beq_eq_true e2, Nat.eq_of_beq_eq_true e3⟩
  · have hb : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun h => hi (Nat.eq_of_beq_eq_true h)
    rw [bIf_eq, hb] at h4
    simp only [Bool.false_eq_true, ↓reduceIte] at h4
    obtain ⟨e1, e⟩ := bAnd_spec h4
    obtain ⟨e2, e⟩ := bAnd_spec e
    obtain ⟨e3, e4⟩ := bAnd_spec e
    refine ⟨Eq.mp Nat.blt_eq e1, Eq.mp Nat.blt_eq e2, Nat.eq_of_beq_eq_true e3, fun hi' => ?_⟩
    rw [bIf_eq] at e4
    have hb' : Nat.beq (Nat.succ i) N = false :=
      Bool.eq_false_iff.2 fun h => hi' (Nat.eq_of_beq_eq_true h)
    rw [hb'] at e4
    simp only [Bool.false_eq_true, ↓reduceIte] at e4
    exact Eq.mp Nat.blt_eq e4

theorem idCode_eq : dec IDK = idCode := by decide +kernel

theorem tables_of {n N : ℕ} {gens : Array (Array ℕ)} {G T : ℕ → ℕ} {E : ℕ → ℕ → ℕ}
    {PA LA SO SOI : ℕ → ℕ} (hN : 2 ≤ N) (hG : ∀ k < n, gens[k]! = dec (G k))
    (hGv : ∀ k < n, rawValidK (G k) = true)
    (hpt : ∀ i < N, ptK n N G T E PA LA SO SOI i = true) :
    Tables n N (act gens) keyOf (fun i => dec (T i)) E PA LA ∧
      (∀ i < N, valid (dec (T i)) = true) ∧ dec (T 0) = idCode := by
  have hs : ∀ i < N, CFSG.KS.SporSch.LyM.sortB T SO SOI N i = true := fun i hi =>
    (ptK_spec (hpt i hi)).2.1
  have hinj := CFSG.KS.SporSch.LyLoop.sortB_inj hs
  have hv : ∀ i < N, validK (T i) = true := fun i hi => (ptK_spec (hpt i hi)).1
  have hr : ∀ i < N, rawValidK (T i) = true := fun i hi => (validK_spec (hv i hi)).1
  refine ⟨⟨hN, fun i hi k hk => ?_, fun a ha b hb e => ?_, ?_, ?_, fun j hj1 hjN => ?_,
    fun j hj1 hjN => ?_, fun i hi k hk => ?_⟩, fun i hi => valid_dec (hv i hi), ?_⟩
  · obtain ⟨e1, e2, -⟩ := (ptK_spec (hpt i hi)).2.2.1 k hk
    refine ⟨e1, ?_⟩
    unfold act
    rw [hG k hk, act_dec (rawValidK_spec (hGv k hk)).2.1 (rawValidK_spec (hr i hi)).2.1, e2]
  · exact hinj a ha b hb (keyOf_dec_inj (hr a ha) (hr b hb) e)
  · exact ((ptK_spec (hpt 0 (by omega))).2.2.2.1 rfl).2.1
  · exact ((ptK_spec (hpt 0 (by omega))).2.2.2.1 rfl).2.2
  · obtain ⟨h1, h2, h3, -⟩ := (ptK_spec (hpt j hjN)).2.2.2.2 (by omega)
    exact ⟨h1, h2, h3⟩
  · obtain ⟨-, -, -, h4⟩ := (ptK_spec (hpt j (by omega))).2.2.2.2 (by omega)
    exact h4 (by omega)
  · exact ((ptK_spec (hpt i hi)).2.2.1 k hk).2.2
  · rw [((ptK_spec (hpt 0 (by omega))).2.2.2.1 rfl).1, idCode_eq]

end CFSG.KS.U43Pk

end
