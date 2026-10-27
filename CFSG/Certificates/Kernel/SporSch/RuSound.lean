module

public import Certificates.Data.Kernel.SporSch.RuK
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.SporSch.DerivsSound
public import CFSG.Certificates.Kernel.Spor.TextSound
public import CFSG.Sporadic.Schreier.RuCheckBasicInputs
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.HexText
import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] noncomputable def encRow (r : SlotRow) : Nat × Nat × Nat × Nat :=
  SlotRow.rec (motive := fun _ => Nat × Nat × Nat × Nat) (fun i j k => (0, i, j, k))
    (fun i j => (1, i, j, 0)) (fun e i j => (2, e, i, j)) r

@[expose] noncomputable def encRows (rows : List SlotRow) : List (Nat × Nat × Nat × Nat) :=
  List.rec (motive := fun _ => List (Nat × Nat × Nat × Nat)) []
    (fun r _ ih => encRow r :: ih) rows

private theorem unpack_get₀ {n w p i : Nat} (hi : i < n) :
    (unpack n w p)[i]! = pg w (mask w) p i := by
  rw [unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

private theorem compA_unpack₀ {n w p q : Nat} (hn : n < 2 ^ 32) (hp : p >>> (n * w) = 0) :
    compA n (unpack n w p) (unpack n w q) = unpack n w (pcomp n w (mask w) p q) := by
  apply Array.ext
  · simp [compA, unpack]
  · intro i h1 _
    have hi : i < n := by simpa [compA] using h1
    simp only [compA, Array.getElem_ofFn]
    rw [unpack_get₀ hi]
    simp only [unpack, Array.getElem_ofFn]
    rw [PackFld.pg_pcomp hn hi]
    by_cases hx : pg w (mask w) q i < n
    · rw [← unpack, unpack_get₀ hx]
    · have e : pg w (mask w) p (pg w (mask w) q i) =
          (p >>> (w * pg w (mask w) q i)) &&& mask w := rfl
      have h0 : p >>> (w * pg w (mask w) q i) = 0 := by
        have hm := Nat.mul_le_mul_left w (Nat.le_of_not_lt hx)
        have h1 : w * pg w (mask w) q i = n * w + (w * pg w (mask w) q i - n * w) := by
          rw [Nat.mul_comm n w]
          omega
        rw [h1, Nat.shiftRight_add, hp, Nat.zero_shiftRight]
      rw [getElem!_neg _ _ (by simpa using hx), e, h0, Nat.zero_and]
      rfl

private abbrev Lo (p : Nat) : Prop := p >>> (4060 * 12) = 0

private theorem mulP_eq {p q : Nat} (hp : Lo p) :
    compA 4060 (unpack 4060 12 p) (unpack 4060 12 q) = unpack 4060 12 (CFSG.KC.Misc.RuInv.mulP p q) ∧
      Lo (CFSG.KC.Misc.RuInv.mulP p q) := by
  have e : CFSG.KC.Misc.RuInv.mulP p q = pcomp 4060 12 (mask 12) p q := rfl
  have hn : (4060 : Nat) < 2 ^ 32 := by norm_num
  rw [e]
  exact ⟨compA_unpack₀ (w := 12) hn hp, PackFld.pcomp_shr (w := 12) hn (by norm_num)⟩

private theorem unpack_pidn₀ {n w : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) :
    unpack n w (pidn n w) = idA n := by
  apply Array.ext
  · simp [unpack, idA]
  · intro i h1 _
    have hi : i < n := by simpa [unpack] using h1
    simp only [idA, Array.getElem_ofFn]
    rw [← getElem!_pos (unpack n w (pidn n w)) i h1, unpack_get₀ hi]
    exact PF.pg_pidn hn hw hi

private theorem unpack_idP : unpack 4060 12 CFSG.KC.Misc.RuInv.idP = idA 4060 := by
  unfold CFSG.KC.Misc.RuInv.idP
  exact unpack_pidn₀ (by norm_num) (by norm_num)

private theorem powP_eq {p : Nat} (hp : Lo p) : ∀ e,
    unpack 4060 12 (CFSG.KC.Misc.RuInv.powP p e) = powA 4060 (unpack 4060 12 p) e ∧
      Lo (CFSG.KC.Misc.RuInv.powP p e)
  | 0 => ⟨unpack_idP, PF.pidn_shr (n := 4060) (w := 12) (by norm_num) (by norm_num)⟩
  | e + 1 => by
    have h : CFSG.KC.Misc.RuInv.powP p (e + 1) =
        CFSG.KC.Misc.RuInv.mulP p (CFSG.KC.Misc.RuInv.powP p e) :=
      PackFld.strictN_eqP _ _
    obtain ⟨ih1, _⟩ := powP_eq hp e
    obtain ⟨m1, m2⟩ := mulP_eq (q := CFSG.KC.Misc.RuInv.powP p e) hp
    rw [h]
    refine ⟨?_, m2⟩
    rw [← m1, ih1]
    rfl

private theorem perm_lo {p q : Nat} (h : permOK 4060 12 (mask 12) (4060 * 12) p q = true) :
    Lo p ∧ Lo q := by
  unfold permOK at h
  simp only [bAnd_iff] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2.1⟩

private theorem readI_cons (a b : Nat) (s : List (Nat × Nat)) (k : Nat) :
    readI ((a, b) :: s) k = if a = k then b else readI s k := by
  change nIf(Nat.beq a k, b, readI s k) = _
  by_cases h : a = k
  · rw [ite_eq_left h, h, Nat.beq_refl]
  · rw [ite_eq_right h]
    cases e : Nat.beq a k
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) h

private theorem slotReadA_cons (a : Nat) (x : Array Nat) (l : List (Nat × Array Nat)) (k : Nat) :
    slotReadA 4060 ((a, x) :: l) k = if a = k then x else slotReadA 4060 l k := by
  unfold slotReadA
  by_cases h : a = k
  · subst h
    rw [lookup_cons_self, ite_eq_left rfl]
    rfl
  · rw [lookup_cons_ne (Ne.symm h), ite_eq_right h]

private noncomputable def symG (rows : List (Nat × Nat × Nat × Nat)) :
    Nat → Nat → List (Nat × Nat) → List (Nat × Nat) :=
  List.rec (motive := fun _ => Nat → Nat → List (Nat × Nat) → List (Nat × Nat)) (fun _ _ s => s)
    (fun r _ ih c t s => Nat.rec (motive := fun _ => List (Nat × Nat)) s
      (fun t' _ => ih (Nat.succ c) t' (List.cons (rowKey r, Nat.add c (nat_lit 2)) s)) t)
    rows

private theorem symG_zero : ∀ (l : List (Nat × Nat × Nat × Nat)) c s, symG l c 0 s = s
  | [], _, _ => rfl
  | _ :: _, _, _ => rfl

private theorem symG_succ : ∀ (l : List (Nat × Nat × Nat × Nat)) (c t : Nat) (s : List (Nat × Nat)),
    t < l.length → symG l c (t + 1) s = (rowKey (rowAt l t), c + t + 2) :: symG l c t s
  | [], _, _, _, h => absurd h (by simp)
  | r :: l, c, 0, s, _ => by
    change symG l (c + 1) 0 ((rowKey r, c + 2) :: s) = (rowKey r, c + 0 + 2) :: s
    rw [symG_zero]
  | r :: l, c, t + 1, s, h => by
    change symG l (c + 1) (t + 1) ((rowKey r, c + 2) :: s) =
      (rowKey (rowAt l t), c + (t + 1) + 2) :: symG l (c + 1) t ((rowKey r, c + 2) :: s)
    rw [symG_succ l (c + 1) t _ (by simp at h; omega)]
    congr 3
    omega

private theorem symAt_succ {l : List (Nat × Nat × Nat × Nat)} {t : Nat} (h : t < l.length) :
    symAt l (t + 1) = (rowKey (rowAt l t), t + 2) :: symAt l t := by
  have := symG_succ l 0 t [(1, 0), (2, 1)] h
  rw [Nat.zero_add] at this
  exact this

private theorem length_encRows : ∀ rows : List SlotRow, (encRows rows).length = rows.length
  | [] => rfl
  | _ :: rows => congrArg Nat.succ (length_encRows rows)

private theorem rowAt_enc : ∀ (rows : List SlotRow) (t : Nat) (h : t < rows.length),
    rowAt (encRows rows) t = encRow rows[t]
  | [], _, h => absurd h (by simp)
  | _ :: _, 0, _ => rfl
  | _ :: rows, t + 1, h => rowAt_enc rows t (by simp at h; omega)

private def SInv (V : Nat → Nat) (t : Nat) (s : List (Nat × Nat))
    (a : List (Nat × Array Nat) × Bool) : Prop :=
  a.2 = true ∧ ∀ k, (readI s k = 1000000 ∨ readI s k < t + 2) ∧
    (readI s k < t + 2 → slotReadA 4060 a.1 k = unpack 4060 12 (V (readI s k)) ∧ Lo (V (readI s k)))

private theorem sInv_push {V : Nat → Nat} {t : Nat} {s : List (Nat × Nat)}
    {a : List (Nat × Array Nat) × Bool} (ht : t + 2 < 1000000) (h : SInv V t s a)
    (key : Nat) (x : Array Nat) (b : Bool) (hb : b = true) (hx : x = unpack 4060 12 (V (t + 2)))
    (hlo : Lo (V (t + 2))) :
    SInv V (t + 1) ((key, t + 2) :: s) ((key, x) :: a.1, b) := by
  refine ⟨hb, fun k => ?_⟩
  rw [readI_cons]
  dsimp only
  rw [slotReadA_cons]
  by_cases hk : key = k
  · rw [ite_eq_left hk, ite_eq_left hk]
    exact ⟨Or.inr (by omega), fun _ => ⟨hx, hlo⟩⟩
  · rw [ite_eq_right hk, ite_eq_right hk]
    obtain ⟨h1, h2⟩ := h.2 k
    refine ⟨by omega, fun h3 => h2 ?_⟩
    rcases h1 with h1 | h1 <;> omega

private noncomputable def rowOK' (V : Nat → Nat) (o : Nat) (s : List (Nat × Nat))
    (r : Nat × Nat × Nat × Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) false
        (strictB (readI s r.2.2.1) (fun a => bAnd(Nat.blt a o,
          Nat.beq (CFSG.KC.Misc.RuInv.powP (V a) r.2.1) (V o))))
        (Nat.beq r.1 (nat_lit 2)))
      (strictB (readI s r.2.1) (fun a => bAnd(Nat.blt a o,
        permOK (nat_lit 4060) (nat_lit 12) (nat_lit 4095) (nat_lit 48720) (V a) (V o))))
      (Nat.beq r.1 (nat_lit 1)))
    (strictB (readI s r.2.1) (fun a => strictB (readI s r.2.2.1) (fun b =>
      bAnd(Nat.blt a o, bAnd(Nat.blt b o,
        Nat.beq (CFSG.KC.Misc.RuInv.mulP (V a) (V b)) (V o))))))
    (Nat.beq r.1 (nat_lit 0))

private theorem rowOK_eq (rows : List (Nat × Nat × Nat × Nat)) (V : Nat → Nat) (t : Nat) :
    rowOK rows V t = rowOK' V (t + 2) (symAt rows t) (rowAt rows t) := by
  unfold rowOK
  exact PackFld.strictB_eqP _ _

private theorem sInv_step {V : Nat → Nat} {t : Nat} {s : List (Nat × Nat)}
    {a : List (Nat × Array Nat) × Bool} (ht : t + 2 < 1000000) (h : SInv V t s a) (r : SlotRow)
    (hr : rowOK' V (t + 2) s (encRow r) = true) :
    SInv V (t + 1) ((rowKey (encRow r), t + 2) :: s) (slotStepA 4060 a r) := by
  cases r with
  | mu i j k =>
    change strictB (readI s i) (fun a => strictB (readI s j) (fun b =>
      bAnd(Nat.blt a (t + 2), bAnd(Nat.blt b (t + 2),
        Nat.beq (CFSG.KC.Misc.RuInv.mulP (V a) (V b)) (V (t + 2))))))  = true at hr
    simp only [PackFld.strictB_eqP, bAnd_iff, Nat.blt_eq] at hr
    obtain ⟨ha, hb, he⟩ := hr
    obtain ⟨ea, la⟩ := (h.2 i).2 ha
    obtain ⟨eb, _⟩ := (h.2 j).2 hb
    obtain ⟨m1, m2⟩ := mulP_eq (q := V (readI s j)) la
    have he' := Nat.eq_of_beq_eq_true he
    refine sInv_push ht h k _ _ h.1 ?_ (by rw [← he']; exact m2)
    rw [ea, eb, m1, he']
  | iv i j =>
    change strictB (readI s i) (fun a => bAnd(Nat.blt a (t + 2),
      permOK (nat_lit 4060) (nat_lit 12) (nat_lit 4095) (nat_lit 48720) (V a) (V (t + 2)))) =
        true at hr
    simp only [PackFld.strictB_eqP, bAnd_iff, Nat.blt_eq] at hr
    obtain ⟨ha, hp⟩ := hr
    have hp' : permOK 4060 12 (mask 12) (4060 * 12) (V (readI s i)) (V (t + 2)) = true := hp
    obtain ⟨ea, _⟩ := (h.2 i).2 ha
    obtain ⟨i1, i2⟩ := invEqK_sound hp'
    change SInv V (t + 1) ((j, t + 2) :: s) ((j, invCand 4060 (slotReadA 4060 a.1 i)) :: a.1,
      a.2 && isInvA 4060 (slotReadA 4060 a.1 i) (invCand 4060 (slotReadA 4060 a.1 i)))
    refine sInv_push ht h j _ _ ?_ (by rw [ea, i1]) (perm_lo hp').2
    rw [h.1, ea, i1, i2]
    rfl
  | pwr e i j =>
    change strictB (readI s i) (fun a => bAnd(Nat.blt a (t + 2),
      Nat.beq (CFSG.KC.Misc.RuInv.powP (V a) e) (V (t + 2)))) = true at hr
    simp only [PackFld.strictB_eqP, bAnd_iff, Nat.blt_eq] at hr
    obtain ⟨ha, he⟩ := hr
    obtain ⟨ea, la⟩ := (h.2 i).2 ha
    have he' := Nat.eq_of_beq_eq_true he
    obtain ⟨p1, p2⟩ := powP_eq la e
    refine sInv_push ht h j _ _ h.1 ?_ (by rw [← he']; exact p2)
    rw [ea, ← p1, he']

theorem slotV_sound {rows : List SlotRow} {V : Nat → Nat} {L I0 I1 C D : Nat}
    (hL : rows.length = L) (hL' : L < 999999)
    (hA : permOK 4060 12 (mask 12) (4060 * 12) (V 0) I0 = true)
    (hB : permOK 4060 12 (mask 12) (4060 * 12) (V 1) I1 = true)
    (hr : ∀ t < L, rowOK (encRows rows) V t = true) (hf : finOK (encRows rows) L V C D = true) :
    slotRunA 4060 rows (unpack 4060 12 (V 0)) (unpack 4060 12 (V 1)) =
      (unpack 4060 12 C, unpack 4060 12 D, true) := by
  have hlen := length_encRows rows
  have key : ∀ t ≤ L, SInv V t (symAt (encRows rows) t)
      ((rows.take t).foldl (slotStepA 4060)
        ([(1, unpack 4060 12 (V 0)), (2, unpack 4060 12 (V 1))], true)) := by
    intro t
    induction t with
    | zero =>
      intro _
      have e0 : symAt (encRows rows) 0 = [(1, 0), (2, 1)] := symG_zero _ _ _
      rw [e0, List.take_zero, List.foldl_nil]
      refine ⟨rfl, fun k => ?_⟩
      change (readI [(1, 0), (2, 1)] k = 1000000 ∨ readI [(1, 0), (2, 1)] k < 0 + 2) ∧
        (readI [(1, 0), (2, 1)] k < 0 + 2 → slotReadA 4060
          [(1, unpack 4060 12 (V 0)), (2, unpack 4060 12 (V 1))] k =
            unpack 4060 12 (V (readI [(1, 0), (2, 1)] k)) ∧ Lo (V (readI [(1, 0), (2, 1)] k)))
      rw [readI_cons, readI_cons, slotReadA_cons, slotReadA_cons]
      by_cases h1 : 1 = k
      · rw [ite_eq_left h1, ite_eq_left h1]
        exact ⟨Or.inr (by omega), fun _ => ⟨rfl, (perm_lo hA).1⟩⟩
      · rw [ite_eq_right h1, ite_eq_right h1]
        by_cases h2 : 2 = k
        · rw [ite_eq_left h2, ite_eq_left h2]
          exact ⟨Or.inr (by omega), fun _ => ⟨rfl, (perm_lo hB).1⟩⟩
        · rw [ite_eq_right h2, ite_eq_right h2]
          exact ⟨Or.inl rfl, fun h => absurd h (by change ¬ 1000000 < 0 + 2; omega)⟩
    | succ t ih =>
      intro htL
      have ht : t < rows.length := by omega
      rw [symAt_succ (by omega), List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some,
        List.foldl_append, List.foldl_cons, List.foldl_nil, rowAt_enc rows t ht]
      refine sInv_step (by omega) (ih (by omega)) _ ?_
      have := hr t (by omega)
      rw [rowOK_eq, rowAt_enc rows t ht] at this
      exact this
  have hK := key L (Nat.le_refl L)
  rw [← hL, List.take_length] at hK
  rw [hL] at hK
  unfold finOK at hf
  simp only [PackFld.strictB_eqP, bAnd_iff, Nat.blt_eq] at hf
  obtain ⟨ha, hb, hc, hd⟩ := hf
  unfold slotRunA slotFinalA
  dsimp only
  rw [((hK.2 1).2 ha).1, ((hK.2 2).2 hb).1, Nat.eq_of_beq_eq_true hc, Nat.eq_of_beq_eq_true hd,
    hK.1]

private theorem powA_eq (n : Nat) (t : Array Nat) :
    ∀ e, powA n t e = CFSG.Sporadic.Schreier.Co3.co3PowA n t e
  | 0 => rfl
  | e + 1 => congrArg (compA n t) (powA_eq n t e)

theorem powEqRK_sound {n w p e r : Nat}
    (h : powEqRK n w (mask w) (n * w) (pidn n w) p e r = true) :
    powA n (unpack n w p) e = unpack n w r := by
  rw [powA_eq]
  exact powEqK_sound h

open CFSG.KS.Mathieu (icode)

private theorem unpack_get' {n w p i : Nat} (hi : i < n) :
    (unpack n w p)[i]! = pg w (mask w) p i := by
  rw [unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

private theorem pg_hi {n w p x : Nat} (hp : p >>> (n * w) = 0) (hx : n ≤ x) :
    pg w (mask w) p x = 0 := by
  have e : pg w (mask w) p x = (p >>> (w * x)) &&& mask w := rfl
  have h0 : p >>> (w * x) = 0 := by
    have hm := Nat.mul_le_mul_left w hx
    have h1 : w * x = n * w + (w * x - n * w) := by rw [Nat.mul_comm n w]; omega
    rw [h1, Nat.shiftRight_add, hp, Nat.zero_shiftRight]
  rw [e, h0, Nat.zero_and]

private theorem compA_unpack' {n w p q : Nat} (hn : n < 2 ^ 32) (hp : p >>> (n * w) = 0) :
    compA n (unpack n w p) (unpack n w q) = unpack n w (pcomp n w (mask w) p q) := by
  apply Array.ext
  · simp [compA, unpack]
  · intro i h1 _
    have hi : i < n := by simpa [compA] using h1
    simp only [compA, Array.getElem_ofFn]
    rw [unpack_get' hi]
    simp only [unpack, Array.getElem_ofFn]
    rw [PackFld.pg_pcomp hn hi]
    by_cases hx : pg w (mask w) q i < n
    · rw [← unpack, unpack_get' hx]
    · rw [getElem!_neg _ _ (by simpa using hx), pg_hi hp (by omega)]
      rfl

private noncomputable def letK (S SI : Nat → Nat) (c : Nat) : Nat :=
  nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
    S (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
    SI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))

private theorem letK_even {S SI : Nat → Nat} {c : Nat} (hc : c % 2 = 0) :
    letK S SI c = S (c / 2 - 1) := by
  have e : Nat.land c 1 = c % 2 := Nat.and_one_is_mod c
  unfold letK
  rw [e, hc, PackFld.shr_eq, Nat.pow_one]
  rfl

private theorem letK_odd {S SI : Nat → Nat} {c : Nat} (hc : c % 2 = 1) :
    letK S SI c = SI (c / 2 - 1) := by
  have e : Nat.land c 1 = c % 2 := Nat.and_one_is_mod c
  unfold letK
  rw [e, hc, PackFld.shr_eq, Nat.pow_one]
  rfl

private theorem wordK_cons' (n w m idn : Nat) (S SI : Nat → Nat) (z : Int) (wd : List Int) :
    wordK n w m idn S SI (z :: wd) =
      pcomp n w m (letK S SI (icode z)) (wordK n w m idn S SI wd) := by
  change strictN (wordK n w m idn S SI wd)
    (fun T => strictN (icode z) (fun c => pcomp n w m (letK S SI c) T)) = _
  simp only [PackFld.strictN_eqP]

private theorem lettersK_cons' (j : Nat) (z : Int) (wd : List Int) :
    lettersK j (z :: wd) = bAnd(Nat.blt (nat_lit 0) (icode z),
      bAnd(Nat.ble (Nat.shiftRight (icode z) (nat_lit 1)) j, lettersK j wd)) :=
  PackFld.strictB_eqP (icode z) (fun c => bAnd(Nat.blt (nat_lit 0) c,
    bAnd(Nat.ble (Nat.shiftRight c (nat_lit 1)) j, lettersK j wd)))

private theorem map_get' {S : Array (Array Nat)} {f : Array Nat → Array Nat} {k : Nat}
    (hk : k < S.size) : (S.map f)[k]! = f S[k]! := by
  rw [getElem!_pos (S.map f) k (by simpa using hk), Array.getElem_map, getElem!_pos S k hk]

private theorem letter_sound' {n w kS : Nat} {PS PSI : Nat → Nat} {S : Array (Array Nat)}
    (hS : S.size = kS ∧ ∀ j < kS, S[j]! = unpack n w (PS j))
    (hperm : ∀ j < kS, permOK n w (mask w) (n * w) (PS j) (PSI j) = true) {z : Int}
    (h1 : Nat.blt (nat_lit 0) (icode z) = true)
    (h2 : Nat.ble (Nat.shiftRight (icode z) (nat_lit 1)) kS = true) :
    unpack n w (letK PS PSI (icode z)) = letterA S (rawInvs n S) z ∧
      letK PS PSI (icode z) >>> (n * w) = 0 := by
  have h1' := Nat.blt_eq.mp h1
  have h2' := Nat.ble_eq.mp h2
  rw [PackFld.shr_eq, Nat.pow_one] at h2'
  have hc : ∀ j < kS, PS j >>> (n * w) = 0 ∧ PSI j >>> (n * w) = 0 := fun j hj => by
    have := hperm j hj
    unfold permOK at this
    simp only [bAnd_iff] at this
    exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2.1⟩
  cases z with
  | ofNat k =>
    have hk : k + k = icode (Int.ofNat k) := rfl
    rw [← hk] at h1' h2'
    have hL : letK PS PSI (icode (Int.ofNat k)) = PS (k - 1) := by
      rw [← hk, letK_even (by omega)]
      congr 1
      omega
    have hj : k - 1 < kS := by omega
    have hk0 : 0 < k := by omega
    have h0 : (0 : Int) < Int.ofNat k := Int.ofNat_lt.mpr hk0
    have et : (Int.ofNat k).toNat = k := rfl
    rw [hL]
    refine ⟨?_, (hc _ hj).1⟩
    unfold letterA
    rw [PackFld.iteT h0, et, hS.2 _ hj]
  | negSucc k =>
    have hk : k + 1 + (k + 1) + 1 = icode (Int.negSucc k) := rfl
    rw [← hk] at h2'
    have hL : letK PS PSI (icode (Int.negSucc k)) = PSI k := by
      rw [← hk, letK_odd (by omega)]
      congr 1
      omega
    have hj : k < kS := by omega
    have h0 : ¬ (0 : Int) < Int.negSucc k := Int.not_lt.mpr (Int.le_of_lt (Int.negSucc_lt_zero k))
    have et : (-Int.negSucc k).toNat = k + 1 := rfl
    rw [hL]
    refine ⟨?_, (hc _ hj).2⟩
    unfold letterA
    rw [PackFld.iteF h0, et, Nat.add_sub_cancel, rawInvs, map_get' (by rw [hS.1]; exact hj),
      hS.2 _ hj, (invEqK_sound (hperm _ hj)).1]

theorem wordAppK_sound {n w kS P r : Nat} {PS PSI : Nat → Nat} {S : Array (Array Nat)}
    {wd rest : List Int} (hS : S.size = kS ∧ ∀ j < kS, S[j]! = unpack n w (PS j))
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hP : wordA n S (rawInvs n S) rest = unpack n w P)
    (h : wordAppK n w (mask w) PS PSI kS wd P r = true) :
    wordA n S (rawInvs n S) (wd ++ rest) = unpack n w r := by
  unfold wordAppK at h
  simp only [bAnd_iff] at h
  obtain ⟨hsz, hl, hr⟩ := h
  have hn : n < 2 ^ 32 := by
    unfold szOK at hsz
    simp only [bAnd_iff] at hsz
    have := Nat.blt_eq.mp hsz.1
    omega
  have hperm : ∀ j < kS, permOK n w (mask w) (n * w) (PS j) (PSI j) = true :=
    fun j hj => allN_spec hp j hj
  rw [← Nat.eq_of_beq_eq_true hr]
  clear hr
  induction wd with
  | nil => exact hP
  | cons z wd ih =>
    rw [lettersK_cons'] at hl
    simp only [bAnd_iff] at hl
    obtain ⟨h1, h2, h3⟩ := hl
    obtain ⟨hL1, hL2⟩ := letter_sound' hS hperm h1 h2
    have e2 : wordA n S (rawInvs n S) ((z :: wd) ++ rest) =
        compA n (letterA S (rawInvs n S) z) (wordA n S (rawInvs n S) (wd ++ rest)) := rfl
    rw [e2, ih h3, ← hL1, compA_unpack' hn hL2, wordK_cons']

theorem takeK_eq : ∀ (k : Nat) (l : List Int), takeK k l = l.take k
  | _, [] => by cases ‹Nat› <;> rfl
  | 0, _ :: _ => rfl
  | k + 1, x :: l => by
    change x :: takeK k l = x :: l.take k
    rw [takeK_eq k l]

theorem dropK_eq : ∀ (k : Nat) (l : List Int), dropK k l = l.drop k
  | _, [] => by cases ‹Nat› <;> rfl
  | 0, _ :: _ => rfl
  | k + 1, _ :: l => dropK_eq k l

theorem chunks_eq {α : Type} {f : List Int → α} {wd : List Int} {c K : Nat} {P : Nat → α}
    (hK : wd.length ≤ c * K) (h0 : f [] = P K)
    (hstep : ∀ q < K, f (wd.drop (c * (q + 1))) = P (q + 1) →
      f ((wd.drop (c * q)).take c ++ wd.drop (c * (q + 1))) = P q) :
    f wd = P 0 := by
  have key : ∀ i ≤ K, f (wd.drop (c * (K - i))) = P (K - i) := by
    intro i
    induction i with
    | zero => intro _; rw [Nat.sub_zero, List.drop_eq_nil_of_le hK]; exact h0
    | succ i ih =>
      intro hi
      have hq : K - (i + 1) < K := by omega
      have e : K - (i + 1) + 1 = K - i := by omega
      have h1 := hstep _ hq (by rw [e]; exact ih (by omega))
      rwa [e, show c * (K - i) = c * (K - (i + 1)) + c by
        rw [← e, Nat.mul_succ], ← List.drop_drop, List.take_append_drop] at h1
  have := key K (Nat.le_refl K)
  rwa [Nat.sub_self, Nat.mul_zero, List.drop_zero] at this

private theorem utf8_size_ascii : ∀ cs : List Char,
    (∀ k < cs.length, (cs[k]!).toNat < 128) → cs.utf8Encode.size = cs.length
  | [], _ => rfl
  | c :: cs, h => by
    have hc : c.toNat < 128 := by simpa using h 0 (by simp)
    rw [List.utf8Encode_cons, CFSG.KS.HexText.utf8_single hc, ByteArray.size_append,
      utf8_size_ascii cs (fun k hk => by simpa using h (k + 1) (by simp; omega))]
    simp
    omega

private theorem hexRun_spec {wd bd cnt : Nat} {L : List Char} : ∀ r e t,
    L.length = wd * e + t + r → t < wd →
    hexRun wd bd cnt (L.drop (wd * e + t)) e t (CFSG.KS.HexText.numA L (wd * e) t) = true →
    L.length = wd * cnt ∧
      (∀ k, wd * e + t ≤ k → k < L.length → CFSG.KS.Text.hexV (L[k]!).toNat < 16) ∧
      ∀ e', e ≤ e' → e' < cnt → CFSG.KS.HexText.numA L (wd * e') wd < bd
  | 0, e, t, hl, _, h => by
    rw [List.drop_eq_nil_of_le (by omega)] at h
    change bAnd(Nat.beq e cnt, Nat.beq t (nat_lit 0)) = true at h
    rw [bAnd_iff] at h
    have he : e = cnt := Nat.eq_of_beq_eq_true h.1
    have ht : t = 0 := Nat.eq_of_beq_eq_true h.2
    subst he ht
    exact ⟨by omega, fun k h1 h2 => by omega, fun e' h1 h2 => by omega⟩
  | r + 1, e, t, hl, htw, h => by
    have hp : wd * e + t < L.length := by omega
    rw [List.drop_eq_getElem_cons hp] at h
    have hget : L[wd * e + t]! = L[wd * e + t] := getElem!_pos L _ hp
    have hv' : Nat.add (Nat.mul (CFSG.KS.HexText.numA L (wd * e) t) 16)
        (CFSG.KS.Text.hexV (Char.toNat L[wd * e + t])) =
          CFSG.KS.HexText.numA L (wd * e) (t + 1) := by
      rw [CFSG.KS.HexText.numA, hget]
      rfl
    change strictB (CFSG.KS.Text.hexV (Char.toNat L[wd * e + t])) (fun h =>
      bIf(Nat.blt h (nat_lit 16),
        strictB (Nat.add (Nat.mul (CFSG.KS.HexText.numA L (wd * e) t) (nat_lit 16)) h) (fun v' =>
          bIf(Nat.beq (Nat.succ t) wd,
            bIf(Nat.blt v' bd, hexRun wd bd cnt (L.drop (wd * e + t + 1)) (Nat.succ e) (nat_lit 0)
              (nat_lit 0), false),
            hexRun wd bd cnt (L.drop (wd * e + t + 1)) e (Nat.succ t) v')),
        false)) = true at h
    simp only [CFSG.KS.PackFld.strictB_eqP] at h
    rw [hv'] at h
    cases h1 : Nat.blt (CFSG.KS.Text.hexV (Char.toNat L[wd * e + t])) 16 <;> rw [h1] at h
    · exact absurd h Bool.false_ne_true
    dsimp only at h
    have hdig : CFSG.KS.Text.hexV (L[wd * e + t]!).toNat < 16 := by
      rw [hget]
      exact Nat.blt_eq.mp h1
    cases h3 : Nat.beq (Nat.succ t) wd <;> rw [h3] at h
    · have htw' : t + 1 < wd := by
        have := CFSG.KS.PackFld.false_of_beq h3
        omega
      have e1 : wd * e + t + 1 = wd * e + (t + 1) := by omega
      rw [e1] at h
      obtain ⟨a, b, c⟩ := hexRun_spec r e (t + 1) (by omega) htw' h
      refine ⟨a, fun k hk1 hk2 => ?_, c⟩
      rcases Nat.lt_or_ge k (wd * e + t + 1) with hk | hk
      · have : k = wd * e + t := by omega
        subst this
        exact hdig
      · exact b k (by omega) hk2
    · have ht1 : t + 1 = wd := Nat.eq_of_beq_eq_true h3
      dsimp only at h
      cases h4 : Nat.blt (CFSG.KS.HexText.numA L (wd * e) (t + 1)) bd <;> rw [h4] at h
      · exact absurd h Bool.false_ne_true
      dsimp only at h
      have e1 : wd * e + t + 1 = wd * (e + 1) + 0 := by rw [Nat.mul_succ]; omega
      rw [e1] at h
      obtain ⟨a, b, c⟩ := hexRun_spec r (e + 1) 0 (by rw [Nat.mul_succ]; omega) (by omega) h
      refine ⟨a, fun k hk1 hk2 => ?_, fun e' he1 he2 => ?_⟩
      · rcases Nat.lt_or_ge k (wd * e + t + 1) with hk | hk
        · have : k = wd * e + t := by omega
          subst this
          exact hdig
        · exact b k (by omega) hk2
      · rcases Nat.lt_or_ge e' (e + 1) with he | he
        · have he' : e' = e := by omega
          have h4' := Nat.blt_eq.mp h4
          rw [ht1] at h4'
          rw [he']
          exact h4'
        · exact c e' he he2

theorem hexRunK_sound {wd bd cnt : Nat} {cs : List Char} (h : hexRunK wd bd cnt cs = true) :
    (String.ofList cs).toUTF8.size = wd * cnt ∧
      ∀ k < cnt, CFSG.Monster.B.Max2.Native.hexAt (String.ofList cs).toUTF8 (wd * k) wd < bd := by
  unfold hexRunK at h
  rw [bAnd_iff] at h
  have hwd : 0 < wd := Nat.blt_eq.mp h.1
  obtain ⟨hlen, hdig, hlt⟩ := hexRun_spec (L := cs) (bd := bd) (cnt := cnt) cs.length 0 0
    (by omega) hwd (by rw [Nat.mul_zero, Nat.add_zero, List.drop_zero]; exact h.2)
  have hasc : ∀ k < cs.length, k < cs.length ∧ (cs[k]!).toNat < 128 := by
    intro k hk
    refine ⟨hk, ?_⟩
    rcases CFSG.KS.HexText.hexV_dig (hdig k (by omega) hk) with ⟨-, h2, -⟩ | ⟨-, h2, -⟩ <;> omega
  have hsize : (String.ofList cs).toUTF8.size = cs.length := by
    rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
    exact utf8_size_ascii cs (fun k hk => (hasc k hk).2)
  refine ⟨by rw [hsize, hlen], fun k hk => ?_⟩
  have hk' : wd * k + wd ≤ cs.length := by
    rw [hlen, ← Nat.mul_succ]
    exact Nat.mul_le_mul_left wd hk
  rw [CFSG.KS.HexText.num_bytes (o := wd * k) hasc
    (fun c => CFSG.Monster.B.Max2.Native.hexAt (String.ofList cs).toUTF8 (wd * k) c)
    rfl (fun c => rfl) wd hk' (fun s hs => hdig _ (by omega) (by omega))]
  exact hlt k (Nat.zero_le k) hk

theorem hexAt_eq (b : ByteArray) (o : Nat) :
    ∀ w, CFSG.Monster.B.Max2.Native.hexAt b o w = CFSG.Monster.B.Co2.Native.hexAt b o w
  | 0 => rfl
  | w + 1 => by
    rw [CFSG.Monster.B.Max2.Native.hexAt, CFSG.Monster.B.Co2.Native.hexAt, hexAt_eq b o w]
    rfl

theorem ruHexRow_eq (b : ByteArray) (n L : Nat) :
    ruHexRow b n L = CFSG.Sporadic.Schreier.Co3.Native.hexLine b 3 n L := by
  unfold ruHexRow CFSG.Sporadic.Schreier.Co3.Native.hexLine ruHexAt
  simp only [hexAt_eq]

theorem row_of {s : String} {cs : List Char} {n w lines L : Nat} {F : Nat → Nat}
    (e : s = String.ofList cs) (hb : CFSG.KS.Text.hexBind cs 3 n w lines 0 lines F = true)
    (hL : L < lines) : ruHexRow s.toUTF8 n L = unpack n w (F L) := by
  subst e
  have h := CFSG.KS.Text.hexBind_sound hb L hL
  rw [Nat.zero_add] at h
  rw [ruHexRow_eq]
  exact h

theorem layout_of {s : String} {cs : List Char} {n w lines : Nat} {F : Nat → Nat}
    (e : s = String.ofList cs) (hb : CFSG.KS.Text.hexBind cs 3 n w lines 0 lines F = true) :
    ruLayoutOK s.toUTF8 n lines = true := by
  subst e
  exact hexBind_layout hb rfl

theorem ruLayoutOK_eq (b : ByteArray) (n m : Nat) :
    ruLayoutOK b n m = CFSG.Sporadic.Schreier.Co3.Native.layoutOK b 3 n m := rfl

theorem forall_of_blocks {f : Nat → Bool} {K Q : Nat}
    (h : ∀ q < Q, allN K (fun d => f (Nat.add (Nat.mul K q) d)) = true) :
    ∀ j < K * Q, f j = true := by
  intro j hj
  have hK : 0 < K := Nat.pos_of_ne_zero (by rintro rfl; simp at hj)
  have hq : j / K < Q := (Nat.div_lt_iff_lt_mul hK).2 (by rwa [Nat.mul_comm] at hj)
  have hd : j % K < K := Nat.mod_lt j hK
  have := allN_spec (h (j / K) hq) (j % K) hd
  rwa [show Nat.add (Nat.mul K (j / K)) (j % K) = j from Nat.div_add_mod j K] at this

theorem lettersAllK_sound {k : Nat} : ∀ {ws : List (List Int)}, lettersAllK k ws = true →
    ws.all (lettersOK k) = true
  | [], _ => rfl
  | wd :: ws, h => by
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    rw [List.all_cons, lettersK_sound h1, lettersAllK_sound h2]
    rfl

end CFSG.KS.SporSch

end
