module

public import Certificates.Data.Kernel.SporSch.RuEnumK
public import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.HexText
import CFSG.Certificates.Kernel.Spor.RawSiftK
public import CFSG.Sporadic.Schreier.RuArrays
public import CFSG.Sporadic.Schreier.RuEnum

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

private noncomputable def entF (wd start len : Nat) (L : List Char) (e k : Nat) : Nat :=
  if k < len ∧ start + k < e then CFSG.KS.HexText.numA L (wd * (start + k)) wd else 0

private theorem hexPack_spec {wd bd cnt start len w F : Nat} {L : List Char} (hbd : bd ≤ 2 ^ w) :
    ∀ r e t acc, L.length = wd * e + t + r → t < wd → PackFld.Fld w acc (entF wd start len L e) →
    hexPack wd bd cnt start len w F (L.drop (wd * e + t)) e t
      (CFSG.KS.HexText.numA L (wd * e) t) acc = true →
    L.length = wd * cnt ∧
      (∀ k, wd * e + t ≤ k → k < L.length → CFSG.KS.Text.hexV (L[k]!).toNat < 16) ∧
      PackFld.Fld w F (entF wd start len L cnt) ∧
      ∀ e', e ≤ e' → e' < cnt → CFSG.KS.HexText.numA L (wd * e') wd < bd
  | 0, e, t, acc, hl, _, ha, h => by
    rw [List.drop_eq_nil_of_le (by omega)] at h
    change bAnd(Nat.beq e cnt, bAnd(Nat.beq t (nat_lit 0), Nat.beq acc F)) = true at h
    simp only [bAnd_iff] at h
    have he : e = cnt := Nat.eq_of_beq_eq_true h.1
    have ht : t = 0 := Nat.eq_of_beq_eq_true h.2.1
    have hF : acc = F := Nat.eq_of_beq_eq_true h.2.2
    subst he ht hF
    exact ⟨by omega, fun k h1 h2 => by omega, ha, fun e' h1 h2 => by omega⟩
  | r + 1, e, t, acc, hl, htw, ha, h => by
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
            bIf(Nat.blt v' bd,
              strictB (nIf(bAnd(Nat.ble start e, Nat.blt e (Nat.add start len)),
                  Nat.lor acc (Nat.shiftLeft v' (Nat.mul w (Nat.sub e start))), acc))
                (fun acc' => hexPack wd bd cnt start len w F (L.drop (wd * e + t + 1)) (Nat.succ e)
                  (nat_lit 0) (nat_lit 0) acc'), false),
            hexPack wd bd cnt start len w F (L.drop (wd * e + t + 1)) e (Nat.succ t) v' acc)),
        false)) = true at h
    simp only [PackFld.strictB_eqP] at h
    rw [hv'] at h
    cases h1 : Nat.blt (CFSG.KS.Text.hexV (Char.toNat L[wd * e + t])) 16 <;> rw [h1] at h
    · exact absurd h Bool.false_ne_true
    dsimp only at h
    have hdig : CFSG.KS.Text.hexV (L[wd * e + t]!).toNat < 16 := by
      rw [hget]
      exact Nat.blt_eq.mp h1
    cases h3 : Nat.beq (Nat.succ t) wd <;> rw [h3] at h
    · have htw' : t + 1 < wd := by
        have := PackFld.false_of_beq h3
        omega
      have e1 : wd * e + t + 1 = wd * e + (t + 1) := by omega
      rw [e1] at h
      obtain ⟨a, b, c, d⟩ := hexPack_spec hbd r e (t + 1) acc (by omega) htw' ha h
      refine ⟨a, fun k hk1 hk2 => ?_, c, d⟩
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
      have hv : CFSG.KS.HexText.numA L (wd * e) wd < 2 ^ w := by
        have := Nat.blt_eq.mp h4
        rw [ht1] at this
        omega
      have e1 : wd * e + t + 1 = wd * (e + 1) + 0 := by rw [Nat.mul_succ]; omega
      rw [e1] at h
      have ha' : PackFld.Fld w (Bool.rec (motive := fun _ => Nat) acc
          (Nat.lor acc (Nat.shiftLeft (CFSG.KS.HexText.numA L (wd * e) (t + 1))
            (Nat.mul w (Nat.sub e start))))
          (bAnd(Nat.ble start e, Nat.blt e (Nat.add start len))))
          (entF wd start len L (e + 1)) := by
        rw [ht1]
        cases hin : bAnd(Nat.ble start e, Nat.blt e (Nat.add start len))
        · refine PackFld.fld_congr ha (fun k => ?_)
          have hn : ¬ (start ≤ e ∧ e < start + len) := by
            intro ⟨x, y⟩
            have y' : Nat.blt e (Nat.add start len) = true := Nat.blt_eq.mpr y
            rw [Nat.ble_eq_true_of_le x, y'] at hin
            exact Bool.noConfusion hin
          unfold entF
          by_cases hk : k < len ∧ start + k < e
          · have : k < len ∧ start + k < e + 1 := ⟨hk.1, by omega⟩
            simp only [hk, this, and_self, ↓reduceIte]
          · have : ¬ (k < len ∧ start + k < e + 1) := by
              intro ⟨x, y⟩
              by_cases hke : start + k = e
              · exact hn ⟨by omega, by omega⟩
              · exact hk ⟨x, by omega⟩
            simp only [hk, this, ↓reduceIte]
        · rw [bAnd_iff] at hin
          have hs : start ≤ e := Nat.le_of_ble_eq_true hin.1
          have hel : e < start + len := Nat.blt_eq.mp hin.2
          refine PackFld.fld_congr (PackFld.fld_or ha (PackFld.fld_shl (e - start)
            (PackFld.fld_one hv))) (fun k => ?_)
          unfold entF
          by_cases hk : start + k < e
          · have h5 : ¬ e - start ≤ k := by omega
            have h6 : k < len := by omega
            simp [hk, h5, h6, show start + k < e + 1 by omega]
          · by_cases hke : start + k = e
            · have h5 : e - start ≤ k := by omega
              have h6 : k - (e - start) = 0 := by omega
              have h7 : k < len := by omega
              have h8 : wd * (start + k) = wd * e := by rw [hke]
              simp [hk, h5, h6, h7, h8, show start + k < e + 1 by omega]
            · have h5 : e - start ≤ k := by omega
              have h6 : k - (e - start) ≠ 0 := by omega
              have h7 : ¬ start + k < e + 1 := by omega
              simp [hk, h5, h6, h7]
      obtain ⟨a, b, c, d⟩ := hexPack_spec hbd r (e + 1) 0 _ (by rw [Nat.mul_succ]; omega)
        (by omega) ha' h
      refine ⟨a, fun k hk1 hk2 => ?_, c, fun e' he1 he2 => ?_⟩
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
        · exact d e' he he2

theorem hexPackK_sound {wd bd cnt start len w F : Nat} {cs : List Char} (hbd : bd ≤ 2 ^ w)
    (hr : start + len ≤ cnt) (h : hexPackK wd bd cnt start len w F cs = true) :
    ∀ k < len, CFSG.Monster.B.Max2.Native.hexAt (String.ofList cs).toUTF8 (wd * (start + k)) wd =
      pg w (mask w) F k := by
  unfold hexPackK at h
  rw [bAnd_iff] at h
  have hwd : 0 < wd := Nat.blt_eq.mp h.1
  have h0 : PackFld.Fld w 0 (entF wd start len cs 0) :=
    PackFld.fld_congr (PackFld.fld_zero w) (fun k => by unfold entF; simp)
  obtain ⟨hlen, hdig, hF, hbnd⟩ := hexPack_spec (L := cs) (F := F) (cnt := cnt) hbd cs.length 0 0 0
    (by omega) hwd h0 (by rw [Nat.mul_zero, Nat.add_zero, List.drop_zero]; exact h.2)
  have hasc : ∀ k < cs.length, k < cs.length ∧ (cs[k]!).toNat < 128 := by
    intro k hk
    refine ⟨hk, ?_⟩
    rcases CFSG.KS.HexText.hexV_dig (hdig k (by omega) hk) with ⟨-, h2, -⟩ | ⟨-, h2, -⟩ <;> omega
  intro k hk
  have hk' : wd * (start + k) + wd ≤ cs.length := by
    rw [hlen, ← Nat.mul_succ]
    exact Nat.mul_le_mul_left wd (by omega)
  rw [CFSG.KS.HexText.num_bytes (o := wd * (start + k)) hasc
    (fun c => CFSG.Monster.B.Max2.Native.hexAt (String.ofList cs).toUTF8 (wd * (start + k)) c)
    rfl (fun c => rfl) wd hk' (fun s hs => hdig _ (by omega) (by omega))]
  have hlt : entF wd start len cs cnt k < 2 ^ w := by
    unfold entF
    have hb : CFSG.KS.HexText.numA cs (wd * (start + k)) wd < 2 ^ w :=
      Nat.lt_of_lt_of_le (hbnd _ (Nat.zero_le _) (by omega)) hbd
    split
    · exact hb
    · exact Nat.two_pow_pos w
  rw [PackFld.pg_of_fld hF hlt]
  unfold entF
  simp [hk, show start + k < cnt by omega]

private theorem all_iffK {n : Nat} {f : Nat → Bool} :
    (Nat.all n fun i _ => f i) = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.all_succ, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · exact h1 i h
      · subst h
        exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

theorem posK_sound {n m w F POS : Nat} (h : posK n m w F POS = true) :
    ruPosTab n (unpack m w F) = unpack n w POS := by
  unfold posK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have hF : ∀ i < m, pg w (mask w) F i < n ∧ pg w (mask w) POS (pg w (mask w) F i) = i := by
    intro i hi
    have := allN_spec h1 i hi
    rw [PackFld.strictB_eqP] at this
    obtain ⟨a, b⟩ := (bAnd_iff _ _).1 this
    exact ⟨Nat.blt_eq.mp a, Nat.eq_of_beq_eq_true b⟩
  have hP : ∀ x < n, pg w (mask w) POS x = n ∨
      (pg w (mask w) POS x < m ∧ pg w (mask w) F (pg w (mask w) POS x) = x) := by
    intro x hx
    have := allN_spec h2 x hx
    rw [PackFld.strictB_eqP] at this
    cases e : Nat.beq (pg w (mask w) POS x) n
    · rw [e] at this
      obtain ⟨a, b⟩ := (bAnd_iff _ _).1 this
      exact Or.inr ⟨Nat.blt_eq.mp a, Nat.eq_of_beq_eq_true b⟩
    · exact Or.inl (Nat.eq_of_beq_eq_true e)
  have hsz : (unpack m w F).size = m := by simp [unpack]
  have hget : ∀ i < m, (unpack m w F)[i]! = pg w (mask w) F i := by
    intro i hi
    rw [unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  have key : ∀ k ≤ m,
      ((List.range k).foldl (fun r i => r.set! (unpack m w F)[i]! i) (Array.replicate n n)).size =
        n ∧ ∀ x < n, ((List.range k).foldl (fun r i => r.set! (unpack m w F)[i]! i)
          (Array.replicate n n))[x]! =
          if pg w (mask w) POS x < k then pg w (mask w) POS x else n := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨by simp, fun x hx => ?_⟩
      simp only [List.range_zero, List.foldl_nil]
      rw [getElem!_pos (Array.replicate n n) x (by simpa using hx)]
      simp
    | succ k ih =>
      intro hk
      obtain ⟨hs, hv⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hget k (by omega)]
      obtain ⟨hFk, hPk⟩ := hF k (by omega)
      refine ⟨by rw [Array.set!, Array.size_setIfInBounds, hs], fun x hx => ?_⟩
      rw [Array.set!, getElem!_pos _ x (by rw [Array.size_setIfInBounds, hs]; exact hx),
        Array.getElem_setIfInBounds (by rw [hs]; exact hx)]
      by_cases hxk : pg w (mask w) F k = x
      · subst hxk
        rw [ite_eq_left rfl, hPk, ite_eq_left (by omega)]
      · rw [ite_eq_right hxk, ← getElem!_pos _ x (by rw [hs]; exact hx), hv x hx]
        by_cases hlt : pg w (mask w) POS x < k
        · rw [ite_eq_left hlt, ite_eq_left (by omega)]
        · rw [ite_eq_right hlt]
          by_cases he : pg w (mask w) POS x = k
          · rcases hP x hx with hn | ⟨-, hFx⟩
            · rw [ite_eq_left (by omega), hn]
            · rw [he] at hFx
              exact absurd hFx hxk
          · rw [ite_eq_right (by omega)]
  obtain ⟨hs, hv⟩ := key m le_rfl
  unfold ruPosTab
  rw [hsz]
  apply Array.ext
  · rw [hs]
    simp [unpack]
  · intro x h1 _
    have hx : x < n := by rwa [hs] at h1
    rw [← getElem!_pos _ x h1, hv x hx]
    simp only [unpack, Array.getElem_ofFn]
    split
    · rfl
    · rcases hP x hx with hn | ⟨hm, -⟩
      · exact hn.symm
      · omega

theorem resK_sound {n m w w' F POS G R : Nat} (hF : ∀ i < m, pg w (mask w) F i < n)
    (hG : canonK n w (mask w) (n * w) G = true) (h : resK m w w' F POS G R = true) :
    resA (unpack m w F) (unpack n w POS) (unpack n w G) = unpack m w' R := by
  unfold resK at h
  obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 h
  have hGr := allN_spec (CFSG.KS.Raw.range_of_canonK hG)
  have hget : ∀ {k v P : Nat}, v < k → (unpack k w P)[v]! = pg w (mask w) P v := by
    intro k v P hv
    rw [unpack, getElem!_pos _ v (by simpa using hv), Array.getElem_ofFn]
  apply Array.ext
  · simp [resA, unpack]
  · intro i h1 _
    have hi : i < m := by simpa [resA, unpack] using h1
    simp only [resA, Array.getElem_ofFn, unpack]
    have e1 := hget (P := F) hi
    simp only [unpack] at e1
    rw [e1]
    have e2 := hget (P := G) (hF i hi)
    simp only [unpack] at e2
    rw [e2]
    have e3 := hget (P := POS) (Nat.blt_eq.mp (hGr _ (hF i hi)))
    simp only [unpack] at e3
    rw [e3]
    exact (Nat.eq_of_beq_eq_true (allN_spec h2 i hi)).symm

theorem canon_eqA {n w p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) :
    eqA n (unpack n w p) (unpack n w q) = Nat.beq p q := by
  unfold canonK szOK at hp hq
  obtain ⟨hsz, hp2⟩ := (bAnd_iff _ _).1 hp
  obtain ⟨hp0, -⟩ := (bAnd_iff _ _).1 hp2
  obtain ⟨-, hq2⟩ := (bAnd_iff _ _).1 hq
  obtain ⟨hq0, -⟩ := (bAnd_iff _ _).1 hq2
  have hw : 0 < w := by
    obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 hsz
    have h2 := Nat.blt_eq.mp h2
    rw [PackFld.shl_eq, Nat.one_mul] at h2
    rcases Nat.eq_zero_or_pos w with h0 | h0
    · subst h0
      simp at h2
    · exact h0
  have hp0 : p >>> (n * w) = 0 := Nat.eq_of_beq_eq_true hp0
  have hq0 : q >>> (n * w) = 0 := Nat.eq_of_beq_eq_true hq0
  have hget : ∀ {v P : Nat}, v < n → (unpack n w P)[v]! = pg w (mask w) P v := by
    intro v P hv
    rw [unpack, getElem!_pos _ v (by simpa using hv), Array.getElem_ofFn]
  have hall : eqA n (unpack n w p) (unpack n w q) = true ↔
      ∀ i < n, pg w (mask w) p i = pg w (mask w) q i := by
    unfold eqA CFSG.Monster.B.Co2.Native.allLt
    rw [all_iffK]
    simp only [beq_iff_eq]
    constructor
    · intro h i hi
      rw [← hget hi, ← hget hi]
      exact h i hi
    · intro h i hi
      rw [hget hi, hget hi]
      exact h i hi
  cases e : Nat.beq p q
  · have hne : p ≠ q := fun he => by rw [he, Nat.beq_refl] at e; exact absurd e (by decide)
    apply Bool.eq_false_iff.2
    intro he
    apply hne
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < n * w
    · have hd := Nat.div_add_mod j w
      have hi : j / w < n := (Nat.div_lt_iff_lt_mul hw).2 hj
      have hk : j % w < w := Nat.mod_lt j hw
      have tp := PackFld.testBit_pgM w p (j / w) (j % w)
      have tq := PackFld.testBit_pgM w q (j / w) (j % w)
      rw [hd] at tp tq
      rw [(hall.1 he) _ hi] at tp
      simp only [hk, decide_true, Bool.true_and] at tp tq
      rw [← tp, tq]
    · have e : j = n * w + (j - n * w) := by omega
      rw [e, ← Nat.testBit_shiftRight, ← Nat.testBit_shiftRight, hp0, hq0]
  · have hpq := Nat.eq_of_beq_eq_true e
    subst hpq
    exact hall.2 fun i _ => rfl

private theorem prod2_facts {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {p : Array Nat → Bool} {pK : Nat → Bool}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (h2 : 2 ≤ nb)
    (hpK : ∀ G, canonK n w (mask w) (n * w) G = true → pK G = p (unpack n w G)) :
    (rawLevels n S base)[0]!.pts.size = rcnt (LR 0) ∧
      (rawLevels n S base)[1]!.pts.size = rcnt (LR 1) ∧
      ∀ a < rcnt (LR 0), ∀ b < rcnt (LR 1),
        p (CFSG.Sporadic.RuSchreier.prod2A n (rawLevels n S base) a b) =
          pK (pcomp n w (mask w) (TR (roff n (n * w) (LR 0) + a))
            (TR (roff n (n * w) (LR 1) + b))) := by
  have hbl := Raw.Orb.base_lt_of_levels hb hl
  obtain ⟨A0, P0⟩ := Raw.Orb.agree_levelK hb hp hbl (R := LR) (TRI := TRI) (i := 0) (by omega)
    (hl 0 (by omega))
  obtain ⟨A1, P1⟩ := Raw.Orb.agree_levelK hb hp hbl (R := LR) (TRI := TRI) (i := 1) (by omega)
    (hl 1 (by omega))
  have hn32 : n < 2 ^ 32 := by have := hb.2.2.1; omega
  have hw : 0 < w := by
    have h := hb.2.1
    rcases Nat.eq_zero_or_pos w with h0 | h0
    · subst h0
      simp at h
    · exact h0
  have e0 : (rawLevels n S base)[0]! = CFSG.Certificates.ChainArrays.lev n S base 0 := rfl
  have e1 : (rawLevels n S base)[1]! = CFSG.Certificates.ChainArrays.lev n S base 1 := rfl
  refine ⟨by rw [e0, A0.cnt], by rw [e1, A1.cnt], fun a ha b hb' => ?_⟩
  set T0 := TR (roff n (n * w) (LR 0) + a)
  set T1 := TR (roff n (n * w) (LR 1) + b)
  have hP0 := (P0 a ha).1
  have hP1 := (P1 b hb').1
  have hT1 : ∀ i < n, pg w (mask w) T1 i < n := fun i hi => by
    rw [hP1 ⟨i, hi⟩]
    exact Fin.is_lt _
  have hpc : ∀ i < n, pg w (mask w) (pcomp n w (mask w) T0 T1) i < n := fun i hi => by
    rw [PackFld.pg_pcomp hn32 hi, hP0 ⟨_, hT1 i hi⟩]
    exact Fin.is_lt _
  have hcan : canonK n w (mask w) (n * w) (pcomp n w (mask w) T0 T1) = true := by
    unfold canonK szOK
    have h1 : Nat.blt n 16777216 = true := Nat.blt_eq.mpr (by have := hb.2.2.1; omega)
    have h2' : Nat.blt (Nat.succ n) (Nat.shiftLeft 1 w) = true := by
      rw [Nat.blt_eq, PackFld.shl_eq, Nat.one_mul]
      exact hb.2.1
    have h3 : Nat.beq (Nat.shiftRight (pcomp n w (mask w) T0 T1) (n * w)) 0 = true := by
      rw [Nat.beq_eq]
      exact PackFld.pcomp_shr hn32 hw
    rw [h1, h2', h3, PackFld.allN_of_forall fun i hi => Nat.blt_eq.mpr (hpc i hi)]
  rw [hpK _ hcan]
  congr 1
  have hcnt0 : a < (CFSG.Certificates.ChainArrays.lev n S base 0).pts.size := by rw [← A0.cnt]; exact ha
  have hcnt1 : b < (CFSG.Certificates.ChainArrays.lev n S base 1).pts.size := by rw [← A1.cnt]; exact hb'
  have R0 := (A0.tr a hcnt0).1
  have R1 := (A1.tr b hcnt1).1
  unfold CFSG.Sporadic.RuSchreier.prod2A
  rw [e0, e1]
  apply Array.ext
  · simp [compA, unpack]
  · intro i h1 _
    have hi : i < n := by simpa [compA] using h1
    rw [← getElem!_pos _ i h1, ← getElem!_pos _ i (by simpa [unpack] using hi),
      CFSG.Monster.B.Co2.compA_get hi, Raw.Orb.unpack_get hi, PackFld.pg_pcomp hn32 hi,
      R1 ⟨i, hi⟩, ← hP1 ⟨i, hi⟩, R0 ⟨_, hT1 i hi⟩, ← hP0 ⟨_, hT1 i hi⟩]

private theorem row2K_iff {n w : Nat} {LR TR : Nat → Nat} {pK : Nat → Bool} {a : Nat} :
    row2K n w (mask w) (n * w) LR TR pK a = true ↔ ∀ b < rcnt (LR 1),
      pK (pcomp n w (mask w) (TR (roff n (n * w) (LR 0) + a))
        (TR (roff n (n * w) (LR 1) + b))) = true := by
  unfold row2K
  simp only [PackFld.strictB_eqP]
  constructor
  · intro h b hb
    have := allN_spec h b hb
    exact this
  · intro h
    exact PackFld.allN_of_forall fun b hb => h b hb

theorem all2_of_rows {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {p : Array Nat → Bool} {pK : Nat → Bool}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (h2 : 2 ≤ nb)
    (hpK : ∀ G, canonK n w (mask w) (n * w) G = true → pK G = p (unpack n w G))
    (h : ∀ a < rcnt (LR 0), row2K n w (mask w) (n * w) LR TR pK a = true) :
    CFSG.Sporadic.RuSchreier.all2 n (rawLevels n S base) p = true := by
  obtain ⟨c0, c1, hprod⟩ := prod2_facts hb hp hl h2 hpK
  unfold CFSG.Sporadic.RuSchreier.all2
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro a ha
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro b hb'
  rw [c0] at ha
  rw [c1] at hb'
  rw [hprod a ha b hb']
  exact row2K_iff.1 (h a ha) b hb'

theorem all2_false_of_row {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {p : Array Nat → Bool} {pK : Nat → Bool}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (h2 : 2 ≤ nb)
    (hpK : ∀ G, canonK n w (mask w) (n * w) G = true → pK G = p (unpack n w G))
    {a : Nat} (ha : a < rcnt (LR 0)) (h : row2K n w (mask w) (n * w) LR TR pK a = false) :
    CFSG.Sporadic.RuSchreier.all2 n (rawLevels n S base) p = false := by
  obtain ⟨c0, c1, hprod⟩ := prod2_facts hb hp hl h2 hpK
  apply Bool.eq_false_iff.2
  intro hall
  unfold CFSG.Sporadic.RuSchreier.all2 at hall
  rw [CFSG.Monster.B.Co2.allLt_iff] at hall
  have ha' := hall a (by rw [c0]; exact ha)
  rw [CFSG.Monster.B.Co2.allLt_iff] at ha'
  have hr : row2K n w (mask w) (n * w) LR TR pK a = true := row2K_iff.2 fun b hb' => by
    rw [← hprod a ha b hb']
    exact ha' b (by rw [c1]; exact hb')
  rw [h] at hr
  exact Bool.false_ne_true hr

end CFSG.KS.SporSch

end
