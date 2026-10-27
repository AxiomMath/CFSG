module

public import Certificates.Data.Kernel.Spor.Text
import CFSG.Certificates.Kernel.Spor.TextJoin
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.HexText
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import Certificates.Data.CFSGNative.Co3Schreier.Basic

public section

namespace CFSG.KS.Text

open CFSG.Sporadic.Schreier.Co3.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.PackFld CFSG.KS.HexText

private theorem R_nil (wd n w lines start cnt : Nat) (F : Nat → Nat) (L e t v acc : Nat) :
    run wd n w lines start cnt F [] L e t v acc = nilC lines L e t v acc := rfl

private theorem R_cons (wd n w lines start cnt : Nat) (F : Nat → Nat) (ch : Char) (A : List Char)
    (L e t v acc : Nat) :
    run wd n w lines start cnt F (ch :: A) L e t v acc =
      stepC wd n w start cnt F ch A (run wd n w lines start cnt F A) L e t v acc := rfl

private theorem nil_false {lines L e t v acc : Nat} (hL : L < lines) :
    nilC lines L e t v acc = false := by
  unfold nilC
  have h : Nat.beq L lines = false := by
    cases hb : Nat.beq L lines
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) (by omega)
  rw [h]

private theorem digitsT {cs : List Char} {wd n w lines start cnt : Nat} {F : Nat → Nat}
    {L e o acc : Nat} (hL : L < lines) (he : e < n) : ∀ c t, t + c = wd → t < wd →
    run wd n w lines start cnt F (cs.drop (o + t)) L e t (numA cs o t) acc = true →
    (∀ s, t ≤ s → s < wd → o + s < cs.length ∧ hexV (Char.toNat cs[o + s]!) < 16) ∧
    numA cs o wd < 2 ^ w ∧
    run wd n w lines start cnt F (cs.drop (o + wd)) L (e + 1) 0 0
      (Nat.lor acc (Nat.shiftLeft (numA cs o wd) (Nat.mul w e))) = true := by
  intro c
  induction c with
  | zero => intro t h1 h2; omega
  | succ c ih =>
    intro t hc htd hr
    have hb : Nat.blt e n = true := Nat.blt_eq.mpr he
    have hlen : o + t < cs.length := by
      apply Nat.lt_of_not_le
      intro hl
      rw [List.drop_eq_nil_of_le hl, R_nil, nil_false hL] at hr
      exact Bool.false_ne_true hr
    rw [List.drop_eq_getElem_cons hlen, R_cons] at hr
    have hget : cs[o + t]! = cs[o + t] := getElem!_pos cs (o + t) hlen
    have hv' : Nat.add (Nat.mul (numA cs o t) 16) (hexV (Char.toNat cs[o + t])) =
        numA cs o (t + 1) := by
      rw [numA, hget]
      rfl
    cases hh : Nat.blt (hexV (Char.toNat cs[o + t])) 16
    · rw [stepC_bad2 hb hh] at hr
      exact absurd hr Bool.false_ne_true
    have hdig : hexV (Char.toNat cs[o + t]!) < 16 := by
      rw [hget]
      exact Nat.blt_eq.mp hh
    cases ht : Nat.beq (Nat.succ t) wd
    · have htd' : t + 1 < wd := by
        have := false_of_beq ht
        omega
      rw [stepC_dig hb hh ht, hv'] at hr
      have e1 : o + t + 1 = o + (t + 1) := by omega
      rw [e1] at hr
      obtain ⟨a, b, c1⟩ := ih (t + 1) (by omega) htd' hr
      refine ⟨fun s hs1 hs2 => ?_, b, c1⟩
      rcases Nat.lt_or_ge s (t + 1) with hs | hs
      · have : s = t := by omega
        subst this
        exact ⟨hlen, hdig⟩
      · exact a s hs hs2
    · have htd' : t + 1 = wd := Nat.eq_of_beq_eq_true ht
      have hch : ∀ s, t ≤ s → s < wd → o + s < cs.length ∧ hexV (Char.toNat cs[o + s]!) < 16 := by
        intro s hs1 hs2
        have : s = t := by omega
        subst this
        exact ⟨hlen, hdig⟩
      cases hv : Nat.blt (Nat.add (Nat.mul (numA cs o t) 16) (hexV (Char.toNat cs[o + t])))
          (Nat.shiftLeft 1 w)
      · rw [stepC_bad3 hb hh ht hv] at hr
        exact absurd hr Bool.false_ne_true
      have hV : numA cs o wd < 2 ^ w := by
        have := Nat.blt_eq.mp hv
        rw [hv', htd', shl_eq, Nat.one_mul] at this
        exact this
      have hdrop : o + t + 1 = o + wd := by omega
      rw [stepC_ent hb hh ht hv, hv', htd', hdrop] at hr
      exact ⟨hch, hV, hr⟩

private theorem entriesT {cs : List Char} {wd n w lines start cnt : Nat} {F : Nat → Nat} {L : Nat}
    (hL : L < lines) (hwd : 0 < wd) : ∀ r e acc, e + r = n →
    Fld w acc (fun i => if i < e then numA cs (L * (wd * n + 1) + wd * i) wd else 0) →
    run wd n w lines start cnt F (cs.drop (L * (wd * n + 1) + wd * e)) L e 0 0 acc = true →
    (∀ i, e ≤ i → i < n → numA cs (L * (wd * n + 1) + wd * i) wd < 2 ^ w ∧
      ∀ s < wd, L * (wd * n + 1) + wd * i + s < cs.length ∧
        hexV (Char.toNat cs[L * (wd * n + 1) + wd * i + s]!) < 16) ∧
    ∃ a, Fld w a (fun i => if i < n then numA cs (L * (wd * n + 1) + wd * i) wd else 0) ∧
      run wd n w lines start cnt F (cs.drop (L * (wd * n + 1) + wd * n)) L n 0 0 a = true := by
  intro r
  induction r with
  | zero =>
    intro e acc hr hacc hrun
    have : e = n := by omega
    subst this
    exact ⟨fun i h1 h2 => absurd h2 (by omega), acc, hacc, hrun⟩
  | succ r ih =>
    intro e acc hr hacc hrun
    have he : e < n := by omega
    obtain ⟨hch, hV, hnext⟩ := digitsT (cs := cs) (o := L * (wd * n + 1) + wd * e) (acc := acc)
      (start := start) (cnt := cnt) (F := F) hL he wd 0 (by omega) hwd
      (by rw [Nat.add_zero]; exact hrun)
    have hacc' : Fld w (Nat.lor acc (Nat.shiftLeft (numA cs (L * (wd * n + 1) + wd * e) wd)
        (Nat.mul w e))) (fun i => if i < e + 1 then numA cs (L * (wd * n + 1) + wd * i) wd else 0) := by
      refine fld_congr (fld_or hacc (fld_shl e (fld_one hV))) ?_
      intro i
      by_cases h1 : i < e
      · have h2 : ¬ e ≤ i := by omega
        have h3 : i < e + 1 := by omega
        rw [iteT h1, iteF h2, iteT h3, Nat.or_zero]
      · by_cases h2 : i = e
        · subst h2
          rw [iteF h1, iteT (Nat.le_refl i), Nat.sub_self, iteT rfl, iteT (Nat.lt_succ_self i),
            Nat.zero_or]
        · have h3 : ¬ i < e + 1 := by omega
          have h4 : i - e ≠ 0 := by omega
          rw [iteF h1, iteF h3, Nat.zero_or]
          by_cases h5 : e ≤ i
          · rw [iteT h5, iteF h4]
          · rw [iteF h5]
    have hstep : L * (wd * n + 1) + wd * e + wd = L * (wd * n + 1) + wd * (e + 1) := by
      rw [Nat.mul_succ wd e, Nat.add_assoc]
    rw [hstep] at hnext
    obtain ⟨a, b⟩ := ih (e + 1) _ (by omega) hacc' hnext
    refine ⟨fun i hi1 hi2 => ?_, b⟩
    rcases Nat.lt_or_ge i (e + 1) with h | h
    · have : i = e := by omega
      subst this
      exact ⟨hV, fun s hs => hch s (Nat.zero_le s) hs⟩
    · exact a i h hi2

private def LineOK (cs : List Char) (wd n w start cnt : Nat) (F : Nat → Nat) (L : Nat) : Prop :=
  (∀ i < n, numA cs (L * (wd * n + 1) + wd * i) wd < 2 ^ w ∧
    ∀ s < wd, L * (wd * n + 1) + wd * i + s < cs.length ∧
      hexV (Char.toNat cs[L * (wd * n + 1) + wd * i + s]!) < 16) ∧
  (L * (wd * n + 1) + wd * n < cs.length ∧ Char.toNat cs[L * (wd * n + 1) + wd * n]! = 10) ∧
  (start ≤ L → L < start + cnt →
    Fld w (F (L - start)) (fun i => if i < n then numA cs (L * (wd * n + 1) + wd * i) wd else 0))

private theorem lineT {cs : List Char} {wd n w lines start cnt : Nat} {F : Nat → Nat} {L : Nat}
    (hL : L < lines) (hwd : 0 < wd)
    (hrun : run wd n w lines start cnt F (cs.drop (L * (wd * n + 1))) L 0 0 0 0 = true) :
    LineOK cs wd n w start cnt F L ∧
      run wd n w lines start cnt F (cs.drop ((L + 1) * (wd * n + 1))) (L + 1) 0 0 0 0 = true := by
  have h0 : Fld w 0 (fun i => if i < 0 then numA cs (L * (wd * n + 1) + wd * i) wd else 0) :=
    fld_congr (fld_zero w) (fun i => (iteF (Nat.not_lt_zero i)).symm)
  obtain ⟨hent, a, ha, hra⟩ := entriesT (cs := cs) (F := F) (start := start) (cnt := cnt) hL hwd
    n 0 0 (by omega) h0 (by rw [Nat.mul_zero, Nat.add_zero]; exact hrun)
  have hlen : L * (wd * n + 1) + wd * n < cs.length := by
    apply Nat.lt_of_not_le
    intro hl
    rw [List.drop_eq_nil_of_le hl, R_nil, nil_false hL] at hra
    exact Bool.false_ne_true hra
  rw [List.drop_eq_getElem_cons hlen, R_cons] at hra
  have hget : cs[L * (wd * n + 1) + wd * n]! = cs[L * (wd * n + 1) + wd * n] :=
    getElem!_pos cs _ hlen
  have hb : Nat.blt n n = false := by
    cases h : Nat.blt n n
    · rfl
    · exact absurd (Nat.blt_eq.mp h) (Nat.lt_irrefl n)
  cases hn : Nat.beq (Char.toNat cs[L * (wd * n + 1) + wd * n]) 10
  · rw [stepC_bad1 hb hn] at hra
    exact absurd hra Bool.false_ne_true
  rw [stepC_nl hb hn] at hra
  obtain ⟨hc, hnext⟩ := (bAnd_iff _ _).1 hra
  have hpos : L * (wd * n + 1) + wd * n + 1 = (L + 1) * (wd * n + 1) := by
    rw [Nat.succ_mul]
    omega
  rw [hpos] at hnext
  refine ⟨⟨fun i hi => hent i (Nat.zero_le i) hi,
    ⟨hlen, by rw [hget]; exact Nat.eq_of_beq_eq_true hn⟩, fun h1 h2 => ?_⟩, hnext⟩
  have e1 : Nat.ble start L = true := Nat.ble_eq.mpr h1
  have e2 : Nat.blt L (Nat.add start cnt) = true := Nat.blt_eq.mpr h2
  unfold cmpC at hc
  rw [e1] at hc
  try dsimp only at hc
  rw [e2] at hc
  have hF : a = F (L - start) := Nat.eq_of_beq_eq_true hc
  rw [← hF]
  exact ha

private theorem linesT {cs : List Char} {wd n w lines start cnt : Nat} {F : Nat → Nat}
    (hwd : 0 < wd) : ∀ r L, L + r = lines →
    run wd n w lines start cnt F (cs.drop (L * (wd * n + 1))) L 0 0 0 0 = true →
    ∀ L', L ≤ L' → L' < lines → LineOK cs wd n w start cnt F L' := by
  intro r
  induction r with
  | zero => intro L h1 _ L' h2 h3; omega
  | succ r ih =>
    intro L hr hrun L' h1 h2
    obtain ⟨hl, hnext⟩ := lineT (lines := lines) (by omega) hwd hrun
    rcases Nat.lt_or_ge L L' with h | h
    · exact ih (L + 1) (by omega) hnext L' h h2
    · have : L' = L := by omega
      subst this
      exact hl

private theorem pos_lt {wd n lines L i s : Nat} (hL : L < lines) (hi : i < n) (hs : s < wd) :
    L * (wd * n + 1) + wd * i + s < lines * (wd * n + 1) := by
  have h1 : wd * i + wd ≤ wd * n := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ hi
  have h2 : (L + 1) * (wd * n + 1) ≤ lines * (wd * n + 1) := Nat.mul_le_mul_right _ hL
  rw [Nat.succ_mul] at h2
  omega

theorem hexBind_sound {cs : List Char} {wd n w lines start cnt : Nat} {F : Nat → Nat}
    (h : hexBind cs wd n w lines start cnt F = true) :
    ∀ j < cnt, hexLine (String.ofList cs).toUTF8 wd n (start + j) = CFSG.KS.Raw.unpack n w (F j) := by
  unfold hexBind at h
  obtain ⟨hwd, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hle, hr⟩ := (bAnd_iff _ _).1 h2
  have hwd' : 0 < wd := Nat.blt_eq.mp hwd
  have hle' : start + cnt ≤ lines := Nat.ble_eq.mp hle
  have T := linesT (cs := cs) (F := F) (w := w) (start := start) (cnt := cnt) (lines := lines)
    hwd' lines 0 (Nat.zero_add lines) (by rw [Nat.zero_mul, List.drop_zero]; exact hr)
  have hasc : ∀ k < lines * (wd * n + 1), k < cs.length ∧ (cs[k]!).toNat < 128 := by
    intro k hk
    have hl : 0 < wd * n + 1 := Nat.succ_pos _
    have hq : k / (wd * n + 1) < lines := (Nat.div_lt_iff_lt_mul hl).2 hk
    have hm : k % (wd * n + 1) < wd * n + 1 := Nat.mod_lt _ hl
    have ek : k = k / (wd * n + 1) * (wd * n + 1) + k % (wd * n + 1) :=
      (Nat.div_add_mod' k (wd * n + 1)).symm
    obtain ⟨hA, hB, -⟩ := T (k / (wd * n + 1)) (Nat.zero_le _) hq
    rcases Nat.lt_or_ge (k % (wd * n + 1)) (wd * n) with hr' | hr'
    · have hi : k % (wd * n + 1) / wd < n := by
        rw [Nat.div_lt_iff_lt_mul hwd', Nat.mul_comm n wd]
        exact hr'
      have er : k % (wd * n + 1) = wd * (k % (wd * n + 1) / wd) + k % (wd * n + 1) % wd :=
        (Nat.div_add_mod _ wd).symm
      obtain ⟨-, hC⟩ := hA _ hi
      obtain ⟨hlen, hx⟩ := hC (k % (wd * n + 1) % wd) (Nat.mod_lt _ hwd')
      have ek' : k = k / (wd * n + 1) * (wd * n + 1) + wd * (k % (wd * n + 1) / wd) +
          k % (wd * n + 1) % wd := by omega
      rw [← ek'] at hlen hx
      refine ⟨hlen, ?_⟩
      rcases hexV_dig hx with ⟨-, h2, -⟩ | ⟨-, h2, -⟩ <;> omega
    · have ek' : k = k / (wd * n + 1) * (wd * n + 1) + wd * n := by omega
      obtain ⟨hlen, hx⟩ := hB
      rw [← ek'] at hlen hx
      exact ⟨hlen, by omega⟩
  intro j hj
  have hL : start + j < lines := by omega
  obtain ⟨hA, -, hF⟩ := T (start + j) (Nat.zero_le _) hL
  have hFj := hF (Nat.le_add_right _ _) (by omega)
  rw [Nat.add_sub_cancel_left] at hFj
  apply Array.ext
  · simp [hexLine, CFSG.KS.Raw.unpack]
  · intro i h1 _
    have hi : i < n := by simpa [hexLine] using h1
    simp only [hexLine, CFSG.KS.Raw.unpack, Array.getElem_ofFn]
    obtain ⟨hV, hC⟩ := hA i hi
    rw [pg_of_fld hFj (by simp only [hi, ↓reduceIte]; exact hV)]
    simp only [hi, ↓reduceIte]
    exact num_bytes (o := (start + j) * (wd * n + 1) + wd * i) hasc
      (fun c => CFSG.Monster.B.Co2.Native.hexAt (String.ofList cs).toUTF8
        ((start + j) * (wd * n + 1) + wd * i) c)
      rfl (fun c => rfl) wd (by have := pos_lt hL hi (Nat.sub_lt hwd' Nat.one_pos); omega)
      (fun s hs => (hC s hs).2)

end CFSG.KS.Text

end
