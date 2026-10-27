module

public import Certificates.Data.Kernel.SporSch.J4STok
public import CFSG.Sporadic.Schreier.PairText
import CFSG.Certificates.Kernel.Spor.HexText

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum

private def tokI (neg : Bool) (cur : Nat) : Int := if neg = true then -(cur : Int) else (cur : Int)

private def stepT (st : Array Int × Nat × Bool × Bool) (c : Nat) : Array Int × Nat × Bool × Bool :=
  if (decide (48 ≤ c) && decide (c ≤ 57)) = true then (st.1, st.2.1 * 10 + (c - 48), st.2.2.1, true)
  else if (c == 45) = true then (st.1, st.2.1, true, st.2.2.2)
  else if st.2.2.2 = true then (st.1.push (tokI st.2.2.1 st.2.1), 0, false, false)
  else (st.1, 0, false, false)

private def finT (st : Array Int × Nat × Bool × Bool) : Array Int :=
  if st.2.2.2 = true then st.1.push (tokI st.2.2.1 st.2.1) else st.1

private theorem ite_pure_yield' {β : Type} (c : Prop) [Decidable c] (a b : β) :
    (if c then pure (ForInStep.yield a) else pure (ForInStep.yield b) : Id (ForInStep β)) =
      pure (ForInStep.yield (if c then a else b)) := by
  split <;> rfl

private theorem tokens_eq (s : String) : CFSG.Sporadic.Schreier.PairText.tokens s =
    finT ((List.range' 0 s.toUTF8.size).foldl (fun st i => stepT st (s.toUTF8.get! i).toNat)
      (#[], 0, false, false)) := by
  simp only [CFSG.Sporadic.Schreier.PairText.tokens, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, ite_pure_yield', List.forIn_pure_yield_eq_foldl,
    Nat.add_sub_cancel, Nat.div_one, Nat.sub_zero]
  rfl

private theorem strictB_eqT (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem bAnd_eq (a b : Bool) : bAnd(a, b) = (a && b) := by
  cases a <;> rfl

private theorem bAnd_true {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

private theorem tokEq_sound {x : Int} {neg : Bool} {cur : Nat} (h : tokEq x neg cur = true) :
    x = tokI neg cur := by
  unfold tokI
  cases x with
  | ofNat k =>
    change bAnd(Nat.beq k cur, bIf(neg, Nat.beq cur (nat_lit 0), true)) = true at h
    obtain ⟨h1, h2⟩ := bAnd_true h
    have e := Nat.eq_of_beq_eq_true h1
    subst e
    cases neg
    · rfl
    · have e0 := Nat.eq_of_beq_eq_true h2
      subst e0
      rfl
  | negSucc k =>
    change bAnd(neg, Nat.beq (Nat.succ k) cur) = true at h
    obtain ⟨h1, h2⟩ := bAnd_true h
    have e := Nat.eq_of_beq_eq_true h2
    subst e h1
    rfl

private theorem emitK_sound {neg : Bool} {cur : Nat} {k : List Int → Bool} :
    ∀ {rem : List Int}, emitK neg cur rem k = true → ∃ r, rem = tokI neg cur :: r ∧ k r = true
  | [], h => absurd h Bool.false_ne_true
  | x :: xs, h => by
    change bAnd(tokEq x neg cur, k xs) = true at h
    obtain ⟨h1, h2⟩ := bAnd_true h
    exact ⟨xs, by rw [tokEq_sound h1], h2⟩

private theorem nilK_sound : ∀ {rem : List Int}, nilK rem = true → rem = []
  | [], _ => rfl
  | _ :: _, h => absurd h Bool.false_ne_true

private theorem ble_eq' (a b : Nat) : Nat.ble a b = decide (a ≤ b) :=
  Bool.eq_iff_iff.mpr (by rw [Nat.ble_eq, decide_eq_true_iff])

private theorem beq_eq' (a b : Nat) : Nat.beq a b = (a == b) :=
  Bool.eq_iff_iff.mpr (by rw [beq_iff_eq, Nat.beq_eq])

private theorem tokRun_sound : ∀ (cs : List Char) (out : Array Int) (cur : Nat) (neg inTok : Bool)
    (rem : List Int), tokRun cs cur neg inTok rem = true →
    (∀ c ∈ cs, c.toNat < 128) ∧
      (finT ((cs.map Char.toNat).foldl stepT (out, cur, neg, inTok))).toList = out.toList ++ rem
  | [], out, cur, neg, inTok, rem, h => by
    change bIf(inTok, emitK neg cur rem nilK, nilK rem) = true at h
    refine ⟨fun c hc => absurd hc List.not_mem_nil, ?_⟩
    unfold finT
    cases inTok
    · rw [nilK_sound h]
      simp
    · obtain ⟨r, hr, hn⟩ := emitK_sound h
      rw [hr, nilK_sound hn]
      simp
  | ch :: cs, out, cur, neg, inTok, rem, h => by
    change strictB (Char.toNat ch) (fun c =>
      bAnd(Nat.blt c (nat_lit 128),
      bIf(bAnd(Nat.ble (nat_lit 48) c, Nat.ble c (nat_lit 57)),
        strictB (Nat.add (Nat.mul cur (nat_lit 10)) (Nat.sub c (nat_lit 48)))
          (fun cur' => tokRun cs cur' neg true rem),
        bIf(Nat.beq c (nat_lit 45), tokRun cs cur true inTok rem,
          bIf(inTok, emitK neg cur rem (fun r => tokRun cs (nat_lit 0) false false r),
            tokRun cs (nat_lit 0) false false rem))))) = true at h
    simp only [strictB_eqT] at h
    obtain ⟨h128, h⟩ := bAnd_true h
    have hc : ch.toNat < 128 := Nat.blt_eq.mp h128
    rw [bAnd_eq, ble_eq', ble_eq', beq_eq'] at h
    rw [List.map_cons, List.foldl_cons]
    have hall : ∀ {P : Prop}, (∀ c ∈ cs, c.toNat < 128) ∧ P →
        (∀ c ∈ ch :: cs, c.toNat < 128) ∧ P :=
      fun hP => ⟨fun c hc' => by
        rcases List.mem_cons.mp hc' with e | e
        · rw [e]
          exact hc
        · exact hP.1 c e, hP.2⟩
    cases hD : (decide (48 ≤ ch.toNat) && decide (ch.toNat ≤ 57)) <;> rw [hD] at h
    · cases hM : (ch.toNat == 45) <;> rw [hM] at h
      · cases inTok
        · have e : stepT (out, cur, neg, false) ch.toNat = (out, 0, false, false) := by
            unfold stepT
            rw [hD, hM]
            rfl
          rw [e]
          exact hall (tokRun_sound cs out 0 false false rem h)
        · obtain ⟨r, hr, hn⟩ := emitK_sound h
          have e : stepT (out, cur, neg, true) ch.toNat =
              (out.push (tokI neg cur), 0, false, false) := by
            unfold stepT
            rw [hD, hM]
            rfl
          rw [e, hr]
          have ih := tokRun_sound cs (out.push (tokI neg cur)) 0 false false r hn
          refine hall ⟨ih.1, ?_⟩
          rw [ih.2]
          simp
      · have e : stepT (out, cur, neg, inTok) ch.toNat = (out, cur, true, inTok) := by
          unfold stepT
          rw [hD, hM]
          rfl
        rw [e]
        exact hall (tokRun_sound cs out cur true inTok rem h)
    · have e : stepT (out, cur, neg, inTok) ch.toNat =
          (out, cur * 10 + (ch.toNat - 48), neg, true) := by
        unfold stepT
        rw [hD]
        rfl
      rw [e]
      exact hall (tokRun_sound cs out _ neg true rem h)

private theorem utf8_size_ascii' : ∀ cs : List Char,
    (∀ k < cs.length, (cs[k]!).toNat < 128) → cs.utf8Encode.size = cs.length
  | [], _ => rfl
  | c :: cs, h => by
    have hc : c.toNat < 128 := by simpa using h 0 (by simp)
    rw [List.utf8Encode_cons, CFSG.KS.HexText.utf8_single hc, ByteArray.size_append,
      utf8_size_ascii' cs (fun k hk => by simpa using h (k + 1) (by simp; omega))]
    simp
    omega

private theorem foldl_range_eq {β : Type} (f : β → Nat → β) (x : Nat → Nat) (L : List Nat)
    (hx : ∀ i < L.length, x i = L[i]!) (b : β) :
    (List.range' 0 L.length).foldl (fun st i => f st (x i)) b = L.foldl f b := by
  have e : (List.range' 0 L.length).map x = L := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      rw [List.getElem_map, List.getElem_range', Nat.zero_add, Nat.one_mul, hx i h2,
        getElem!_pos L i h2]
  rw [← List.foldl_map (f := x) (g := f), e]

theorem tokK_sound {cs : List Char} {L : List Int} (h : tokK cs L = true) :
    CFSG.Sporadic.Schreier.PairText.tokens (String.ofList cs) = L.toArray := by
  obtain ⟨hasc, hres⟩ := tokRun_sound cs #[] _ _ _ L h
  have hasc' : ∀ k < cs.length, k < cs.length ∧ (cs[k]!).toNat < 128 := fun k hk =>
    ⟨hk, by rw [getElem!_pos cs k hk]; exact hasc _ (List.getElem_mem hk)⟩
  have hb : (String.ofList cs).toUTF8 = cs.utf8Encode := by
    rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
  rw [tokens_eq, hb, utf8_size_ascii' cs (fun k hk => (hasc' k hk).2)]
  have hx : ∀ i < (cs.map Char.toNat).length, (cs.utf8Encode.get! i).toNat =
      (cs.map Char.toNat)[i]! := by
    intro i hi
    rw [List.length_map] at hi
    rw [CFSG.KS.HexText.utf8_get cs cs.length hasc' i hi, UInt8.toNat_ofNat',
      Nat.mod_eq_of_lt (by have := (hasc' i hi).2; omega),
      getElem!_pos (cs.map Char.toNat) i (by simpa using hi), List.getElem_map,
      getElem!_pos cs i hi]
  have e := foldl_range_eq stepT (fun i => (cs.utf8Encode.get! i).toNat) (cs.map Char.toNat) hx
    (#[], 0, false, false)
  rw [List.length_map] at e
  rw [e]
  apply Array.ext'
  rw [hres]
  simp

end CFSG.KS.SporSch

end
