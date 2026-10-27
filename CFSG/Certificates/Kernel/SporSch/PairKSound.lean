module

public import Certificates.Data.Kernel.SporSch.PairK
public import CFSG.Certificates.Kernel.Spor.RawSound
public import Certificates.Data.CFSGNative.PairSchreier.Core
import CFSG.Certificates.Kernel.Misc.HexFlatSound
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KS.SporSch

open CFSG.KS.Raw CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative
open CFSG.KC.Enum CFSG.KS CFSG.KS.PackFld
open CFSG.KS.Text (hexV)

private theorem beq_false' {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

private theorem hexTabRun_flat {wd n w cnt : Nat} {F : Nat → Nat} : ∀ (cs : List Char)
    (j e t v acc : Nat), hexTabRun wd n w cnt F cs j e t v acc = true →
    CFSG.KC.Misc.HexFlat.run wd n w cnt F cs j e t v acc = true
  | [], j, e, t, v, acc, h => by
    change bAnd(Nat.beq j cnt, bAnd(Nat.beq e (nat_lit 0), Nat.beq t (nat_lit 0))) = true at h
    rw [bAnd_iff] at h
    exact h.1
  | ch :: cs, j, e, t, v, acc, h => by
    have ih := hexTabRun_flat (wd := wd) (n := n) (w := w) (cnt := cnt) (F := F) cs
    by_cases hj : j = cnt
    · subst hj
      change bIf(Nat.beq j j, true, _) = true
      rw [Nat.beq_refl]
    · change strictB (hexV (Char.toNat ch)) (fun h => bIf(Nat.blt h (nat_lit 16), bIf(Nat.blt j cnt,
        strictB (Nat.add (Nat.mul v (nat_lit 16)) h) (fun v' =>
        bIf(Nat.beq (Nat.succ t) wd,
          bIf(Nat.blt v' (Nat.shiftLeft (nat_lit 1) w),
            strictB (Nat.lor acc (Nat.shiftLeft v' (Nat.mul w e))) (fun acc' =>
            strictB (Nat.succ e) (fun e' =>
              bIf(Nat.beq e' n,
                bAnd(Nat.beq acc' (F j),
                  strictB (Nat.succ j) (fun j' => hexTabRun wd n w cnt F cs j' (nat_lit 0)
                    (nat_lit 0) (nat_lit 0) (nat_lit 0))),
                hexTabRun wd n w cnt F cs j e' (nat_lit 0) (nat_lit 0) acc'))),
            false),
          strictB (Nat.succ t) (fun t' => hexTabRun wd n w cnt F cs j e t' v' acc))),
        false), false)) = true at h
      change bIf(Nat.beq j cnt, true,
        strictB (hexV (Char.toNat ch)) (fun h => bIf(Nat.blt h (nat_lit 16),
          strictB (Nat.add (Nat.mul v (nat_lit 16)) h) (fun v' =>
          bIf(Nat.beq (Nat.succ t) wd,
            bIf(Nat.blt v' (Nat.shiftLeft (nat_lit 1) w),
              strictB (Nat.lor acc (Nat.shiftLeft v' (Nat.mul w e))) (fun acc' =>
                bIf(Nat.beq (Nat.succ e) n,
                  bAnd(Nat.beq acc' (F j),
                    CFSG.KC.Misc.HexFlat.run wd n w cnt F cs (Nat.succ j) (nat_lit 0) (nat_lit 0)
                      (nat_lit 0) (nat_lit 0)),
                  CFSG.KC.Misc.HexFlat.run wd n w cnt F cs j (Nat.succ e) (nat_lit 0) (nat_lit 0)
                    acc')),
              false),
            CFSG.KC.Misc.HexFlat.run wd n w cnt F cs j e (Nat.succ t) v' acc)),
          false))) = true
      rw [beq_false' hj]
      simp only [strictB_eqP] at h ⊢
      cases h1 : Nat.blt (hexV (Char.toNat ch)) 16 <;> rw [h1] at h
      · exact absurd h Bool.false_ne_true
      dsimp only at h ⊢
      cases h2 : Nat.blt j cnt <;> rw [h2] at h
      · exact absurd h Bool.false_ne_true
      dsimp only at h
      cases h3 : Nat.beq (Nat.succ t) wd <;> rw [h3] at h
      · exact ih _ _ _ _ _ h
      dsimp only at h ⊢
      cases h4 : Nat.blt (Nat.add (Nat.mul v 16) (hexV (Char.toNat ch))) (Nat.shiftLeft 1 w) <;>
        rw [h4] at h
      · exact absurd h Bool.false_ne_true
      dsimp only at h ⊢
      cases h5 : Nat.beq (Nat.succ e) n <;> rw [h5] at h
      · exact ih _ _ _ _ _ h
      · dsimp only at h ⊢
        rw [bAnd_iff] at h ⊢
        exact ⟨h.1, ih _ _ _ _ _ h.2⟩

theorem hexTabK_sound {cs : List Char} {wd n w cnt : Nat} {F : Nat → Nat}
    (h : hexTabK cs wd n w cnt F = true) :
    ∀ j < cnt, hexTable wd n (n * j) (String.ofList cs) = unpack n w (F j) := by
  unfold hexTabK at h
  rw [bAnd_iff, bAnd_iff] at h
  apply CFSG.KC.Misc.HexFlat.hexTable_sound
  unfold CFSG.KC.Misc.HexFlat.hexFlat
  rw [bAnd_iff, bAnd_iff]
  exact ⟨h.1, h.2.1, hexTabRun_flat cs 0 0 0 0 0 h.2.2⟩

private theorem unpack_getElem! {n w W q : Nat} (hq : q < n) :
    (unpack n w W)[q]! = pg w (mask w) W q := by
  simp [unpack, hq]

private theorem bAnd_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

private theorem range_of_canonL {n w : Nat} : ∀ {Ws : List Nat}, canonL n w Ws = true →
    ∀ W ∈ Ws, ∀ q < n, pg w (mask w) W q < n
  | [], _, W, hW => by simp at hW
  | V :: Ws, h, W, hW => by
    change bAnd(CFSG.KS.Prim.canonK n w (mask w) (Nat.mul n w) V, canonL n w Ws) = true at h
    rw [bAnd_iff] at h
    rcases List.mem_cons.1 hW with rfl | hW
    · intro q hq
      have := allN_spec (CFSG.KS.Raw.range_of_canonK h.1) q hq
      simpa using this
    · exact range_of_canonL h.2 W hW

private theorem evRK_eq {n w : Nat} : ∀ {Ws : List Nat}, (∀ W ∈ Ws, ∀ q < n, pg w (mask w) W q < n) →
    ∀ p < n, evRK w Ws p = evR (Ws.map (unpack n w)) p ∧ evRK w Ws p < n
  | [], _, p, hp => ⟨rfl, hp⟩
  | W :: Ws, hW, p, hp => by
    have h1 := hW W List.mem_cons_self p hp
    have ih := evRK_eq (Ws := Ws) (fun V hV => hW V (List.mem_cons_of_mem _ hV)) _ h1
    change strictN (pg w (mask w) W p) (evRK w Ws) = _ ∧ strictN (pg w (mask w) W p) (evRK w Ws) < n
    rw [strictN_eqP]
    refine ⟨?_, ih.2⟩
    rw [ih.1, List.map_cons]
    change _ = evR (Ws.map (unpack n w)) ((unpack n w W)[p]!)
    rw [unpack_getElem! hp]

private theorem evPowK_eq {n w : Nat} {Ws : List Nat} (hW : ∀ W ∈ Ws, ∀ q < n, pg w (mask w) W q < n) :
    ∀ e, ∀ p < n, evPowK w Ws e p = evPow (Ws.map (unpack n w)) e p ∧ evPowK w Ws e p < n
  | 0, p, hp => ⟨rfl, hp⟩
  | e + 1, p, hp => by
    have ih := evPowK_eq hW e p hp
    change strictN (evPowK w Ws e p) (evRK w Ws) = _ ∧ strictN (evPowK w Ws e p) (evRK w Ws) < n
    rw [strictN_eqP, evPow, ← ih.1]
    exact evRK_eq hW _ ih.2

private theorem fixBK_eq {n w : Nat} {Ws : List Nat} (hW : ∀ W ∈ Ws, ∀ q < n, pg w (mask w) W q < n)
    (e : Nat) : ∀ {bs : List Nat}, ltL n bs = true →
    fixBK w bs Ws e = fixB bs (Ws.map (unpack n w)) e
  | [], _ => rfl
  | b :: bs, h => by
    change bAnd(Nat.blt b n, ltL n bs) = true at h
    rw [bAnd_iff, Nat.blt_eq] at h
    change bAnd(Nat.beq (evPowK w Ws e b) b, fixBK w bs Ws e) = _
    rw [bAnd_eq, fixBK_eq hW e h.2, (evPowK_eq hW e b h.1).1]
    simp only [fixB, List.all_cons]
    congr 1

theorem ordWK_sound {n w m : Nat} {bs Ws : List Nat} (h : ordWK n w bs Ws m = true) :
    ordB bs (Ws.map (unpack n w)) m = true := by
  unfold ordWK ordB0 at h
  rw [bAnd_iff, bAnd_iff, bAnd_iff] at h
  obtain ⟨hc, hl, hm, ha⟩ := h
  have hW := range_of_canonL hc
  have hF := fun e => fixBK_eq hW e hl
  rw [hF] at hm
  rw [ordB, hm, Bool.true_and, List.all_eq_true]
  intro e he
  simp only [CFSG.Sporadic.Schreier.Native.divParts, List.mem_map, List.mem_filter,
    List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at he
  obtain ⟨d, ⟨hd, h1, h2⟩, rfl⟩ := he
  have hd' := allN_spec ha d hd
  have e1 : Nat.blt 1 d = true := by simpa using h1
  have e2 : Nat.beq (m % d) 0 = true := by simpa using h2
  change bIf(bAnd(Nat.blt 1 d, Nat.beq (Nat.mod m d) 0), bIf(fixBK w bs Ws (Nat.div m d), false, true),
    true) = true at hd'
  rw [e1] at hd'
  change bIf(Nat.beq (m % d) 0, bIf(fixBK w bs Ws (m / d), false, true), true) = true at hd'
  rw [e2, hF] at hd'
  revert hd'
  cases fixB bs (Ws.map (unpack n w)) (m / d) <;> decide

end CFSG.KS.SporSch

end
