module

public import CFSG.Certificates.Kernel.BabyMonster.LatCheck

public section

namespace CFSG.KC.BM.Lat

open CFSG.KC.BM CFSG.KC.BM.B64 CFSG.KC.YModel

@[expose] noncomputable def b64Mask : Nat := nat_lit 10633823810298881998972995141504073728

@[expose] noncomputable def b64Tbl : Nat := nat_lit 1170122250367812253792561161953783704940108079513007214268205706402001729237779462942684488284441401481494778077403596574861169050028540041073156461921684986860117725882011662041029298022003281605426490249264467222426812416

@[expose] noncomputable def isB64T (c : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight b64Mask c) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def b64vT (c : Nat) : Nat :=
  Nat.land (Nat.shiftRight b64Tbl (Nat.mul (nat_lit 6) c)) (nat_lit 63)

set_option maxRecDepth 100000 in
theorem isB64_lt : ∀ c < 256, isB64 c = isB64T c := by decide +kernel

set_option maxRecDepth 100000 in
theorem b64v_lt : ∀ c < 256, b64v c = b64vT c := by decide +kernel

theorem isB64_eq (c : Nat) : isB64 c = isB64T c := by
  rcases Nat.lt_or_ge c 256 with h | h
  · exact isB64_lt c h
  · have e1 : ∀ lo hi, hi < c → inR lo hi c = false := fun lo hi hc => by
      unfold inR
      have : Nat.ble c hi = false := by
        cases h' : Nat.ble c hi
        · rfl
        · have := Nat.le_of_ble_eq_true h'; omega
      rw [this]; cases Nat.ble lo c <;> rfl
    have hb : Nat.shiftRight b64Mask c = 0 := by
      show b64Mask >>> c = 0
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) h))
    have e2 : ∀ k, k < 256 → Nat.beq c k = false := fun k hk => by
      cases h' : Nat.beq c k
      · rfl
      · have := Nat.eq_of_beq_eq_true h'; omega
    unfold isB64 isB64T
    rw [e1 65 90 (by omega), e1 97 122 (by omega), e1 48 57 (by omega), e2 43 (by decide),
      e2 47 (by decide), e2 61 (by decide), hb]
    rfl

theorem b64v_eq (c : Nat) : b64v c = b64vT c := by
  rcases Nat.lt_or_ge c 256 with h | h
  · exact b64v_lt c h
  · have e1 : ∀ lo hi, hi < c → inR lo hi c = false := fun lo hi hc => by
      unfold inR
      have : Nat.ble c hi = false := by
        cases h' : Nat.ble c hi
        · rfl
        · have := Nat.le_of_ble_eq_true h'; omega
      rw [this]; cases Nat.ble lo c <;> rfl
    have hb : Nat.shiftRight b64Tbl (Nat.mul 6 c) = 0 := by
      show b64Tbl >>> (6 * c) = 0
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (show b64Tbl < 2 ^ 738 by decide +kernel)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    have e2 : ∀ k, k < 256 → Nat.beq c k = false := fun k hk => by
      cases h' : Nat.beq c k
      · rfl
      · have := Nat.eq_of_beq_eq_true h'; omega
    unfold b64v b64vT
    rw [e1 65 90 (by omega), e1 97 122 (by omega), e1 48 57 (by omega), e2 43 (by decide),
      e2 47 (by decide), hb]
    rfl

@[expose] noncomputable def quadVG (bv : Nat → Nat) (N q : Nat) : Nat :=
  (fun i => Nat.lor (Nat.lor (Nat.shiftLeft (bv (chAt N i)) (nat_lit 18))
      (Nat.shiftLeft (bv (chAt N (Nat.add i (nat_lit 1)))) (nat_lit 12)))
    (Nat.lor (Nat.shiftLeft (bv (chAt N (Nat.add i (nat_lit 2)))) (nat_lit 6))
      (bv (chAt N (Nat.add i (nat_lit 3))))))
  (Nat.mul (nat_lit 4) q)

@[expose] noncomputable def segDecG (bv : Nat → Nat) (N q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k ih => forceB ih (fun a =>
      Nat.lor a (Nat.shiftLeft (tripleOf (quadVG bv N k)) (Nat.mul (nat_lit 24) k)))) q

@[expose] noncomputable def pieceOKG (isB : Nat → Bool) (last : Bool) (p : Nat × Nat) : Bool :=
  andB (Bool.rec (motive := fun _ => Bool) (Nat.beq p.2 (nat_lit 256)) (Nat.ble p.2 (nat_lit 256))
      last)
    (Nat.rec (motive := fun _ => Bool) true
      (fun k ih => andB ih (Bool.rec (motive := fun _ => Bool)
        (andB (Nat.beq (chAt p.1 k) (nat_lit 10)) (andB (Nat.beq (Nat.succ k) p.2) last))
        true (isB (chAt p.1 k)))) p.2)

@[expose] noncomputable def winOfG (isB : Nat → Bool) (bv : Nat → Nat) (L : List (Nat × Nat)) (c : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ acc => acc)
    (fun p t ih c m acc => Bool.rec (motive := fun _ => Nat) acc
      (Bool.rec (motive := fun _ => Nat) (Nat.shiftLeft (nat_lit 1) (nat_lit 1073741824))
        (forceB (Nat.lor acc (Nat.shiftLeft (segDecG bv p.1 (nat_lit 64)) (Nat.mul (nat_lit 1536) m)))
          (fun a => ih (Nat.sub c (nat_lit 1)) (Nat.succ m) a))
        (pieceOKG isB (isNilP t) p))
      (Nat.blt (nat_lit 0) c))
    L c (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def rowsOKG (isB : Nat → Bool) (bv : Nat → Nat) (L : List (Nat × Nat))
    (Bs : List (List Nat)) (i c : Nat) : Bool :=
  (fun p0 pe => (fun W => Nat.rec (motive := fun _ => Bool) true
      (fun k ih => andB ih (rowOK Bs W (Nat.mul (nat_lit 1536) p0) (Nat.add i k))) c)
    (winOfG isB bv (dropP L (Nat.succ p0)) (Nat.sub pe p0)))
    (Nat.div (Nat.mul (nat_lit 7) (entBefore i)) (nat_lit 1536))
    (Nat.div (Nat.add (Nat.mul (nat_lit 7) (entBefore (Nat.add i c))) (nat_lit 1535)) (nat_lit 1536))

theorem rowsOK_eq_G (L : List (Nat × Nat)) (Bs : List (List Nat)) (i c : Nat) :
    rowsOK L Bs i c = rowsOKG isB64 b64v L Bs i c := rfl

theorem rowsOK_fast (L : List (Nat × Nat)) (Bs : List (List Nat)) (i c : Nat) :
    rowsOK L Bs i c = rowsOKG isB64T b64vT L Bs i c := by
  rw [rowsOK_eq_G, show isB64 = isB64T from funext isB64_eq, show b64v = b64vT from funext b64v_eq]

end CFSG.KC.BM.Lat

end
