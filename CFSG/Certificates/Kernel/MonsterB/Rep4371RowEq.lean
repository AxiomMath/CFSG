module

public import Certificates.Data.Kernel.MonsterB.Rep4371Row
public import CFSG.Certificates.Kernel.KDense.KeysSound
public import CFSG.Monster.B.Rep4371.GlueDefs

public section

namespace CFSG.KC.Rep4371Row

open CFSG.KC CFSG.KC.KDense CFSG.KC.Loop CFSG.KC.Trace6091 CFSG.Monster.B

@[expose] noncomputable def encB (r : Bool × Bool × Nat) : Nat := enc r.1.toNat r.2.1.toNat r.2.2

@[expose] def thenB (g : Bool → Nat → Bool × Bool × Nat) (r : Bool × Bool × Nat) :
    Bool × Bool × Nat :=
  (r.1 ^^ (g r.2.1 r.2.2).1, (g r.2.1 r.2.2).2.1, (g r.2.1 r.2.2).2.2)

theorem bAnd_true {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem recAnd (f : Nat → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) true (fun i ih => Bool.rec (motive := fun _ => Bool) false ih (f i))
      n = true → ∀ i < n, f i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    obtain ⟨h1, h2⟩ := bAnd_true h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
    · exact recAnd f n h2 i hlt
    · exact h1

theorem allBelow_spec {m hi : Nat} {f : Nat → Bool} (h : allBelow m hi f = true)
    (hm : m ≤ 64 * hi) : ∀ i < m, f i = true := by
  intro i him
  have h1 := recAnd (fun h => Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft h 6) l), ih2)) 64) hi h
    (i / 64) (by omega)
  have h2 := recAnd (fun l => (fun i => bIf(Nat.blt i m, f i, true))
    (Nat.add (Nat.shiftLeft (i / 64) 6) l)) 64 h1 (i % 64) (Nat.mod_lt _ (by decide))
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq, (rfl : (2 : Nat) ^ 6 = 64)]
    omega
  have hb : Nat.blt i m = true := by
    rw [Nat.blt_eq]
    exact him
  dsimp only at h2
  rw [e, hb] at h2
  exact h2

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem enc_def (s η c : Nat) : enc s η c = s + 2 * η + 4 * c := by
  unfold enc
  change s + (2 * η + 4 * c) = _
  omega

theorem toNat_lt (b : Bool) : b.toNat < 2 := by cases b <;> decide

theorem encB_inj {r r' : Bool × Bool × Nat} (h : encB r = encB r') : r = r' := by
  obtain ⟨s, η, c⟩ := r
  obtain ⟨s', η', c'⟩ := r'
  simp only [encB, enc_def] at h
  cases s <;> cases η <;> cases s' <;> cases η' <;> simp at h ⊢ <;> omega

theorem encB_beq (r r' : Bool × Bool × Nat) (h : encB r = encB r') : (r == r') = true := by
  rw [encB_inj h]
  exact beq_self_eq_true r'

theorem land1_enc (s η c : Nat) (hs : s < 2) : Nat.land (enc s η c) 1 = s := by
  change enc s η c &&& 1 = s
  rw [Nat.and_one_is_mod, enc_def]
  omega

theorem bit1_enc (s η c : Nat) (hs : s < 2) (hη : η < 2) : bitN (enc s η c) 1 = η := by
  change (enc s η c >>> 1) &&& 1 = η
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, enc_def]
  omega

theorem shr2_enc (s η c : Nat) (hs : s < 2) (hη : η < 2) : Nat.shiftRight (enc s η c) 2 = c := by
  change enc s η c >>> 2 = c
  rw [Nat.shiftRight_eq_div_pow, enc_def]
  omega

theorem xor1_even (m : Nat) : (2 * m) ^^^ 1 = 2 * m + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  cases i with
  | zero =>
    simp only [Nat.testBit_zero]
    have h1 : 2 * m % 2 = 0 := by omega
    have h2 : (2 * m + 1) % 2 = 1 := by omega
    rw [h1, h2]
    decide
  | succ i =>
    rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    have h1 : 2 * m / 2 = m := by omega
    have h2 : (2 * m + 1) / 2 = m := by omega
    rw [h1, h2]
    simp

theorem xor_enc (s η c t : Nat) (hs : s < 2) (ht : t < 2) :
    Nat.xor (enc s η c) t = enc (s ^^^ t) η c := by
  change enc s η c ^^^ t = _
  rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
  · rw [Nat.xor_zero, Nat.xor_zero]
  · have hm : enc s η c = 2 * (η + 2 * c) + s := by
      rw [enc_def]
      omega
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
    · rw [hm, Nat.add_zero, xor1_even, enc_def]
      change _ = 1 + _ + _
      omega
    · rw [hm, ← xor1_even, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, enc_def]
      change _ = 0 + _ + _
      omega

theorem thenT_eq (f : Nat → Nat → Nat) (g : Bool → Nat → Bool × Bool × Nat)
    (hf : ∀ η c, f η.toNat c = encB (g η c)) (r : Bool × Bool × Nat) :
    thenT f (encB r) = encB (thenB g r) := by
  obtain ⟨s, η, c⟩ := r
  unfold thenT
  rw [strictN_eq]
  simp only [encB]
  rw [bit1_enc _ _ _ (toNat_lt s) (toNat_lt η), shr2_enc _ _ _ (toNat_lt s) (toNat_lt η),
    land1_enc _ _ _ (toNat_lt s), hf η c]
  simp only [encB, thenB]
  rw [xor_enc _ _ _ _ (toNat_lt _) (toNat_lt s), ← toNat_xor, Bool.xor_comm]

theorem pi0T_eq (c : Nat) : pi0T c = Model.pi0N c := by
  unfold pi0T Model.pi0N
  rw [bitN_eq, selB_toNat]
  rfl

theorem shiftT_eq (a c : Nat) : shiftT a c = Model.shiftN a c := by
  unfold shiftT Model.shiftN
  rw [pi0T_eq]
  rfl

theorem pi0_testBit (c : Nat) : (Model.pi0N c).testBit 0 = false := by
  unfold Model.pi0N
  cases h : c.testBit 0
  · rw [ite_eq_right (by simp), Nat.xor_zero, h]
  · rw [ite_eq_left rfl, Nat.testBit_xor, h]
    decide

theorem pi0_of {a : Nat} (h : a.testBit 0 = false) : Model.pi0N a = a := by
  unfold Model.pi0N
  rw [ite_eq_right (by simp [h]), Nat.xor_zero]

theorem pi0_pi0 (c : Nat) : Model.pi0N (Model.pi0N c) = Model.pi0N c :=
  pi0_of (pi0_testBit c)

theorem pi0_lt {c : Nat} (hc : c < 4096) : Model.pi0N c < 4096 := by
  have h12 : (4096 : Nat) = 2 ^ 12 := rfl
  rw [h12] at hc ⊢
  unfold Model.pi0N
  split
  · exact Nat.xor_lt_two_pow hc (by decide)
  · rw [Nat.xor_zero]
    exact hc

theorem pi0_two_mul (c : Nat) : 2 * (Model.pi0N c / 2) = Model.pi0N c := by
  have := Nat.mod_two_eq_zero_iff_testBit_zero.2 (pi0_testBit c)
  omega

theorem eYN_pi0 (a : Nat) (η : Bool) (c : Nat) : Model.eYN a η (Model.pi0N c) = Model.eYN a η c := by
  unfold Model.eYN
  rw [pi0_pi0]

theorem ePermN_pi0 (p : Array Nat) (η : Bool) (c : Nat) :
    Model.ePermN p η (Model.pi0N c) = Model.ePermN p η c := by
  unfold Model.ePermN
  rw [pi0_pi0]

theorem ePauliN_pi0 (q : Model.Pauli) (η : Bool) (c : Nat) :
    Model.ePauliN q η (Model.pi0N c) = Model.ePauliN q η c := by
  unfold Model.ePauliN
  rw [pi0_pi0]

theorem shr1_and1 (n : Nat) : Nat.land (Nat.shiftRight n 1) 1 = (n / 2 % 2 == 1).toNat := by
  change (n >>> 1) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (n / 2) with h | h <;> simp [h]

theorem kT_eq (a c : Nat) : kT a c = (Model.kN a c).toNat := by
  unfold kT Model.kN
  rw [KeysOKAux.popc24_eq, Rep4371.native_popcN, wordT_eq, wordT_eq, shr1_and1]
  rfl

theorem toNat_beq_one (b : Bool) : Nat.beq b.toNat 1 = b := by cases b <;> rfl

theorem eYT_eq (a : Nat) (η : Bool) (c : Nat) : eYT a η.toNat c = encB (Model.eYN a η c) := by
  unfold eYT
  rw [strictN_eq, toNat_beq_one, pi0T_eq]
  cases η
  · simp only [Model.eYN, Bool.false_eq_true, ite_false, encB, Model.thetaBit]
    rw [thetaT_eq, pairT_eq, shiftT_eq]
    rfl
  · simp only [Model.eYN, ite_true, encB]
    rw [kT_eq]
    rfl

theorem ePauliT_eq (s : Bool) (a d : Nat) (η : Bool) (c : Nat) :
    ePauliT s.toNat a d η.toNat c = encB (Model.ePauliN (s, a, d) η c) := by
  unfold ePauliT
  rw [strictN_eq, pi0T_eq, shiftT_eq]
  simp only [Model.ePauliN, encB, Model.mu0N, Nat.xor_eq, Nat.land_eq]
  rw [pairT_eq, pairT_eq, bitN_eq, ← toNat_and, ← toNat_xor, ← toNat_xor, ← toNat_xor]

theorem ePermT_eq {P : Nat} {p : Array Nat} (hP : ∀ i < 24, pe P i = p[i]!) {BT K : Nat}
    (hBT : betaTabT P = BT) (hK : (Model.kappaN p 63).toNat = K) (η : Bool) (c : Nat) :
    ePermT P BT K η.toNat c = encB (Model.ePermN p η c) := by
  unfold ePermT
  rw [strictN_eq, strictN_eq, pi0T_eq, pi0T_eq, permCT_eq hP, ← hBT, kappaT_eq hP, ← hK,
    bitN_eq]
  simp only [Model.ePermN, encB, Model.mu0N, Nat.xor_eq, Nat.land_eq]
  rw [← toNat_xor, ← toNat_and, ← toNat_xor]

section Sigma

variable {P : Nat} {p : Array Nat} (hP : ∀ i < 24, pe P i = p[i]!) {BT K : Nat}
  (hBT : betaTabT P = BT) (hK : (Model.kappaN p 63).toNat = K)

include hP hBT hK

theorem sigT_eq (A : Nat) (η : Bool) (c : Nat) :
    sigT A P BT K η.toNat c = encB (thenB (Model.ePermN p) (Model.eYN A η c)) := by
  unfold sigT
  rw [eYT_eq, thenT_eq _ _ (ePermT_eq hP hBT hK)]

theorem sqT_eq (A : Nat) (η : Bool) (c : Nat) :
    sqT A P BT K η.toNat c = encB (thenB (fun η c => thenB (Model.ePermN p) (Model.eYN A η c))
      (thenB (Model.ePermN p) (Model.eYN A η c))) := by
  unfold sqT
  rw [sigT_eq hP hBT hK, thenT_eq _ _ (sigT_eq hP hBT hK A)]

end Sigma

end CFSG.KC.Rep4371Row

end
