module

public import CFSG.Certificates.Kernel.KDenseP.Sound
public import CFSG.Certificates.Kernel.BenesSound

public section

namespace CFSG.KC.KStep

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.MonsterConv.Perm CFSG.KC.Loop
open CFSG.Monster.AxisCount

@[expose] noncomputable def resM {M : ℕ} (h : ZMod M) (v : Native.DVec) (k : ℕ) : ZMod M :=
  (v.D.getD k 0 : ZMod M) * h ^ v.e

@[expose] def scat (T : ℕ → List (ℕ × ℤ)) (p q : ℕ) : ℤ :=
  (((T p).filter (fun t => decide (t.1 = q))).map Prod.snd).sum

@[expose] def keyQ (q : ℕ) : ℕ × ℕ := Native.keyAt (Native.thetaTab ()) q

@[expose] def KeysGood : Prop :=
  (∀ q < 98280, (keyQ q).1 < 4096 ∧ (keyQ q).2 < 4096) ∧
    ∀ p < 98280, ∀ q < 98280, keyQ p = keyQ q → p = q

structure KeyBind (F : Fix) : Prop where
  ka : ∀ q < 98280, ∀ b < 12, F.keyA.testBit (b * SX + xposK q) = (keyQ q).1.testBit b
  kd : ∀ q < 98280, ∀ b < 12, F.keyD.testBit (b * SX + xposK q) = (keyQ q).2.testBit b
  pa : ∀ p < SX, (∀ q < 98280, xposK q ≠ p) → ∀ b < 12, F.keyA.testBit (b * SX + p) = false
  pd : ∀ p < SX, (∀ q < 98280, xposK q ≠ p) → ∀ b < 12, F.keyD.testBit (b * SX + p) = false
  la : F.keyA < 2 ^ (12 * SX)
  ld : F.keyD < 2 ^ (12 * SX)

structure POps where
  rep : ℕ → ℕ → ℕ
  neg : ℕ → ℕ → ℕ → ℕ
  add : ℕ → ℕ → ℕ → ℕ
  half : ℕ → ℕ → ℕ → ℕ
  bfly : ℕ → ℕ → ℕ → ℕ → ℕ
  net : ℕ → ℕ → ℕ → ℕ → ℕ
  xsw : ℕ → ℕ → ℕ → ℕ
  compact : ℕ → ℕ → ℕ
  expand : ℕ → ℕ → ℕ

@[expose] noncomputable def ops15 : POps :=
  ⟨rep4, negM, add15, fun S j x => rotk S (Nat.sub 4 j) x, bfly, net4, xsw, compact, expand⟩

@[expose] noncomputable def opsN (n lg : ℕ) : POps :=
  ⟨fun S m => repN S n m, fun S m x => negMN S n m x, fun S x y => addN S n lg x y,
    fun S j x => rotN S n (dvN n j) x, fun S b R x => bflyN S n lg b R x,
    fun S k N x => netN S n k N x, fun S b x => xswN S n b x, compactN n, expandN n⟩

@[expose] def hN (np : ℕ) : ZMod (2 ^ np - 1) := 2 ^ (np - 1)

@[expose] def Bd (np S x : ℕ) : Prop := x < 2 ^ (np * S)

@[expose] def Zero (np S x p : ℕ) : Prop := ∀ b < np, x.testBit (b * S + p) = false

structure PLaw (np : ℕ) (O : POps) : Prop where
  rep_lt : ∀ {S m}, m < 2 ^ S → Bd np S (O.rep S m)
  rep_testBit : ∀ {S m b p}, m < 2 ^ S → b < np → p < S →
    (O.rep S m).testBit (b * S + p) = m.testBit p
  neg_bd : ∀ {S m x}, m < 2 ^ S → Bd np S x → Bd np S (O.neg S m x)
  neg_res : ∀ {S m x p}, m < 2 ^ S → Bd np S x → p < S →
    resPN np S (O.neg S m x) p = if m.testBit p then -resPN np S x p else resPN np S x p
  add_bd : ∀ {S x y}, Bd np S x → Bd np S y → Bd np S (O.add S x y)
  add_res : ∀ {S x y p}, Bd np S x → Bd np S y → p < S →
    resPN np S (O.add S x y) p = resPN np S x p + resPN np S y p
  half_bd : ∀ {S j x}, 1 ≤ j → j ≤ 3 → Bd np S x → Bd np S (O.half S j x)
  half_res : ∀ {S j x p}, 1 ≤ j → j ≤ 3 → Bd np S x → p < S →
    resPN np S (O.half S j x) p = hN np ^ j * resPN np S x p
  bfly_bd : ∀ {k S b R x}, S = 2 ^ k → b < k → R < 2 ^ S → Bd np S x → Bd np S (O.bfly S b R x)
  bfly_res : ∀ {k S b R x p}, S = 2 ^ k → b < k → R < 2 ^ S →
    (∀ q < S, R.testBit q = true → q.testBit b = false → R.testBit (q + 2 ^ b) = true) →
    Bd np S x → p < S →
    resPN np S (O.bfly S b R x) p =
      if R.testBit p = false then resPN np S x p
      else if p.testBit b = false then resPN np S x p + resPN np S x (p + 2 ^ b)
      else if R.testBit (p - 2 ^ b) = true then resPN np S x (p - 2 ^ b) - resPN np S x p
      else 0
  net_bd : ∀ {k S N x}, S = 2 ^ k → netOK k N = true → Bd np S x → Bd np S (O.net S k N x)
  net_res : ∀ {k S N x p}, S = 2 ^ k → netOK k N = true → Bd np S x → p < S →
    resPN np S (O.net S k N x) p = resPN np S x (Benes.benesPerm k N p)
  xsw_bd : ∀ {k S b x}, S = 2 ^ k → b < k → Bd np S x → Bd np S (O.xsw S b x)
  xsw_res : ∀ {k S b x p}, S = 2 ^ k → b < k → Bd np S x → p < S →
    resPN np S (O.xsw S b x) p = resPN np S x (p ^^^ 2 ^ b)
  compact_bd : ∀ {o Z}, Bd np SA (O.compact o Z)
  compact_res : ∀ {o Z p}, o + SA ≤ SX → Bd np SX Z → p < SA →
    resPN np SA (O.compact o Z) p = resPN np SX Z (o + p)
  expand_bd : ∀ {o Z}, o + SA ≤ SX → Bd np SA Z → Bd np SX (O.expand o Z)
  expand_res : ∀ {o Z p}, o + SA ≤ SX → Bd np SA Z → p < SX →
    resPN np SX (O.expand o Z) p = if o ≤ p ∧ p < o + SA then resPN np SA Z (p - o) else 0
  neg_zero : ∀ {S m x p}, m < 2 ^ S → Bd np S x → p < S → m.testBit p = false → Zero np S x p →
    Zero np S (O.neg S m x) p
  add_zero : ∀ {S x y p}, Bd np S x → Bd np S y → p < S → Zero np S x p → Zero np S y p →
    Zero np S (O.add S x y) p
  half_zero : ∀ {S j x p}, 1 ≤ j → j ≤ 3 → Bd np S x → p < S → Zero np S x p →
    Zero np S (O.half S j x) p
  bfly_zero : ∀ {k S b R x p}, S = 2 ^ k → b < k → R < 2 ^ S →
    (∀ q < S, R.testBit q = true → q.testBit b = false → R.testBit (q + 2 ^ b) = true) →
    Bd np S x → p < S →
    R.testBit p = false → Zero np S x p → Zero np S (O.bfly S b R x) p
  net_zero : ∀ {k S N x p}, S = 2 ^ k → netOK k N = true → Bd np S x → p < S →
    Zero np S x (Benes.benesPerm k N p) → Zero np S (O.net S k N x) p
  xsw_zero : ∀ {k S b x p}, S = 2 ^ k → b < k → Bd np S x → p < S → Zero np S x (p ^^^ 2 ^ b) →
    Zero np S (O.xsw S b x) p
  compact_zero : ∀ {o Z p}, o + SA ≤ SX → Bd np SX Z → p < SA → Zero np SX Z (o + p) →
    Zero np SA (O.compact o Z) p
  expand_zero : ∀ {o Z p}, o + SA ≤ SX → Bd np SA Z → p < SX →
    (o ≤ p ∧ p < o + SA → Zero np SA Z (p - o)) → Zero np SX (O.expand o Z) p

@[expose] noncomputable def translG (O : POps) (S t x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun b ih y => strictN (Bool.rec (motive := fun _ => Nat) y (O.xsw S b y)
      (Nat.beq (bitN t b) (nat_lit 1))) ih)
    (nat_lit 17) x

@[expose] noncomputable def rhoG (O : POps) (F : Fix) (s a d : Nat) (X A W : Nat) : St :=
  (true, O.neg SX (Nat.xor (xorSel SX F.keyA d) (xorSel SX F.keyD a)) X, A,
    translG O SX (Nat.lor (Nat.shiftLeft (Nat.shiftRight (pi0 a) (nat_lit 1)) (nat_lit 5))
        (Nat.shiftLeft (par12 (Nat.land d (nat_lit 63))) (nat_lit 16)))
      (O.neg SX (rhoSgnW s a d) W))

@[expose] noncomputable def colxiG (O : POps) (S b0 b1 R x : Nat) : Nat :=
  dsw (Nat.sub (Nat.shiftLeft (nat_lit 1) b1) (Nat.shiftLeft (nat_lit 1) b0))
    (O.rep S (Nat.land R (Nat.land (idPlane S b0) (clr S b1))))
    (O.bfly S b1 R (O.bfly S b0 R (O.neg S (Nat.land R (Nat.land (clr S b0) (clr S b1))) x)))

@[expose] noncomputable def pinWG (O : POps) (x : Nat) : Nat :=
  dsw (nat_lit 512) (O.rep SX (Nat.land par58 (clr SX (nat_lit 9)))) x

@[expose] noncomputable def wht4G (O : POps) (x : Nat) : Nat :=
  O.bfly SX (nat_lit 8) valW (O.bfly SX (nat_lit 7) valW (O.bfly SX (nat_lit 6) valW
    (O.bfly SX (nat_lit 5) valW x)))

@[expose] noncomputable def xiG (O : POps) (F : Fix) (X A W : Nat) : Nat × Nat × Nat :=
  (O.net SX (nat_lit 17) F.xiNet (O.neg SX F.xiSgn X),
    O.half SA (nat_lit 2) (colxiG O SA (nat_lit 5) (nat_lit 6) valA (colxiG O SA (nat_lit 0) (nat_lit 1) valA A)),
    O.half SX (nat_lit 3) (O.neg SX doutM (O.net SX (nat_lit 17) F.pout
      (wht4G O (pinWG O (O.neg SX dinM (colxiG O SX (nat_lit 0) (nat_lit 1) valW W)))))))

@[expose] noncomputable def transpG (O : POps) (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun k ih y => strictN (dsw (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.add k (nat_lit 5)))
        (Nat.shiftLeft (nat_lit 1) k))
      (O.rep SA (Nat.land (idPlane SA k) (clr SA (Nat.add k (nat_lit 5))))) y) ih) (nat_lit 5) x

@[expose] noncomputable def wht6G (O : POps) (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun b ih y => strictN (O.bfly SX b regOct y) ih) (nat_lit 6) x

@[expose] noncomputable def tauG (O : POps) (F : Fix) (X A W : Nat) : Nat × Nat × Nat :=
  (fun L Xp Xq =>
    (fun d2 U =>
      (Nat.lor (O.neg SX F.sgWLo (Nat.land W L))
        (Nat.lor (O.half SX (nat_lit 3) (O.neg SX F.doct (O.net SX (nat_lit 17) F.pi6
            (wht6G O (Nat.land X (O.rep SX regOct))))))
          (Nat.lor (O.expand (nat_lit 114688) (Nat.land (O.add SA A d2) (O.rep SA upA)))
            (O.expand (nat_lit 115712) (Nat.land (O.add SA (O.neg SA upA A) d2) (O.rep SA upA))))),
       Nat.lor (Nat.land A (O.rep SA diagA)) (Nat.lor U (transpG O U)),
       Nat.lor (O.neg SX F.sgWUp (Nat.land (Nat.shiftRight W (nat_lit 65536)) L))
         (Nat.shiftLeft (O.neg SX F.sgOddUp (Nat.land X L)) (nat_lit 65536))))
      (O.half SA (nat_lit 1) (O.add SA Xp (O.neg SA upA Xq)))
      (Nat.land (O.half SA (nat_lit 1) (O.add SA Xp Xq)) (O.rep SA upA)))
    (O.rep SX lo16) (O.compact (nat_lit 114688) X) (O.compact (nat_lit 115712) X)

theorem rhoStep_eq (F : Fix) (s a d X A W : Nat) : rhoStep F s a d X A W = rhoG ops15 F s a d X A W :=
  rfl

theorem rhoStepN_eq (n lg : ℕ) (F : Fix) (s a d X A W : Nat) :
    rhoStepN n F s a d X A W = rhoG (opsN n lg) F s a d X A W :=
  rfl

theorem xiStep_eq (F : Fix) (X A W : Nat) : xiStep F X A W = xiG ops15 F X A W := rfl

theorem xiStepN_eq (n lg : ℕ) (F : Fix) (X A W : Nat) : xiStepN n lg F X A W = xiG (opsN n lg) F X A W :=
  rfl

theorem tauStep_eq (F : Fix) (X A W : Nat) : tauStep F X A W = tauG ops15 F X A W := rfl

theorem tauStepN_eq (n lg : ℕ) (F : Fix) (X A W : Nat) :
    tauStepN n lg F X A W = tauG (opsN n lg) F X A W :=
  rfl

end CFSG.KC.KStep

end
