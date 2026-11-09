module

public import Certificates.Data.Kernel.OpsLayFillOne
public import Certificates.Data.Kernel.OpsRenL
public import CFSG.Certificates.Kernel.LocalQTSecLemmas
import CFSG.Certificates.Kernel.OpsLayMcertSound
import CFSG.Certificates.Kernel.CosetLat.MatEnc
import all CFSG.Certificates.Kernel.Spor.OrdSound

public section

namespace CFSG.KC.OpsLayK

open CFSG.KC.LQT CFSG.KS.Ord

theorem chain_conj_monoid {M : Type*} [Monoid M] {a y x : M} (ha : a * a = 1)
    (hy : y * (y * y) = 1) (hx : x = y * (a * y * a * (a * y * a))) (hxy : x * y = y * x) :
    x * (x * x) = 1 ∧ a * x = x * x * a := by
  have haa : ∀ t, a * (a * t) = t := fun t => by rw [← mul_assoc, ha, one_mul]
  have hyy : ∀ t, y * (y * (y * t)) = t := fun t => by
    calc y * (y * (y * t)) = y * (y * y) * t := by simp only [mul_assoc]
      _ = t := by rw [hy, one_mul]
  obtain ⟨b, hb⟩ : ∃ b, b = a * (y * (y * a)) := ⟨_, rfl⟩
  have hxb : x = y * b := by
    rw [hx, hb]
    simp only [mul_assoc, haa]
  have hb3 : b * (b * b) = 1 := by
    rw [hb]
    simp only [mul_assoc, haa, hyy, ha]
  have hby : b * y = y * b := by
    calc b * y = y * (y * (y * (b * y))) := (hyy _).symm
      _ = y * (y * (x * y)) := by rw [hxb, mul_assoc]
      _ = y * (y * (y * x)) := by rw [hxy]
      _ = y * b := by rw [hxb, hyy]
  have hbyt : ∀ t, b * (y * t) = y * (b * t) := fun t => by
    rw [← mul_assoc, hby, mul_assoc]
  have h3 : x * (x * x) = 1 := by
    rw [hxb]
    simp only [mul_assoc, hbyt, hyy, hb3]
  have hxxx : ∀ t, x * (x * (x * t)) = t := fun t => by
    calc x * (x * (x * t)) = x * (x * x) * t := by simp only [mul_assoc]
      _ = t := by rw [h3, one_mul]
  have hu : a * (x * (a * x)) = 1 := by
    rw [hxb, hb]
    simp only [mul_assoc, haa, hyy, ha]
  refine ⟨h3, ?_⟩
  calc a * x = a * (x * (a * x)) * (x * (x * a)) := by simp only [mul_assoc, hxxx, ha, mul_one]
    _ = x * x * a := by rw [hu, one_mul, mul_assoc]

theorem chain_conj {c : Lay} (hc : c.ok = true) {a y V W Z x Y2 : Nat}
    (hca : Canon c.p c.d c.w a) (hcy : Canon c.p c.d c.w y)
    (hV : c.mul a y = V) (hW : c.mul V a = W) (hZ : c.mul W W = Z) (hx : c.mul y Z = x)
    (ha : c.mul a a = c.ONE) (hy1 : c.mul y y = Y2) (hy2 : c.mul y Y2 = c.ONE)
    (hxy : c.mul x y = c.mul y x) :
    c.mul x (c.mul x x) = c.ONE ∧ c.mul a x = c.mul (c.mul x x) a := by
  obtain ⟨-, hS, hw, -⟩ := consts_facts hc
  have h1 := one_sound hc
  have key : ∀ {X Y : Nat}, Canon c.p c.d c.w X → Canon c.p c.d c.w Y →
      ordMat c.p c.d c.w c.S X = ordMat c.p c.d c.w c.S Y → X = Y := fun hX hY h =>
    CFSG.KC.CosetLat.canon_eq_of_ordMat hw hX hY (by rw [← hS]; exact h)
  obtain ⟨cV, mV⟩ := SecS.mul_sound c hc hca hcy
  rw [hV] at cV mV
  obtain ⟨cW, mW⟩ := SecS.mul_sound c hc cV hca
  rw [hW] at cW mW
  obtain ⟨cZ, mZ⟩ := SecS.mul_sound c hc cW cW
  rw [hZ] at cZ mZ
  obtain ⟨cx, mx⟩ := SecS.mul_sound c hc hcy cZ
  rw [hx] at cx mx
  obtain ⟨cY2, mY2⟩ := SecS.mul_sound c hc hcy hcy
  rw [hy1] at cY2 mY2
  have ma := (SecS.mul_sound c hc hca hca).2
  rw [ha, h1.2] at ma
  have my := (SecS.mul_sound c hc hcy cY2).2
  rw [hy2, h1.2, mY2] at my
  have mxy := (SecS.mul_sound c hc cx hcy).2
  rw [hxy, (SecS.mul_sound c hc hcy cx).2] at mxy
  have hxM : ordMat c.p c.d c.w c.S x = ordMat c.p c.d c.w c.S y *
      (ordMat c.p c.d c.w c.S a * ordMat c.p c.d c.w c.S y * ordMat c.p c.d c.w c.S a *
        (ordMat c.p c.d c.w c.S a * ordMat c.p c.d c.w c.S y * ordMat c.p c.d c.w c.S a)) := by
    rw [mx, mZ, mW, mV]
  obtain ⟨g1, g2⟩ := chain_conj_monoid ma.symm my.symm hxM mxy.symm
  obtain ⟨cxx, mxx⟩ := SecS.mul_sound c hc cx cx
  refine ⟨key (SecS.mul_sound c hc cx cxx).1 h1.1 ?_,
    key (SecS.mul_sound c hc hca cx).1 (SecS.mul_sound c hc cxx hca).1 ?_⟩
  · rw [(SecS.mul_sound c hc cx cxx).2, mxx, h1.2]
    exact g1
  · rw [(SecS.mul_sound c hc hca cx).2, (SecS.mul_sound c hc cxx hca).2, mxx]
    exact g2

theorem strictB_chain (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem chunkV_mul3 {c : Lay} {i j s0 s1 s2 : Nat} {S' : List Nat}
    (h : chunkV c (4, [[0, i, j, 3]], [0, 1, 2, 3]) [s0, s1, s2] S' = true) :
    S' = [s0, s1, s2, c.mul ([s0, s1, s2, c.ONE].getD i c.ONE)
      ([s0, s1, s2, c.ONE].getD j c.ONE)] := by
  change strictB (c.mul (getR c [s0, s1, s2, c.ONE] i) (getR c [s0, s1, s2, c.ONE] j))
    (fun v => eqL ([0, 1, 2, 3].map (getR c ([s0, s1, s2, c.ONE].set 3 v))) S') = true at h
  rw [strictB_chain] at h
  exact (eq_of_eqL h).symm

theorem chunkV_mul4 {c : Lay} {i j s0 s1 s2 s3 : Nat} {S' : List Nat}
    (h : chunkV c (4, [[0, i, j, 3]], [0, 1, 2, 3]) [s0, s1, s2, s3] S' = true) :
    S' = [s0, s1, s2, c.mul ([s0, s1, s2, s3].getD i c.ONE)
      ([s0, s1, s2, s3].getD j c.ONE)] := by
  change strictB (c.mul (getR c [s0, s1, s2, s3] i) (getR c [s0, s1, s2, s3] j))
    (fun v => eqL ([0, 1, 2, 3].map (getR c ([s0, s1, s2, s3].set 3 v))) S') = true at h
  rw [strictB_chain] at h
  exact (eq_of_eqL h).symm

theorem chunkV_pow4 {c : Lay} {e i s0 s1 s2 s3 : Nat} {S' : List Nat}
    (h : chunkV c (4, [[e + 1, i, 0, 3]], [0, 1, 2, 3]) [s0, s1, s2, s3] S' = true) :
    S' = [s0, s1, s2, powK c ([s0, s1, s2, s3].getD i c.ONE) (e + 1)] := by
  change strictB (powK c (getR c [s0, s1, s2, s3] i) (e + 1))
    (fun v => eqL ([0, 1, 2, 3].map (getR c ([s0, s1, s2, s3].set 3 v))) S') = true at h
  rw [strictB_chain] at h
  exact (eq_of_eqL h).symm

theorem chunkV_mul3_02 {c : Lay} {s0 s1 s2 : Nat} {S' : List Nat}
    (h : chunkV c (4, [[0, 0, 2, 3]], [0, 1, 2, 3]) [s0, s1, s2] S' = true) :
    c.mul s0 s2 = S'.getD 3 0 := by
  rw [chunkV_mul3 h]
  rfl

theorem chunkV_mul4_30 {c : Lay} {s0 s1 s2 s3 : Nat} {S' : List Nat}
    (h : chunkV c (4, [[0, 3, 0, 3]], [0, 1, 2, 3]) [s0, s1, s2, s3] S' = true) :
    c.mul s3 s0 = S'.getD 3 0 := by
  rw [chunkV_mul4 h]
  rfl

theorem chunkV_mul4_23 {c : Lay} {s0 s1 s2 s3 : Nat} {S' : List Nat}
    (h : chunkV c (4, [[0, 2, 3, 3]], [0, 1, 2, 3]) [s0, s1, s2, s3] S' = true) :
    c.mul s2 s3 = S'.getD 3 0 := by
  rw [chunkV_mul4 h]
  rfl

theorem chunkV_sq4_3 {c : Lay} {s0 s1 s2 s3 : Nat} {S' : List Nat}
    (h : chunkV c (4, [[2, 3, 0, 3]], [0, 1, 2, 3]) [s0, s1, s2, s3] S' = true) :
    c.mul s3 s3 = S'.getD 3 0 := by
  rw [chunkV_pow4 (e := 1) h, ← powK_two]
  rfl

theorem factL1_ord3_eq {c : Lay} {R : List Nat} {n r : Nat} (hr : decide (r < n) = true)
    (h : c.mul (getR c R r) (c.mul (getR c R r) (getR c R r)) = c.ONE) :
    factL1 c R n (.ord r 3) = true := by
  simp only [factL1, Bool.and_eq_true, hr, powK_three, h, Nat.beq_refl]
  decide

theorem factL1_conj_eq {c : Lay} {R : List Nat} {n h a e b f U W : Nat}
    (hok : (decide (h < n) && wordOK n [(a, e)] && wordOK n [(b, f)]) = true)
    (hU : powK c (getR c R a) e = U) (hW : powK c (getR c R b) f = W)
    (h1 : c.mul (getR c R h) U = c.mul W (getR c R h)) :
    factL1 c R n (.conj h [(a, e)] [(b, f)]) = true := by
  simp only [factL1, evalWL1, Bool.and_eq_true] at hok ⊢
  rw [hU, hW, h1]
  exact ⟨hok, Nat.beq_refl _⟩

end CFSG.KC.OpsLayK

end
