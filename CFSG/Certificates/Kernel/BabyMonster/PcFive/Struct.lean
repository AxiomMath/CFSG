module

public import CFSG.Certificates.Kernel.BabyMonster.PcFive.Cover

public section

namespace CFSG.KC.BM.PcFive

variable {G : Type*} [Group G]

@[expose] def qOne (x h : G) : G := (x * h ^ 3) ^ 8

@[expose] def qW (x h : G) : Fin 4 → G :=
  ![qOne x h, h⁻¹ * qOne x h * h, x⁻¹ * qOne x h * x, x⁻¹ * (h⁻¹ * qOne x h * h) * x]

@[expose] def zW (x h : G) : G := (qW x h 0)⁻¹ * (qW x h 1)⁻¹ * qW x h 0 * qW x h 1

structure FiveRel (x h : G) : Prop where
  x5 : x ^ 5 = 1
  h8 : h ^ 8 = 1
  q5 : qW x h 0 ^ 5 = 1
  z5 : zW x h ^ 5 = 1
  z1 : zW x h ≠ 1
  zq : ∀ i, qW x h i * zW x h = zW x h * qW x h i
  zx : x * zW x h = zW x h * x
  c01 : qW x h 0 * qW x h 1 = qW x h 1 * qW x h 0 * zW x h
  c02 : qW x h 0 * qW x h 2 = qW x h 2 * qW x h 0 * zW x h ^ 4
  c03 : qW x h 0 * qW x h 3 = qW x h 3 * qW x h 0 * zW x h
  c12 : qW x h 1 * qW x h 2 = qW x h 2 * qW x h 1
  c13 : qW x h 1 * qW x h 3 = qW x h 3 * qW x h 1 * zW x h ^ 2
  c23 : qW x h 2 * qW x h 3 = qW x h 3 * qW x h 2 * zW x h
  ax2 : x⁻¹ * qW x h 2 * x = nfQ (qW x h) (zW x h) xAct.r2
  ax3 : x⁻¹ * qW x h 3 * x = nfQ (qW x h) (zW x h) xAct.r3
  ah1 : h⁻¹ * qW x h 1 * h = nfQ (qW x h) (zW x h) hAct.r1
  ah2 : h⁻¹ * qW x h 2 * h = nfQ (qW x h) (zW x h) hAct.r2
  ah3 : h⁻¹ * qW x h 3 * h = nfQ (qW x h) (zW x h) hAct.r3
  ahz : h⁻¹ * zW x h * h = zW x h ^ 2

inductive Lt
  | h
  | hi
  | x
  | xi

@[expose] def evalW (x h : G) : List Lt → G
  | [] => 1
  | .h :: w => h * evalW x h w
  | .hi :: w => h⁻¹ * evalW x h w
  | .x :: w => x * evalW x h w
  | .xi :: w => x⁻¹ * evalW x h w

@[expose] def iterQ (f : QV → QV) : ℕ → QV → QV
  | 0, a => a
  | k + 1, a => iterQ f k (f a)

@[expose] def conjW : List Lt → QV → QV
  | [], a => a
  | .h :: w, a => iterQ (applyQ cmFive hAct) 7 (conjW w a)
  | .hi :: w, a => applyQ cmFive hAct (conjW w a)
  | .x :: w, a => phiAt 4 (conjW w a)
  | .xi :: w, a => phiAt 1 (conjW w a)

@[expose] def nW : ℕ → List Lt
  | 0 => [.h, .xi, .h, .h, .xi, .xi, .h, .xi]
  | 1 => [.h, .xi, .xi, .h, .h, .xi, .h, .h, .xi, .h, .x, .h, .h, .h]
  | _ => [.hi, .hi, .x, .hi, .x, .h, .x]

@[expose] def sW (m : ℕ) : List Lt := if m = 7 then [.hi] else [.h]

@[expose] def cwIdx : List ℕ :=
  [0, 1617, 988, 625, 125, 1, 0, 0, 126, 29, 6, 1, 0, 0, 0, 25, 7, 1, 0, 0, 0, 0, 6, 1, 0, 0, 0, 0,
    0, 1, 0, 0, 0, 0, 0, 0]

@[expose] def sig (x h : G) : Fin 6 → G :=
  ![x, qW x h 0, qW x h 1, qW x h 2, qW x h 3, zW x h]

@[expose] def NaRel (x h : G) : Prop :=
  ∀ j < 3, evalW x h (nW j) * x * (evalW x h (nW j))⁻¹ =
    psi x (qW x h) (zW x h) (dec (nth (autAt j) 0))

@[expose] def Fact13625 (x h : G) : Prop :=
  (∀ i, sig x h i ^ 5 = 1) ∧
    (∀ i j : Fin 6, i < j → sig x h i * sig x h j * (sig x h i)⁻¹ =
      psi x (qW x h) (zW x h) (dec (nth cwIdx (6 * i.val + j.val)))) ∧
    zW x h ≠ 1 ∧
    (∀ j < 3, AutRel x (qW x h) (zW x h) (evalW x h (nW j)) (autAt j)) ∧
    (∀ m < 11, evalW x h (sW m) * psi x (qW x h) (zW x h) (dec (nth singleSrc m)) *
      (evalW x h (sW m))⁻¹ = psi x (qW x h) (zW x h) (dec (nth singleTgt m)))

theorem flip_comm {a b z : G} {k n : ℕ} (h : a * b = b * a * z ^ k) (hz : z ^ 5 = 1)
    (hkn : k + n = 5) : b * a = a * b * z ^ n := by
  have e : (z ^ k)⁻¹ = z ^ n := by
    rw [inv_eq_iff_mul_eq_one, ← pow_add, hkn, hz]
  rw [← e, h]
  group

theorem conjInv_pow' (g y : G) (n : ℕ) : (g⁻¹ * y * g) ^ n = g⁻¹ * y ^ n * g := by
  rw [← conjInv_apply, ← conjInv_apply, map_pow]

variable {x h : G}

theorem FiveRel.qrel (R : FiveRel x h) : QRel cmFive (qW x h) (zW x h) where
  z5 := R.z5
  q5 i := by
    have e1 : qW x h 1 ^ 5 = 1 := by
      have e : qW x h 1 = h⁻¹ * qW x h 0 * h := rfl
      rw [e, conjInv_pow', R.q5]
      group
    fin_cases i
    · exact R.q5
    · exact e1
    · change (x⁻¹ * qW x h 0 * x) ^ 5 = 1
      rw [conjInv_pow', R.q5]
      group
    · change (x⁻¹ * qW x h 1 * x) ^ 5 = 1
      rw [conjInv_pow', e1]
      group
  zc i := (R.zq i).symm
  s01 := flip_comm (k := 1) (by rw [pow_one]; exact R.c01) R.z5 rfl
  s02 := flip_comm R.c02 R.z5 rfl
  s03 := flip_comm (k := 1) (by rw [pow_one]; exact R.c03) R.z5 rfl
  s12 := by rw [R.c12]; simp [cmFive]
  s13 := flip_comm R.c13 R.z5 rfl
  s23 := flip_comm (k := 1) (by rw [pow_one]; exact R.c23) R.z5 rfl

theorem nfQ_unit2 (q : Fin 4 → G) (z : G) : nfQ q z ⟨0, 0, 1, 0, 0⟩ = q 2 := by simp [nfQ]

theorem FiveRel.pcHyp (R : FiveRel x h) : PcHyp x (qW x h) (zW x h) where
  rel := R.qrel
  x5 := R.x5
  x0 := by simp [nfQ, xAct, qW]
  x1 := by simp [nfQ, xAct, qW]
  x2 := R.ax2
  x3 := R.ax3
  xz := by
    simp only [nfQ, xAct, pow_zero, one_mul, pow_one]
    rw [mul_assoc, ← R.zx]
    group

theorem FiveRel.conjH (R : FiveRel x h) (a : QV) :
    h⁻¹ * nfQ (qW x h) (zW x h) a * h = nfQ (qW x h) (zW x h) (applyQ cmFive hAct a) :=
  conj_nfQ R.qrel (by simp [nfQ, hAct, qW]) R.ah1 R.ah2 R.ah3
    (by rw [R.ahz]; simp [nfQ, hAct]) a

theorem FiveRel.conjH_pow (R : FiveRel x h) : ∀ (k : ℕ) (a : QV),
    (h ^ k)⁻¹ * nfQ (qW x h) (zW x h) a * h ^ k =
      nfQ (qW x h) (zW x h) (iterQ (applyQ cmFive hAct) k a)
  | 0, a => by simp [iterQ]
  | k + 1, a => by rw [conj_pow_succ, R.conjH, R.conjH_pow k, iterQ]

theorem phiAt_red (k : ℕ) {a : QV} (ha : a.red) : (phiAt k a).red := by
  unfold phiAt
  cases k.beq 0 <;> cases k.beq 1 <;> cases k.beq 2 <;> cases k.beq 3 <;>
    simp only [cond_true, cond_false] <;> first | exact ha | exact evalQF_red _ _

theorem conjW_red : ∀ (w : List Lt) {a : QV}, a.red → (conjW w a).red
  | [], _, ha => ha
  | .h :: w, _, ha => by
    unfold conjW
    unfold iterQ iterQ iterQ iterQ iterQ iterQ iterQ iterQ
    exact mulQ_red _ _ _
  | .hi :: w, _, _ => mulQ_red _ _ _
  | .x :: w, _, ha => phiAt_red 4 (conjW_red w ha)
  | .xi :: w, _, ha => phiAt_red 1 (conjW_red w ha)

theorem FiveRel.conjW_spec (R : FiveRel x h) (hφ : phiOK () = true) :
    ∀ (w : List Lt) {a : QV}, a.red →
      evalW x h w * nfQ (qW x h) (zW x h) a * (evalW x h w)⁻¹ =
        nfQ (qW x h) (zW x h) (conjW w a)
  | [], _, _ => by simp [evalW, conjW]
  | l :: w, a, ha => by
    have ih := R.conjW_spec hφ w ha
    have hb := conjW_red w ha
    have e : ∀ g : G, g * evalW x h w * nfQ (qW x h) (zW x h) a * (g * evalW x h w)⁻¹ =
        g * nfQ (qW x h) (zW x h) (conjW w a) * g⁻¹ := fun g => by
      rw [← ih]; group
    have H := R.pcHyp
    cases l with
    | h =>
      unfold evalW conjW
      rw [e, ← R.conjH_pow 7]
      have h7 : h⁻¹ = h ^ 7 := by
        rw [inv_eq_iff_mul_eq_one, ← pow_succ', R.h8]
      rw [← h7, inv_inv]
    | hi =>
      unfold evalW conjW
      rw [e, inv_inv, R.conjH]
    | x =>
      unfold evalW conjW
      rw [e, ← H.conjX_pow hφ (by norm_num : 4 < 5) hb]
      have x4 : x⁻¹ = x ^ 4 := by
        rw [inv_eq_iff_mul_eq_one, ← pow_succ', R.x5]
      rw [← x4, inv_inv]
    | xi =>
      unfold evalW conjW
      have c1 := H.conjX_pow hφ (by norm_num : 1 < 5) hb
      rw [pow_one] at c1
      rw [e, inv_inv, c1]

theorem psi_dec_Q {q : Fin 4 → G} {z : G} {n : ℕ} (hn : n < 3125) :
    psi x q z (dec n) = nfQ q z (decQ n) := by
  unfold psi dec
  have e1 : n / 3125 % 5 = 0 := by omega
  have e2 : n % 3125 = n := by omega
  simp only [e1, e2, pow_zero, one_mul]

theorem FiveRel.conj_psiQ (R : FiveRel x h) (hφ : phiOK () = true) (w : List Lt) {n n' : ℕ}
    (hn : n < 3125) (hn' : n' < 3125) (hc : (conjW w (decQ n)).beq (decQ n') = true) :
    evalW x h w * psi x (qW x h) (zW x h) (dec n) * (evalW x h w)⁻¹ =
      psi x (qW x h) (zW x h) (dec n') := by
  rw [psi_dec_Q hn, psi_dec_Q hn', R.conjW_spec hφ w (decQ_red n), QV.beq_eq hc]

@[expose] def genIdx : List ℕ := [3125, 625, 125, 25, 5, 1]

theorem sig_eq (i : Fin 6) : sig x h i = psi x (qW x h) (zW x h) (dec (nth genIdx i.val)) := by
  fin_cases i <;> simp [sig, psi, nfQ, dec, decQ, nth, genIdx]

theorem relCheck : ∀ i j : Fin 6, i < j →
    (mulV (mulV (dec (nth genIdx i.val)) (dec (nth genIdx j.val)))
      (powV (dec (nth genIdx i.val)) 4)).beq (dec (nth cwIdx (6 * i.val + j.val))) = true := by
  decide +kernel

theorem autCheck : ∀ j < 3, ∀ i < 5, nth genIdx (i + 1) < 3125 ∧ nth (autAt j) (i + 1) < 3125 ∧
    (conjW (nW j) (decQ (nth genIdx (i + 1)))).beq (decQ (nth (autAt j) (i + 1))) = true := by
  decide +kernel

theorem singleCheck : ∀ m < 11, nth singleSrc m < 3125 ∧ nth singleTgt m < 3125 ∧
    (conjW (sW m) (decQ (nth singleSrc m))).beq (decQ (nth singleTgt m)) = true := by
  decide +kernel

theorem fact13625_of (R : FiveRel x h) (hN : NaRel x h) (hφ : phiOK () = true) :
    Fact13625 x h := by
  have H := R.pcHyp
  have hsig5 : ∀ i, sig x h i ^ 5 = 1 := by
    intro i
    rw [sig_eq, H.psi_pow hφ (dec_red _)]
    have : powV (dec (nth genIdx i.val)) 5 = V6.one := by
      apply V6.beq_eq
      fin_cases i <;> decide +kernel
    rw [this, psi_one]
  refine ⟨hsig5, fun i j hij => ?_, R.z1, fun j hj => ?_, fun m hm => ?_⟩
  · have hinv : (sig x h i)⁻¹ = sig x h i ^ 4 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', hsig5]
    rw [hinv, sig_eq i, sig_eq j, H.psi_pow hφ (dec_red _), H.psi_mul hφ (dec_red _) (dec_red _),
      H.psi_mul hφ (mulV_red _ _) (powV_red _ _), V6.beq_eq (relCheck i j hij)]
  · have hq : ∀ (i : ℕ) (hi : i < 5), evalW x h (nW j) * sig x h ⟨i + 1, by omega⟩ * (evalW x h (nW j))⁻¹ =
        psi x (qW x h) (zW x h) (dec (nth (autAt j) (i + 1))) := by
      intro i hi
      obtain ⟨h1, h2, h3⟩ := autCheck j hj i hi
      rw [sig_eq]
      exact R.conj_psiQ hφ _ h1 h2 h3
    refine ⟨hN j hj, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [sig] using hq 0 (by norm_num)
    · simpa [sig] using hq 1 (by norm_num)
    · simpa [sig] using hq 2 (by norm_num)
    · simpa [sig] using hq 3 (by norm_num)
    · simpa [sig] using hq 4 (by norm_num)
  · obtain ⟨h1, h2, h3⟩ := singleCheck m hm
    exact R.conj_psiQ hφ _ h1 h2 h3

end CFSG.KC.BM.PcFive

end
