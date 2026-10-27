module

public import Certificates.Data.Kernel.MonsterPcSeven
public import CFSG.Certificates.Kernel.BabyMonster.PcFive.Coll

public section

namespace CFSG.KC.MonPcSeven

open CFSG.KC.BM.PcFive (QV CM QAct G10 QF V6 nth allBelow memN nfQ psi pow_pow_assoc swap_assoc
  conjInv conjInv_apply conj_pow_succ allBelow_spec)

variable {G : Type*} [Group G]

structure QRel (m : CM) (q : Fin 4 → G) (z : G) : Prop where
  z7 : z ^ 7 = 1
  q7 : ∀ i, q i ^ 7 = 1
  zc : ∀ i, z * q i = q i * z
  s01 : q 1 * q 0 = q 0 * q 1 * z ^ m.m01
  s02 : q 2 * q 0 = q 0 * q 2 * z ^ m.m02
  s03 : q 3 * q 0 = q 0 * q 3 * z ^ m.m03
  s12 : q 2 * q 1 = q 1 * q 2 * z ^ m.m12
  s13 : q 3 * q 1 = q 1 * q 3 * z ^ m.m13
  s23 : q 3 * q 2 = q 2 * q 3 * z ^ m.m23

theorem pow_mod_seven {g : G} (h : g ^ 7 = 1) (n : ℕ) : g ^ n = g ^ (n % 7) := by
  conv_lhs => rw [← Nat.div_add_mod n 7, pow_add, pow_mul, h, one_pow, one_mul]

section R

variable {m : CM} {q : Fin 4 → G} {z : G}

theorem QRel.zq_assoc (h : QRel m q z) (i : Fin 4) (n l : ℕ) (X : G) :
    z ^ n * (q i ^ l * X) = q i ^ l * (z ^ n * X) := by
  rw [← mul_assoc, (Commute.pow_pow (h.zc i) n l).eq, mul_assoc]

theorem nfQ_mul (h : QRel m q z) (a b : QV) : nfQ q z a * nfQ q z b = nfQ q z (mulQ m a b) := by
  have w01 := swap_assoc (h.zc 0) (h.zc 1) h.s01
  have w02 := swap_assoc (h.zc 0) (h.zc 2) h.s02
  have w03 := swap_assoc (h.zc 0) (h.zc 3) h.s03
  have w12 := swap_assoc (h.zc 1) (h.zc 2) h.s12
  have w13 := swap_assoc (h.zc 1) (h.zc 3) h.s13
  have w23 := swap_assoc (h.zc 2) (h.zc 3) h.s23
  have zz : ∀ (a b : ℕ) (X : G), z ^ a * (z ^ b * X) = z ^ (a + b) * X := pow_pow_assoc z
  have qq : ∀ (i : Fin 4) (a b : ℕ) (X : G), q i ^ a * (q i ^ b * X) = q i ^ (a + b) * X :=
    fun i => pow_pow_assoc (q i)
  have zq := h.zq_assoc
  unfold nfQ mulQ
  simp only [mul_assoc, w01, w02, w03, w12, w13, w23, zz, qq, zq, ← pow_add]
  rw [pow_mod_seven (h.q7 0) (a.a0 + b.a0), pow_mod_seven (h.q7 1) (a.a1 + b.a1),
    pow_mod_seven (h.q7 2) (a.a2 + b.a2), pow_mod_seven (h.q7 3) (a.a3 + b.a3),
    pow_mod_seven h.z7]
  congr 6
  ring

theorem nfQ_zero : nfQ q z ⟨0, 0, 0, 0, 0⟩ = 1 := by simp [nfQ]

theorem nfQ_pow (h : QRel m q z) (r : QV) : ∀ k : ℕ, nfQ q z r ^ k = nfQ q z (powQ m r k)
  | 0 => by rw [pow_zero, powQ, nfQ_zero]
  | k + 1 => by rw [pow_succ, nfQ_pow h r k, powQ, nfQ_mul h]

theorem map_nfQ (h : QRel m q z) {f : G →* G} {A : QAct} (h0 : f (q 0) = nfQ q z A.r0)
    (h1 : f (q 1) = nfQ q z A.r1) (h2 : f (q 2) = nfQ q z A.r2) (h3 : f (q 3) = nfQ q z A.r3)
    (hz : f z = nfQ q z A.rz) (a : QV) : f (nfQ q z a) = nfQ q z (applyQ m A a) := by
  unfold applyQ
  rw [← nfQ_mul h, ← nfQ_mul h, ← nfQ_mul h, ← nfQ_mul h, ← nfQ_pow h, ← nfQ_pow h,
    ← nfQ_pow h, ← nfQ_pow h, ← nfQ_pow h, ← h0, ← h1, ← h2, ← h3, ← hz]
  unfold nfQ
  simp only [map_mul, map_pow]

theorem conj_nfQ (h : QRel m q z) {u : G} {A : QAct} (h0 : u * q 0 * u⁻¹ = nfQ q z A.r0)
    (h1 : u * q 1 * u⁻¹ = nfQ q z A.r1) (h2 : u * q 2 * u⁻¹ = nfQ q z A.r2)
    (h3 : u * q 3 * u⁻¹ = nfQ q z A.r3) (hz : u * z * u⁻¹ = nfQ q z A.rz) (a : QV) :
    u * nfQ q z a * u⁻¹ = nfQ q z (applyQ m A a) := by
  have e : ∀ y : G, u * y * u⁻¹ = MulAut.conj u y := fun y => by simp [MulAut.conj_apply]
  rw [e]
  exact map_nfQ (f := (MulAut.conj u).toMonoidHom) h (by rw [← h0, e]; rfl)
    (by rw [← h1, e]; rfl) (by rw [← h2, e]; rfl) (by rw [← h3, e]; rfl) (by rw [← hz, e]; rfl) a

end R

theorem decQ_red (n : ℕ) : redQ (decQ n) := by
  unfold decQ redQ
  refine ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
    Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num)⟩

theorem mulQ_red (m : CM) (a b : QV) : redQ (mulQ m a b) := by
  unfold mulQ redQ
  refine ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
    Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num)⟩

theorem evalQF_red (F : QF) (a : QV) : redQ (evalQF F a) := by
  unfold evalQF redQ
  refine ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
    Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num)⟩

@[expose] def zc (a : QV) : QV := ⟨a.a0, a.a1, a.a2, a.a3, 0⟩

@[expose] def encA (a : QV) : ℕ := 343 * a.a0 + 49 * a.a1 + 7 * a.a2 + a.a3

theorem decA_encA {a : QV} (h : redQ a) : decA (encA a) = zc a := by
  obtain ⟨h0, h1, h2, h3, -⟩ := h
  unfold decA encA zc
  congr 1 <;> omega

theorem encA_lt {a : QV} (h : redQ a) : encA a < 2401 := by
  obtain ⟨h0, h1, h2, h3, -⟩ := h
  unfold encA
  omega

section Phi

variable {m : CM} {q : Fin 4 → G} {z : G}

theorem nfQ_zc (a : QV) : nfQ q z a = nfQ q z (zc a) * z ^ a.c := by
  unfold nfQ zc
  simp only [pow_zero, mul_one]

theorem pow_shift (h7 : z ^ 7 = 1) (c P : ℕ) :
    z ^ ((c + P) % 7) = z ^ ((0 + P) % 7) * z ^ c := by
  rw [← pow_add, pow_mod_seven h7 ((0 + P) % 7 + c)]
  congr 1
  omega

theorem zc_evalQF (F : QF) (a : QV) : zc (evalQF F a) = zc (evalQF F (zc a)) := rfl

theorem nfQ_evalQF (h : QRel m q z) (F : QF) (a : QV) :
    nfQ q z (evalQF F a) = nfQ q z (evalQF F (zc a)) * z ^ a.c := by
  rw [nfQ_zc (evalQF F a), nfQ_zc (evalQF F (zc a)), zc_evalQF, mul_assoc]
  congr 1
  exact pow_shift h.z7 a.c (polyC F a)

theorem phiRow_of (hk : ∀ k < 7, phiOK (343 * k) 343 = true) {a : QV} (ha : redQ a) :
    phiRow (zc a) = true := by
  have hl := encA_lt ha
  have h := allBelow_spec (hk (encA a / 343) (by omega)) (encA a % 343) (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod, decA_encA ha] at h

end Phi

structure PcHyp (u : G) (q : Fin 4 → G) (z : G) : Prop where
  rel : QRel cmSeven q z
  u7 : u ^ 7 = 1
  c0 : u * q 0 * u⁻¹ = nfQ q z uAct.r0
  c1 : u * q 1 * u⁻¹ = nfQ q z uAct.r1
  c2 : u * q 2 * u⁻¹ = nfQ q z uAct.r2
  c3 : u * q 3 * u⁻¹ = nfQ q z uAct.r3
  cz : u * z * u⁻¹ = z

variable {u : G} {q : Fin 4 → G} {z : G}

theorem PcHyp.conjU_pow (H : PcHyp u q z) (C : ∀ k < 7, phiOK (343 * k) 343 = true) {k : ℕ}
    (hk : k < 7) {a : QV} (ha : redQ a) : (u ^ k)⁻¹ * nfQ q z a * u ^ k = nfQ q z (phiAt k a) := by
  have hzn : nfQ q z uAct.rz = z := by simp [nfQ, uAct]
  have hxi : u⁻¹ * z * u = z := by
    calc u⁻¹ * z * u = u⁻¹ * (u * z * u⁻¹) * u := by rw [H.cz]
      _ = z := by group
  have hxc : ∀ c : ℕ, u⁻¹ * z ^ c * u = z ^ c := fun c => by
    rw [← conjInv_apply, map_pow, conjInv_apply, hxi]
  have rows : ∀ {a : QV}, redQ a →
      (applyQ cmSeven uAct (evalQF phi1 (zc a))).beq (zc a) = true ∧
      (evalQF phi2 (zc a)).beq (evalQF phi1 (evalQF phi1 (zc a))) = true ∧
      (evalQF phi3 (zc a)).beq (evalQF phi2 (evalQF phi1 (zc a))) = true ∧
      (evalQF phi4 (zc a)).beq (evalQF phi3 (evalQF phi1 (zc a))) = true ∧
      (evalQF phi5 (zc a)).beq (evalQF phi4 (evalQF phi1 (zc a))) = true ∧
      (evalQF phi6 (zc a)).beq (evalQF phi5 (evalQF phi1 (zc a))) = true := fun ha => by
    have := phiRow_of C ha
    unfold phiRow at this
    simp only [Bool.and_eq_true] at this
    exact ⟨this.1.1.1.1.1, this.1.1.1.1.2, this.1.1.1.2, this.1.1.2, this.1.2, this.2⟩
  have g1 : ∀ a : QV, redQ a → u⁻¹ * nfQ q z a * u = nfQ q z (evalQF phi1 a) := fun a ha => by
    have e := conj_nfQ H.rel H.c0 H.c1 H.c2 H.c3 (by rw [hzn]; exact H.cz) (evalQF phi1 (zc a))
    rw [CFSG.KC.BM.PcFive.QV.beq_eq (rows ha).1] at e
    have e2 : u⁻¹ * nfQ q z (zc a) * u = nfQ q z (evalQF phi1 (zc a)) := by
      rw [← e]
      group
    rw [nfQ_zc a, nfQ_evalQF H.rel, ← e2]
    conv_rhs => rw [← hxc a.c]
    group
  have comp : ∀ Fk Fk1 : QF,
      (∀ a : QV, redQ a → (evalQF Fk1 (zc a)).beq (evalQF Fk (evalQF phi1 (zc a))) = true) →
      ∀ a : QV, redQ a → nfQ q z (evalQF Fk (evalQF phi1 a)) = nfQ q z (evalQF Fk1 a) := by
    intro Fk Fk1 hr a ha
    rw [nfQ_evalQF H.rel Fk1 a, CFSG.KC.BM.PcFive.QV.beq_eq (hr a ha),
      nfQ_evalQF H.rel Fk (evalQF phi1 a), nfQ_evalQF H.rel Fk (evalQF phi1 (zc a)),
      zc_evalQF phi1 a, mul_assoc]
    congr 1
    exact pow_shift H.rel.z7 a.c (polyC phi1 a)
  have step : ∀ (k : ℕ) (Fk Fk1 : QF),
      (∀ a : QV, redQ a → (u ^ k)⁻¹ * nfQ q z a * u ^ k = nfQ q z (evalQF Fk a)) →
      (∀ a : QV, redQ a → (evalQF Fk1 (zc a)).beq (evalQF Fk (evalQF phi1 (zc a))) = true) →
      ∀ a : QV, redQ a → (u ^ (k + 1))⁻¹ * nfQ q z a * u ^ (k + 1) = nfQ q z (evalQF Fk1 a) := by
    intro k Fk Fk1 hk hr a ha
    rw [conj_pow_succ, g1 a ha, hk _ (evalQF_red _ _), comp Fk Fk1 hr a ha]
  have g1' : ∀ a : QV, redQ a → (u ^ 1)⁻¹ * nfQ q z a * u ^ 1 = nfQ q z (evalQF phi1 a) :=
    fun a ha => by rw [pow_one]; exact g1 a ha
  have g2 := step 1 phi1 phi2 g1' (fun a ha => (rows ha).2.1)
  have g3 := step 2 phi2 phi3 g2 (fun a ha => (rows ha).2.2.1)
  have g4 := step 3 phi3 phi4 g3 (fun a ha => (rows ha).2.2.2.1)
  have g5 := step 4 phi4 phi5 g4 (fun a ha => (rows ha).2.2.2.2.1)
  have g6 := step 5 phi5 phi6 g5 (fun a ha => (rows ha).2.2.2.2.2)
  interval_cases k
  · simp [phiAt]
  · exact g1' a ha
  · exact g2 a ha
  · exact g3 a ha
  · exact g4 a ha
  · exact g5 a ha
  · exact g6 a ha

theorem mulV_red (v w : V6) : redV (mulV v w) := ⟨Nat.mod_lt _ (by norm_num), mulQ_red _ _ _⟩

theorem one_red : redV ⟨0, ⟨0, 0, 0, 0, 0⟩⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

theorem powV_red (v : V6) : ∀ k, redV (powV v k)
  | 0 => one_red
  | _ + 1 => mulV_red _ _

theorem dec_red (i : ℕ) : redV (dec i) := ⟨Nat.mod_lt _ (by norm_num), decQ_red _⟩

@[expose] def encQ (a : QV) : ℕ := 2401 * a.a0 + 343 * a.a1 + 49 * a.a2 + 7 * a.a3 + a.c

@[expose] def enc (v : V6) : ℕ := 16807 * v.e + encQ v.q

theorem decQ_encQ {a : QV} (h : redQ a) : decQ (encQ a) = a := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  unfold decQ encQ
  cases a
  simp only at h0 h1 h2 h3 h4 ⊢
  congr 1 <;> omega

theorem encQ_lt {a : QV} (h : redQ a) : encQ a < 16807 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  unfold encQ
  omega

theorem dec_enc {v : V6} (h : redV v) : dec (enc v) = v := by
  have hq := encQ_lt h.2
  have he := h.1
  unfold dec enc
  have e1 : (16807 * v.e + encQ v.q) / 16807 % 7 = v.e := by omega
  have e2 : (16807 * v.e + encQ v.q) % 16807 = encQ v.q := by omega
  rw [e1, e2, decQ_encQ h.2]

theorem enc_lt {v : V6} (h : redV v) : enc v < 117649 := by
  have hq := encQ_lt h.2
  have he := h.1
  unfold enc
  omega

theorem psi_zero : psi u q z ⟨0, ⟨0, 0, 0, 0, 0⟩⟩ = 1 := by
  simp [psi, nfQ]

theorem PcHyp.psi_mul (H : PcHyp u q z) (C : ∀ k < 7, phiOK (343 * k) 343 = true) {v w : V6}
    (hv : redV v) (hw : redV w) : psi u q z v * psi u q z w = psi u q z (mulV v w) := by
  unfold psi mulV
  simp only
  rw [← nfQ_mul H.rel, ← H.conjU_pow C hw.1 hv.2, ← pow_mod_seven H.u7, pow_add]
  simp only [mul_assoc, mul_inv_cancel_left]

theorem PcHyp.psi_pow (H : PcHyp u q z) (C : ∀ k < 7, phiOK (343 * k) 343 = true) {v : V6}
    (hv : redV v) : ∀ k, psi u q z v ^ k = psi u q z (powV v k)
  | 0 => by rw [pow_zero, powV, psi_zero]
  | k + 1 => by rw [pow_succ, H.psi_pow C hv k, powV, H.psi_mul C (powV_red _ _) hv]

theorem PcHyp.conj_alpha (H : PcHyp u q z) (C : ∀ k < 7, phiOK (343 * k) 343 = true) {g : G}
    {ws : List ℕ} (hu : g * u * g⁻¹ = psi u q z (dec (nth ws 0)))
    (h0 : g * q 0 * g⁻¹ = psi u q z (dec (nth ws 1)))
    (h1 : g * q 1 * g⁻¹ = psi u q z (dec (nth ws 2)))
    (h2 : g * q 2 * g⁻¹ = psi u q z (dec (nth ws 3)))
    (h3 : g * q 3 * g⁻¹ = psi u q z (dec (nth ws 4)))
    (hz : g * z * g⁻¹ = psi u q z (dec (nth ws 5))) (v : V6) :
    g * psi u q z v * g⁻¹ = psi u q z (alphaV ws v) := by
  unfold alphaV
  rw [← H.psi_mul C (mulV_red _ _) (powV_red _ _), ← H.psi_mul C (mulV_red _ _) (powV_red _ _),
    ← H.psi_mul C (mulV_red _ _) (powV_red _ _), ← H.psi_mul C (mulV_red _ _) (powV_red _ _),
    ← H.psi_mul C (powV_red _ _) (powV_red _ _), ← H.psi_pow C (dec_red _),
    ← H.psi_pow C (dec_red _), ← H.psi_pow C (dec_red _), ← H.psi_pow C (dec_red _),
    ← H.psi_pow C (dec_red _), ← H.psi_pow C (dec_red _), ← hu, ← h0, ← h1, ← h2, ← h3, ← hz,
    ← MulAut.conj_apply]
  unfold psi nfQ
  simp only [map_mul, map_pow, MulAut.conj_apply, mul_assoc]

end CFSG.KC.MonPcSeven

end
