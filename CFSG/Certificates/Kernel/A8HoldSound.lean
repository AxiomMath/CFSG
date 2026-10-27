module

public import Certificates.Data.Kernel.A8Hold
public import CFSG.RankThree.PartTwo.Sec21.Holder214ThetaA8Data
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
public import Mathlib.GroupTheory.Perm.Sign

public section

namespace CFSG.KC.A8Hold

open CFSG.RankThree.PartTwo.Sec21.Holder214Theta Equiv

@[expose] def codeP (p : Perm (Fin 8)) : ℕ :=
  pk (p 0).val (p 1).val (p 2).val (p 3).val (p 4).val (p 5).val (p 6).val (p 7).val

theorem gN_pk {v0 v1 v2 v3 v4 v5 v6 v7 : ℕ} (h0 : v0 < 8) (h1 : v1 < 8) (h2 : v2 < 8)
    (h3 : v3 < 8) (h4 : v4 < 8) (h5 : v5 < 8) (h6 : v6 < 8) (h7 : v7 < 8) :
    gN (pk v0 v1 v2 v3 v4 v5 v6 v7) 0 = v0 ∧ gN (pk v0 v1 v2 v3 v4 v5 v6 v7) 1 = v1 ∧
      gN (pk v0 v1 v2 v3 v4 v5 v6 v7) 2 = v2 ∧ gN (pk v0 v1 v2 v3 v4 v5 v6 v7) 3 = v3 ∧
      gN (pk v0 v1 v2 v3 v4 v5 v6 v7) 4 = v4 ∧ gN (pk v0 v1 v2 v3 v4 v5 v6 v7) 5 = v5 ∧
      gN (pk v0 v1 v2 v3 v4 v5 v6 v7) 6 = v6 ∧ gN (pk v0 v1 v2 v3 v4 v5 v6 v7) 7 = v7 := by
  simp only [gN, pk, Nat.reducePow]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem gN_codeP (p : Perm (Fin 8)) (x : Fin 8) : gN (codeP p) x.val = (p x).val := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := gN_pk (p 0).isLt (p 1).isLt (p 2).isLt (p 3).isLt
    (p 4).isLt (p 5).isLt (p 6).isLt (p 7).isLt
  fin_cases x
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7

theorem gN_codeP' (p : Perm (Fin 8)) (i : ℕ) (hi : i < 8) : gN (codeP p) i = (p ⟨i, hi⟩).val :=
  gN_codeP p ⟨i, hi⟩

theorem codeP_inj {p q : Perm (Fin 8)} (h : codeP p = codeP q) : p = q :=
  Equiv.ext fun x => Fin.ext (by rw [← gN_codeP, h, gN_codeP])

theorem codeP_one : codeP 1 = idN := rfl

theorem codeP_mul (p q : Perm (Fin 8)) : codeP (p * q) = compN (codeP p) (codeP q) := by
  have e : ∀ i (hi : i < 8), gN (codeP p) (gN (codeP q) i) = ((p * q) ⟨i, hi⟩).val := by
    intro i hi
    rw [gN_codeP' q i hi, gN_codeP' p _ (q _).isLt, Perm.mul_apply]
  rw [compN, e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide),
    e 5 (by decide), e 6 (by decide), e 7 (by decide)]
  rfl

theorem codeP_pow (p : Perm (Fin 8)) (k : ℕ) : codeP (p ^ (2 ^ k)) = powN k (codeP p) := by
  induction k with
  | zero => rw [pow_zero, pow_one]; rfl
  | succ k ih =>
    rw [pow_succ, pow_mul, sq, codeP_mul, ih]
    rfl

theorem findN_codeP (p : Perm (Fin 8)) (y : Fin 8) : findN (codeP p) y.val = (p⁻¹ y).val := by
  have hi : ∀ i (hi : i < 8), (gN (codeP p) i = y.val ↔ i = (p⁻¹ y).val) := by
    intro i hi
    rw [gN_codeP' p i hi]
    constructor
    · intro h
      have hy : p ⟨i, hi⟩ = y := Fin.ext h
      rw [← hy]
      simp
    · intro h
      have hx : (⟨i, hi⟩ : Fin 8) = p⁻¹ y := Fin.ext h
      rw [hx]
      simp
  have h0 := hi 0 (by decide)
  have h1 := hi 1 (by decide)
  have h2 := hi 2 (by decide)
  have h3 := hi 3 (by decide)
  have h4 := hi 4 (by decide)
  have h5 := hi 5 (by decide)
  have h6 := hi 6 (by decide)
  have hx := (p⁻¹ y).isLt
  unfold findN
  generalize (p⁻¹ y).val = x0 at *
  interval_cases x0 <;> simp_all

theorem codeP_inv (p : Perm (Fin 8)) : codeP p⁻¹ = invN (codeP p) := by
  have e : ∀ i (hi : i < 8), findN (codeP p) i = (p⁻¹ ⟨i, hi⟩).val :=
    fun i hi => findN_codeP p ⟨i, hi⟩
  rw [invN, e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide),
    e 5 (by decide), e 6 (by decide), e 7 (by decide)]
  rfl

theorem codeP_c1 : codeP a8C1 = c1N := by decide

theorem codeP_c2 : codeP a8C2 = c2N := by decide

theorem codeP_tau : codeP a8Tau = tauN := by decide

theorem a8Chk1_sound (h : a8Chk1 = true) {a b c d : ℕ} (ha : a < 8) (hb : b < 8) (hc : c < 8)
    (hd : d < 8) : leaf1 (tab1 a b c d) = true := by
  unfold a8Chk1 at h
  simp only [List.all_eq_true, List.mem_range] at h
  exact h a ha b hb c hc d hd

theorem comm_apply {π g : Perm (Fin 8)} (h : π * g = g * π) (x : Fin 8) : π (g x) = g (π x) := by
  rw [← Perm.mul_apply, h, Perm.mul_apply]

theorem a8_invol_of (hk : a8Chk1 = true) :
    ∀ π : Perm (Fin 8), π * a8C1 = a8C1 * π → π * a8C2 = a8C2 * π → π ^ 2 = 1 →
      π = 1 ∨ π = a8Tau := by
  intro π h1 h2 hsq
  have v1 : ∀ x : Fin 8, (a8C1 x).val = gN c1N x.val := fun x => by rw [← codeP_c1, gN_codeP]
  have v2 : ∀ x : Fin 8, (a8C2 x).val = gN c2N x.val := fun x => by rw [← codeP_c2, gN_codeP]
  have a10 : a8C1 0 = 1 := by decide +kernel
  have a11 : a8C1 1 = 2 := by decide +kernel
  have a23 : a8C2 3 = 4 := by decide +kernel
  have a24 : a8C2 4 = 5 := by decide +kernel
  have e1 : (π 1).val = gN c1N (π 0).val := by rw [← v1, ← comm_apply h1, a10]
  have e2 : (π 2).val = gN c1N (gN c1N (π 0).val) := by
    rw [← e1, ← v1, ← comm_apply h1, a11]
  have e4 : (π 4).val = gN c2N (π 3).val := by rw [← v2, ← comm_apply h2, a23]
  have e5 : (π 5).val = gN c2N (gN c2N (π 3).val) := by
    rw [← e4, ← v2, ← comm_apply h2, a24]
  have hcode : codeP π = tab1 (π 0).val (π 3).val (π 6).val (π 7).val := by
    unfold codeP tab1
    rw [e1, e2, e4, e5]
  have hsq' : compN (codeP π) (codeP π) = idN := by rw [← codeP_mul, ← sq, hsq, codeP_one]
  have hl := a8Chk1_sound hk (π 0).isLt (π 3).isLt (π 6).isLt (π 7).isLt
  rw [← hcode] at hl
  unfold leaf1 at hl
  rw [hsq', Nat.beq_refl] at hl
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, Nat.beq_eq] at hl
  rcases hl with hl | hl
  · left
    exact codeP_inj (hl.trans codeP_one.symm)
  · right
    exact codeP_inj (hl.trans codeP_tau.symm)

theorem a8Chk2_sound (h : a8Chk2 = true) {a0 a1 a2 a3 a4 a5 e : ℕ} (h0 : a0 < 6) (h1 : a1 < 6)
    (h2 : a2 < 6) (h3 : a3 < 6) (h4 : a4 < 6) (h5 : a5 < 6) (he : e < 2) (d10 : a1 ≠ a0)
    (d20 : a2 ≠ a0) (d21 : a2 ≠ a1) (d30 : a3 ≠ a0) (d31 : a3 ≠ a1) (d32 : a3 ≠ a2)
    (d40 : a4 ≠ a0) (d41 : a4 ≠ a1) (d42 : a4 ≠ a2) (d43 : a4 ≠ a3) (d50 : a5 ≠ a0)
    (d51 : a5 ≠ a1) (d52 : a5 ≠ a2) (d53 : a5 ≠ a3) (d54 : a5 ≠ a4) :
    leaf2 (pk a0 a1 a2 a3 a4 a5 (6 + e) (7 - e)) = true := by
  unfold a8Chk2 at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Nat.beq_eq] at h
  have g1 := (h a0 h0 a1 h1).resolve_left d10
  have g2 := (g1 a2 h2).resolve_left (by omega)
  have g3 := (g2 a3 h3).resolve_left (by omega)
  have g4 := (g3 a4 h4).resolve_left (by omega)
  have g5 := (g4 a5 h5).resolve_left (by omega)
  exact g5 e he

theorem codeP_pow128 (p : Perm (Fin 8)) : powN 7 (codeP p) = codeP (p ^ 128) := by
  rw [← codeP_pow]
  rfl

theorem tau_fix : ∀ y : Fin 8, a8Tau y = y ↔ y.val < 6 := by decide +kernel

theorem tau_six : a8Tau 6 = 7 := by decide +kernel

theorem tau_val_six : gN tauN 6 = 7 := by decide +kernel

theorem tau_val_seven : gN tauN 7 = 6 := by decide +kernel

theorem a8_two_of (hk : a8Chk2 = true) :
    ∀ p : Perm (Fin 8), Perm.sign p = 1 → p * a8Tau = a8Tau * p → p ≠ 1 →
      p ^ 128 = 1 → (p * a8C2 * p⁻¹ * a8C2⁻¹) ^ 128 ≠ 1 ∨
        (p * (a8C1 * a8C2) * p⁻¹ * (a8C1 * a8C2)⁻¹) ^ 128 ≠ 1 := by
  intro p hs ht hp1 h128
  have hfix := tau_fix
  have vt : ∀ y : Fin 8, (a8Tau y).val = gN tauN y.val := fun y => by rw [← codeP_tau, gN_codeP]
  have hlow : ∀ x : Fin 8, x.val < 6 → (p x).val < 6 := fun x hx => by
    rw [← hfix] at hx ⊢
    rw [← comm_apply ht, hx]
  have h67 : (p 7) = a8Tau (p 6) := by rw [← tau_six, comm_apply ht]
  have h6 : 6 ≤ (p 6).val := by
    by_contra hlt
    have hf : a8Tau (p 6) = p 6 := (hfix _).mpr (by omega)
    rw [hf] at h67
    exact absurd (p.injective h67) (by decide)
  have h7 : (p 7).val + (p 6).val = 13 := by
    have hl := (p 6).isLt
    rw [h67, vt]
    generalize (p 6).val = v at *
    interval_cases v
    · rw [tau_val_six]
    · rw [tau_val_seven]
  have l0 := hlow 0 (by decide)
  have l1 := hlow 1 (by decide)
  have l2 := hlow 2 (by decide)
  have l3 := hlow 3 (by decide)
  have l4 := hlow 4 (by decide)
  have l5 := hlow 5 (by decide)
  have hd : ∀ i j : Fin 8, i ≠ j → (p i).val ≠ (p j).val := fun i j hij hv =>
    hij (p.injective (Fin.ext hv))
  have hl6 := (p 6).isLt
  have hl := a8Chk2_sound hk l0 l1 l2 l3 l4 l5 (e := (p 6).val - 6) (by omega)
    (hd 1 0 (by decide)) (hd 2 0 (by decide)) (hd 2 1 (by decide)) (hd 3 0 (by decide))
    (hd 3 1 (by decide)) (hd 3 2 (by decide)) (hd 4 0 (by decide)) (hd 4 1 (by decide))
    (hd 4 2 (by decide)) (hd 4 3 (by decide)) (hd 5 0 (by decide)) (hd 5 1 (by decide))
    (hd 5 2 (by decide)) (hd 5 3 (by decide)) (hd 5 4 (by decide))
  have hcode : pk (p 0).val (p 1).val (p 2).val (p 3).val (p 4).val (p 5).val
      (6 + ((p 6).val - 6)) (7 - ((p 6).val - 6)) = codeP p := by
    have e6 : 6 + ((p 6).val - 6) = (p 6).val := by omega
    have e7 : 7 - ((p 6).val - 6) = (p 7).val := by omega
    rw [e6, e7]
    rfl
  rw [hcode] at hl
  have hA : powN 7 (codeP p) = idN := by rw [codeP_pow128, h128, codeP_one]
  have hP1 : Nat.beq (codeP p) idN = false := by
    rw [Bool.eq_false_iff]
    intro hb
    exact hp1 (codeP_inj ((Nat.eq_of_beq_eq_true hb).trans codeP_one.symm))
  have hPt : Nat.beq (codeP p) tauN = false := by
    rw [Bool.eq_false_iff]
    intro hb
    have hpt : p = a8Tau := codeP_inj ((Nat.eq_of_beq_eq_true hb).trans codeP_tau.symm)
    rw [hpt, a8Tau, Perm.sign_swap (by decide)] at hs
    exact absurd hs (by decide)
  have hK1 : commN (codeP p) c2N = codeP (p * a8C2 * p⁻¹ * a8C2⁻¹) := by
    rw [codeP_mul, codeP_mul, codeP_mul, codeP_inv, codeP_inv, codeP_c2]
    rfl
  have hK2 : commN (codeP p) (compN c1N c2N) =
      codeP (p * (a8C1 * a8C2) * p⁻¹ * (a8C1 * a8C2)⁻¹) := by
    rw [codeP_mul, codeP_mul, codeP_mul, codeP_inv, codeP_inv, codeP_mul, codeP_c1, codeP_c2]
    rfl
  unfold leaf2 at hl
  rw [hA, Nat.beq_refl, hP1, hPt, hK1, hK2, codeP_pow128, codeP_pow128] at hl
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.not_eq_true'] at hl
  rcases hl with hl | hl
  · left
    intro h1
    rw [h1, codeP_one, Nat.beq_refl] at hl
    exact absurd hl (by decide)
  · right
    intro h1
    rw [h1, codeP_one, Nat.beq_refl] at hl
    exact absurd hl (by decide)

end CFSG.KC.A8Hold
