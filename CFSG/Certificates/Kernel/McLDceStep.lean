module

import CFSG.Certificates.Kernel.Co1DceLemmas
import Mathlib.Tactic.Group
public import CFSG.Certificates.Kernel.McLDcePsi

public section

namespace CFSG.Certificates.McLD

open CFSG.KC CFSG.KC.McL.Mat

set_option exponentiation.threshold 700

@[expose] noncomputable def gL (HB GB : ℕ → ℕ) (j : ℕ) : ℕ :=
  McL.Dce.mat HB (McL.Dce.lo20 (McL.Dce.e40 GB j))

@[expose] noncomputable def gH (HB GB : ℕ → ℕ) (j : ℕ) : ℕ :=
  McL.Dce.mat HB (McL.Dce.hi20 (McL.Dce.e40 GB j))

theorem stepT_eq (HB GB TB : ℕ → ℕ) (nT R dir e S : ℕ) :
    McL.Dce.stepT HB GB TB nT R dir e S =
      Bool.rec (motive := fun _ => ℕ) McL.Dce.bad
        (Bool.rec (motive := fun _ => ℕ)
          (Bool.rec (motive := fun _ => ℕ) McL.Dce.bad
            (McL.Dce.mkSt (McL.Dce.rDp R)
              (mul25 (mul25 (McL.Dce.rPi R) (gH HB GB (McL.Dce.rJ R - 1))) (tPsi HB TB e)))
            (Th.andB (Nat.beq (McL.Dce.sD S) (McL.Dce.rD R))
              (Nat.beq (McL.Dce.tSig HB TB e) (mul25 (gL HB GB (McL.Dce.rJ R - 1)) (McL.Dce.sPi S)))))
          (Bool.rec (motive := fun _ => ℕ) McL.Dce.bad
            (McL.Dce.mkSt (McL.Dce.rD R) (mul25 (gH HB GB (McL.Dce.rJ R - 1)) (McL.Dce.tSig HB TB e)))
            (Th.andB (Nat.beq (McL.Dce.sD S) (McL.Dce.rDp R))
              (Nat.beq (tPsi HB TB e)
                (mul25 (mul25 (gL HB GB (McL.Dce.rJ R - 1)) (McL.Dce.rFI R)) (McL.Dce.sPi S)))))
          (Nat.beq dir 1))
        (Th.andB (Nat.blt 0 (McL.Dce.rJ R)) (Nat.blt e nT)) := rfl

@[expose] def LStep (HB GB TB : ℕ → ℕ) (TL nT c R dir e S S' : ℕ) : Prop :=
  (c = TL ∧ 0 < McL.Dce.rJ R ∧ e < nT ∧
    ((Nat.beq dir 1 = false ∧ McL.Dce.sD S = McL.Dce.rD R ∧
        McL.Dce.tSig HB TB e = mul25 (gL HB GB (McL.Dce.rJ R - 1)) (McL.Dce.sPi S) ∧
        S' = McL.Dce.mkSt (McL.Dce.rDp R)
          (mul25 (mul25 (McL.Dce.rPi R) (gH HB GB (McL.Dce.rJ R - 1))) (tPsi HB TB e))) ∨
      (Nat.beq dir 1 = true ∧ McL.Dce.sD S = McL.Dce.rDp R ∧
        tPsi HB TB e = mul25 (mul25 (gL HB GB (McL.Dce.rJ R - 1)) (McL.Dce.rFI R)) (McL.Dce.sPi S) ∧
        S' = McL.Dce.mkSt (McL.Dce.rD R) (mul25 (gH HB GB (McL.Dce.rJ R - 1)) (McL.Dce.tSig HB TB e))))) ∨
  (c = 255 ∧ McL.Dce.rJ R = 0 ∧
    ((Nat.beq dir 1 = false ∧ McL.Dce.sD S = McL.Dce.rD R ∧
        S' = McL.Dce.mkSt (McL.Dce.rDp R) (mul25 (McL.Dce.rPi R) (McL.Dce.sPi S))) ∨
      (Nat.beq dir 1 = true ∧ McL.Dce.sD S = McL.Dce.rDp R ∧
        S' = McL.Dce.mkSt (McL.Dce.rD R) (mul25 (McL.Dce.rFI R) (McL.Dce.sPi S)))))

theorem brfN (a b : ℕ) : Bool.rec (motive := fun _ => ℕ) a b false = a := rfl

theorem brtN (a b : ℕ) : Bool.rec (motive := fun _ => ℕ) a b true = b := rfl

theorem stepL_cases {HB GB TB : ℕ → ℕ} {TL nT c R dir e S : ℕ} :
    McL.Dce.stepL HB GB TB TL nT c R dir e S = McL.Dce.bad ∨
      LStep HB GB TB TL nT c R dir e S (McL.Dce.stepL HB GB TB TL nT c R dir e S) := by
  generalize hS' : McL.Dce.stepL HB GB TB TL nT c R dir e S = S'
  unfold McL.Dce.stepL at hS'
  cases h255 : Nat.beq c 255
  · simp only [h255] at hS'
    cases hT : Nat.beq c TL
    · simp only [hT] at hS'
      exact Or.inl hS'.symm
    simp only [hT] at hS'
    rw [stepT_eq] at hS'
    cases h1 : Th.andB (Nat.blt 0 (McL.Dce.rJ R)) (Nat.blt e nT)
    · simp only [h1] at hS'
      exact Or.inl hS'.symm
    simp only [h1] at hS'
    rw [andB_iff, Nat.blt_eq, Nat.blt_eq] at h1
    have hcT := Nat.eq_of_beq_eq_true hT
    cases hd : Nat.beq dir 1
    · simp only [hd] at hS'
      cases h2 : Th.andB (Nat.beq (McL.Dce.sD S) (McL.Dce.rD R))
          (Nat.beq (McL.Dce.tSig HB TB e) (mul25 (gL HB GB (McL.Dce.rJ R - 1)) (McL.Dce.sPi S)))
      · simp only [h2] at hS'
        exact Or.inl hS'.symm
      · simp only [h2] at hS'
        rw [andB_iff, Nat.beq_eq, Nat.beq_eq] at h2
        exact Or.inr (Or.inl ⟨hcT, h1.1, h1.2, Or.inl ⟨hd, h2.1, h2.2, hS'.symm⟩⟩)
    · simp only [hd] at hS'
      cases h2 : Th.andB (Nat.beq (McL.Dce.sD S) (McL.Dce.rDp R))
          (Nat.beq (tPsi HB TB e)
            (mul25 (mul25 (gL HB GB (McL.Dce.rJ R - 1)) (McL.Dce.rFI R)) (McL.Dce.sPi S)))
      · simp only [h2] at hS'
        exact Or.inl hS'.symm
      · simp only [h2] at hS'
        rw [andB_iff, Nat.beq_eq, Nat.beq_eq] at h2
        exact Or.inr (Or.inl ⟨hcT, h1.1, h1.2, Or.inr ⟨hd, h2.1, h2.2, hS'.symm⟩⟩)
  · simp only [h255] at hS'
    unfold McL.Dce.stepE at hS'
    have hc := Nat.eq_of_beq_eq_true h255
    cases h1 : Nat.beq (McL.Dce.rJ R) 0
    · simp only [h1] at hS'
      exact Or.inl hS'.symm
    simp only [h1] at hS'
    have hJ := Nat.eq_of_beq_eq_true h1
    cases hd : Nat.beq dir 1
    · simp only [hd] at hS'
      cases h2 : Nat.beq (McL.Dce.sD S) (McL.Dce.rD R)
      · simp only [h2] at hS'
        exact Or.inl hS'.symm
      · simp only [h2] at hS'
        exact Or.inr (Or.inr ⟨hc, hJ, Or.inl ⟨hd, Nat.eq_of_beq_eq_true h2, hS'.symm⟩⟩)
    · simp only [hd] at hS'
      cases h2 : Nat.beq (McL.Dce.sD S) (McL.Dce.rDp R)
      · simp only [h2] at hS'
        exact Or.inl hS'.symm
      · simp only [h2] at hS'
        exact Or.inr (Or.inr ⟨hc, hJ, Or.inr ⟨hd, Nat.eq_of_beq_eq_true h2, hS'.symm⟩⟩)

theorem mul25_zero_r (B : ℕ) : mul25 B 0 = 0 :=
  eq_of_toMat_eq (mul25_lt _ _) (Nat.two_pow_pos _) (by rw [toMat_mul25, toMat_zero, mul_zero])

variable {LT TL NL : ℕ}

theorem inM_ne_zero {A : ℕ} (h : InM LT TL NL A) : A ≠ 0 := by
  rintro rfl
  obtain ⟨y, -, hy⟩ := h
  have e := y.mul_inv
  rw [hy, toMat_zero, zero_mul] at e
  apply ident_ne_zero
  exact eq_of_toMat_eq ident_lt (Nat.two_pow_pos _) (by rw [toMat_ident, toMat_zero, e])

theorem InM_cancel_left {A B : ℕ} (hA : InM LT TL NL A) (h : InM LT TL NL (mul25 A B)) :
    InM LT TL NL B := by
  obtain ⟨y, hy, ey⟩ := hA
  obtain ⟨z, hz, ez⟩ := h
  refine ⟨y⁻¹ * z, (Mg LT TL NL).mul_mem ((Mg LT TL NL).inv_mem hy) hz, ?_⟩
  rw [Units.val_mul, ez, toMat_mul25, ← ey, ← mul_assoc, Units.inv_mul, one_mul]

theorem InM_cancel_right {A B : ℕ} (hB : InM LT TL NL B) (h : InM LT TL NL (mul25 A B)) :
    InM LT TL NL A := by
  obtain ⟨y, hy, ey⟩ := hB
  obtain ⟨z, hz, ez⟩ := h
  refine ⟨z * y⁻¹, (Mg LT TL NL).mul_mem hz ((Mg LT TL NL).inv_mem hy), ?_⟩
  rw [Units.val_mul, ez, toMat_mul25, ← ey, mul_assoc, Units.mul_inv, mul_one]

theorem mkSt_lt {D p : ℕ} (hD : D < 256) (hp : p < 2 ^ 625) : McL.Dce.mkSt D p < 2 ^ 640 := by
  have e : McL.Dce.mkSt D p = D + p * 2 ^ 8 := Co1D.lor_shl (k := 8) hD
  rw [e]
  calc D + p * 2 ^ 8 < 2 ^ 8 + p * 2 ^ 8 := by omega
    _ = (p + 1) * 2 ^ 8 := by ring
    _ ≤ 2 ^ 625 * 2 ^ 8 := Nat.mul_le_mul_right _ hp
    _ < 2 ^ 640 := by norm_num

theorem rD_lt (R : ℕ) : McL.Dce.rD R < 256 := land255_lt _

theorem rDp_lt (R : ℕ) : McL.Dce.rDp R < 256 := land255_lt _

theorem sPi_mkD (R p : ℕ) : McL.Dce.sPi (McL.Dce.mkSt (McL.Dce.rD R) p) = p :=
  sPi_mkSt (rD_lt R) p

theorem sPi_mkDp (R p : ℕ) : McL.Dce.sPi (McL.Dce.mkSt (McL.Dce.rDp R) p) = p :=
  sPi_mkSt (rDp_lt R) p

theorem sD_mkD (R p : ℕ) : McL.Dce.sD (McL.Dce.mkSt (McL.Dce.rD R) p) = McL.Dce.rD R :=
  sD_mkSt (rD_lt R) p

theorem sD_mkDp (R p : ℕ) : McL.Dce.sD (McL.Dce.mkSt (McL.Dce.rDp R) p) = McL.Dce.rDp R :=
  sD_mkSt (rDp_lt R) p

theorem LStep_lt {HB GB TB : ℕ → ℕ} {TL nT c R dir e S S' : ℕ}
    (h : LStep HB GB TB TL nT c R dir e S S') : S' < 2 ^ 640 := by
  rcases h with ⟨-, -, -, ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩⟩ | ⟨-, -, ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩⟩ <;>
    exact mkSt_lt (land255_lt _) (mul25_lt _ _)

section Mean

variable {G : Type*} [Group G] (φ : Mg LT TL NL →* G) (gen : ℕ → G) (HB GB TB : ℕ → ℕ)

@[expose] noncomputable def tvJ (J : ℕ) : G :=
  if J = 0 then 1 else (rc φ (gL HB GB (J - 1)))⁻¹ * gen TL * rc φ (gL HB GB (J - 1))

@[expose] def FM (w : ℕ → G) (R : ℕ) : Prop :=
  w (McL.Dce.rD R) * tvJ φ gen HB GB (McL.Dce.rJ R) =
    rc φ (McL.Dce.rN R) * w (McL.Dce.rDp R) * rc φ (McL.Dce.rPi R)

@[expose] noncomputable def mR (R dir : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (McL.Dce.rN R) (McL.Dce.rNI R) (Nat.beq dir 1)

@[expose] noncomputable def lv (c : ℕ) : G := if c = 255 then 1 else gen c

@[expose] def SR (w : ℕ → G) (S : ℕ) (ℓ : G) (m S' : ℕ) : Prop :=
  w (McL.Dce.sD S) * rc φ (McL.Dce.sPi S) * ℓ =
    rc φ m * w (McL.Dce.sD S') * rc φ (McL.Dce.sPi S')

variable {φ gen HB GB TB} {NO nT : ℕ}
  (hG : ∀ j < NO, InM LT TL NL (gL HB GB j) ∧ InM LT TL NL (gH HB GB j) ∧
    mul25 (gL HB GB j) (gH HB GB j) = ident)
  (hS : ∀ e < nT, InM LT TL NL (McL.Dce.tSig HB TB e) ∧ InM LT TL NL (tPsi HB TB e) ∧
    gen TL * rc φ (McL.Dce.tSig HB TB e) * gen TL = rc φ (tPsi HB TB e))
  (ht : gen TL * gen TL = 1)

theorem sig_eq {t s p : G} (ht : t * t = 1) (h : t * s * t = p) : s = t * p * t := by
  rw [← h]
  calc s = (t * t) * s * (t * t) := by rw [ht]; group
    _ = t * (t * s * t) * t := by group

theorem mR_f {R dir : ℕ} (h : Nat.beq dir 1 = false) : mR R dir = McL.Dce.rN R := by
  simp only [mR, h]

theorem mR_t {R dir : ℕ} (h : Nat.beq dir 1 = true) : mR R dir = McL.Dce.rNI R := by
  simp only [mR, h]

omit [Group G] in
theorem mR_inM {R dir : ℕ} (hRN : InM LT TL NL (McL.Dce.rN R))
    (hNN : mul25 (McL.Dce.rN R) (McL.Dce.rNI R) = ident) : InM LT TL NL (mR R dir) := by
  unfold mR
  cases Nat.beq dir 1
  · exact hRN
  · exact InM_inv hRN hNN

include hG hS ht in
theorem step_mean (hT : TL ≠ 255) {w : ℕ → G} {c R dir e S S' : ℕ}
    (hst : LStep HB GB TB TL nT c R dir e S S') (hJ : McL.Dce.rJ R ≤ NO)
    (hPF : mul25 (McL.Dce.rPi R) (McL.Dce.rFI R) = ident)
    (hNN : mul25 (McL.Dce.rN R) (McL.Dce.rNI R) = ident)
    (hRP : InM LT TL NL (McL.Dce.rPi R)) (hRN : InM LT TL NL (McL.Dce.rN R))
    (hP : InM LT TL NL (McL.Dce.sPi S)) :
    InM LT TL NL (McL.Dce.sPi S') ∧
      (SR φ w S (lv gen c) (mR R dir) S' ↔ FM φ gen HB GB w R) := by
  have hFI := InM_inv hRP hPF
  have rFI : rc φ (McL.Dce.rFI R) = (rc φ (McL.Dce.rPi R))⁻¹ := rc_inv φ hRP hPF
  have rNI : rc φ (McL.Dce.rNI R) = (rc φ (McL.Dce.rN R))⁻¹ := rc_inv φ hRN hNN
  rcases hst with ⟨hc, hJ0, he, ⟨hd, hD, hTS, rfl⟩ | ⟨hd, hD, hTP, rfl⟩⟩ |
      ⟨rfl, hJ0, ⟨hd, hD, rfl⟩ | ⟨hd, hD, rfl⟩⟩
  ·
    obtain ⟨hg1, hg2, hgg⟩ := hG (McL.Dce.rJ R - 1) (by omega)
    obtain ⟨hs1, hs2, hsr⟩ := hS e he
    refine ⟨by rw [sPi_mkDp]; exact InM_mul (InM_mul hRP hg2) hs2, ?_⟩
    unfold SR FM tvJ lv
    rw [sD_mkDp, sPi_mkDp, hc, mR_f hd, hD, ite_eq_right hT,
      ite_eq_right (by omega), rc_mul φ (InM_mul hRP hg2) hs2, rc_mul φ hRP hg2, rc_inv φ hg1 hgg]
    have hp : rc φ (McL.Dce.sPi S) = (rc φ (gL HB GB (McL.Dce.rJ R - 1)))⁻¹ *
        rc φ (McL.Dce.tSig HB TB e) := by
      rw [hTS, rc_mul φ hg1 hP]
      group
    rw [hp, sig_eq ht hsr]
    generalize rc φ (gL HB GB (McL.Dce.rJ R - 1)) = g
    generalize rc φ (tPsi HB TB e) = ψ
    have e1 : w (McL.Dce.rD R) * (g⁻¹ * (gen TL * ψ * gen TL)) * gen TL =
        w (McL.Dce.rD R) * (g⁻¹ * gen TL * g) * (g⁻¹ * ψ) := by
      calc _ = w (McL.Dce.rD R) * g⁻¹ * gen TL * ψ * (gen TL * gen TL) := by group
        _ = _ := by rw [ht]; group
    have e2 : rc φ (McL.Dce.rN R) * w (McL.Dce.rDp R) * (rc φ (McL.Dce.rPi R) * g⁻¹ * ψ) =
        rc φ (McL.Dce.rN R) * w (McL.Dce.rDp R) * rc φ (McL.Dce.rPi R) * (g⁻¹ * ψ) := by group
    rw [e1, e2, mul_left_inj]
  ·
    obtain ⟨hg1, hg2, hgg⟩ := hG (McL.Dce.rJ R - 1) (by omega)
    obtain ⟨hs1, hs2, hsr⟩ := hS e he
    refine ⟨by rw [sPi_mkD]; exact InM_mul hg2 hs1, ?_⟩
    unfold SR FM tvJ lv
    rw [sD_mkD, sPi_mkD, hc, mR_t hd, hD, ite_eq_right hT,
      ite_eq_right (by omega), rc_mul φ hg2 hs1, rc_inv φ hg1 hgg, rNI]
    have hp : rc φ (McL.Dce.sPi S) = rc φ (McL.Dce.rPi R) *
        (rc φ (gL HB GB (McL.Dce.rJ R - 1)))⁻¹ * rc φ (tPsi HB TB e) := by
      rw [hTP, rc_mul φ (InM_mul hg1 hFI) hP, rc_mul φ hg1 hFI, rFI]
      group
    rw [hp, sig_eq ht hsr]
    generalize rc φ (gL HB GB (McL.Dce.rJ R - 1)) = g
    generalize rc φ (tPsi HB TB e) = ψ
    generalize rc φ (McL.Dce.rN R) = n
    have e1 : w (McL.Dce.rDp R) * (rc φ (McL.Dce.rPi R) * g⁻¹ * ψ) * gen TL =
        n⁻¹ * (n * w (McL.Dce.rDp R) * rc φ (McL.Dce.rPi R)) * (g⁻¹ * ψ * gen TL) := by group
    have e2 : n⁻¹ * w (McL.Dce.rD R) * (g⁻¹ * (gen TL * ψ * gen TL)) =
        n⁻¹ * (w (McL.Dce.rD R) * (g⁻¹ * gen TL * g)) * (g⁻¹ * ψ * gen TL) := by group
    rw [e1, e2, mul_left_inj, mul_right_inj, eq_comm]
  ·
    refine ⟨by rw [sPi_mkDp]; exact InM_mul hRP hP, ?_⟩
    unfold SR FM tvJ lv
    rw [sD_mkDp, sPi_mkDp, mR_f hd, hD, ite_eq_left rfl, ite_eq_left hJ0, rc_mul φ hRP hP]
    have e1 : w (McL.Dce.rD R) * rc φ (McL.Dce.sPi S) * 1 =
        w (McL.Dce.rD R) * 1 * rc φ (McL.Dce.sPi S) := by group
    have e2 : rc φ (McL.Dce.rN R) * w (McL.Dce.rDp R) *
        (rc φ (McL.Dce.rPi R) * rc φ (McL.Dce.sPi S)) =
        rc φ (McL.Dce.rN R) * w (McL.Dce.rDp R) * rc φ (McL.Dce.rPi R) *
          rc φ (McL.Dce.sPi S) := by group
    rw [e1, e2, mul_left_inj]
  ·
    refine ⟨by rw [sPi_mkD]; exact InM_mul hFI hP, ?_⟩
    unfold SR FM tvJ lv
    rw [sD_mkD, sPi_mkD, mR_t hd, hD, ite_eq_left rfl, ite_eq_left hJ0, rc_mul φ hFI hP, rFI, rNI]
    generalize rc φ (McL.Dce.rN R) = n
    have e1 : w (McL.Dce.rDp R) * rc φ (McL.Dce.sPi S) * 1 =
        n⁻¹ * (n * w (McL.Dce.rDp R) * rc φ (McL.Dce.rPi R)) *
          ((rc φ (McL.Dce.rPi R))⁻¹ * rc φ (McL.Dce.sPi S)) := by group
    have e2 : n⁻¹ * w (McL.Dce.rD R) * ((rc φ (McL.Dce.rPi R))⁻¹ * rc φ (McL.Dce.sPi S)) =
        n⁻¹ * (w (McL.Dce.rD R) * 1) * ((rc φ (McL.Dce.rPi R))⁻¹ * rc φ (McL.Dce.sPi S)) := by
      group
    rw [e1, e2, mul_left_inj, mul_right_inj, eq_comm]

end Mean

variable {HB GB TB : ℕ → ℕ} {NO nT : ℕ}

theorem step_back
    (hG : ∀ j < NO, InM LT TL NL (gL HB GB j) ∧ InM LT TL NL (gH HB GB j) ∧
      mul25 (gL HB GB j) (gH HB GB j) = ident)
    (hS : ∀ e < nT, InM LT TL NL (McL.Dce.tSig HB TB e) ∧ InM LT TL NL (tPsi HB TB e))
    {c R dir e S S' : ℕ} (hst : LStep HB GB TB TL nT c R dir e S S') (hJ : McL.Dce.rJ R ≤ NO)
    (hPF : mul25 (McL.Dce.rPi R) (McL.Dce.rFI R) = ident) (hRP : InM LT TL NL (McL.Dce.rPi R))
    (hP' : InM LT TL NL (McL.Dce.sPi S')) : InM LT TL NL (McL.Dce.sPi S) := by
  have hFI := InM_inv hRP hPF
  rcases hst with ⟨-, hJ0, he, ⟨-, -, hTS, -⟩ | ⟨-, -, hTP, -⟩⟩ | ⟨-, -, ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩⟩
  · have h1 := (hS e he).1
    rw [hTS] at h1
    exact InM_cancel_left (hG (McL.Dce.rJ R - 1) (by omega)).1 h1
  · have h1 := (hS e he).2
    rw [hTP] at h1
    exact InM_cancel_left (InM_mul (hG (McL.Dce.rJ R - 1) (by omega)).1 hFI) h1
  · rw [sPi_mkDp] at hP'
    exact InM_cancel_left hRP hP'
  · rw [sPi_mkD] at hP'
    exact InM_cancel_left hFI hP'

theorem step_own
    (hG : ∀ j < NO, InM LT TL NL (gL HB GB j) ∧ InM LT TL NL (gH HB GB j) ∧
      mul25 (gL HB GB j) (gH HB GB j) = ident)
    (hS : ∀ e < nT, InM LT TL NL (McL.Dce.tSig HB TB e) ∧ InM LT TL NL (tPsi HB TB e))
    {c R dir e S S' : ℕ} (hst : LStep HB GB TB TL nT c R dir e S S') (hJ : McL.Dce.rJ R ≤ NO)
    (hPF : mul25 (McL.Dce.rPi R) (McL.Dce.rFI R) = ident)
    (hP : InM LT TL NL (McL.Dce.sPi S)) (hP' : InM LT TL NL (McL.Dce.sPi S')) :
    InM LT TL NL (McL.Dce.rPi R) := by
  rcases hst with ⟨-, hJ0, he, ⟨-, -, -, rfl⟩ | ⟨-, -, hTP, -⟩⟩ | ⟨-, -, ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩⟩
  · rw [sPi_mkDp] at hP'
    exact InM_cancel_right (hG (McL.Dce.rJ R - 1) (by omega)).2.1
      (InM_cancel_right (hS e he).2 hP')
  · have h1 := (hS e he).2
    rw [hTP] at h1
    exact InM_invL (InM_cancel_left (hG (McL.Dce.rJ R - 1) (by omega)).1
      (InM_cancel_right hP h1)) hPF
  · rw [sPi_mkDp] at hP'
    exact InM_cancel_right hP hP'
  · rw [sPi_mkD] at hP'
    exact InM_invL (InM_cancel_right hP hP') hPF

theorem step_zero
    (hS : ∀ e < nT, InM LT TL NL (McL.Dce.tSig HB TB e) ∧ InM LT TL NL (tPsi HB TB e))
    {c R dir e S S' : ℕ} (hst : LStep HB GB TB TL nT c R dir e S S')
    (h0 : McL.Dce.sPi S = 0) : McL.Dce.sPi S' = 0 := by
  rcases hst with ⟨-, -, he, ⟨-, -, hTS, -⟩ | ⟨-, -, hTP, -⟩⟩ | ⟨-, -, ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩⟩
  · rw [h0, mul25_zero_r] at hTS
    exact absurd hTS (inM_ne_zero (hS e he).1)
  · rw [h0, mul25_zero_r] at hTP
    exact absurd hTP (inM_ne_zero (hS e he).2)
  · rw [sPi_mkDp, h0, mul25_zero_r]
  · rw [sPi_mkD, h0, mul25_zero_r]

end CFSG.Certificates.McLD

end
