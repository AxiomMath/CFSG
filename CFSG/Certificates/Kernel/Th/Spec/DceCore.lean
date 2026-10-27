module

public import CFSG.Certificates.Kernel.Th.Spec.DceMat
public import CFSG.Certificates.Kernel.DceWords
public import CFSG.Certificates.Kernel.Common.RelNorm
import Mathlib.Tactic.Group
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KC.Th.Spec.Dce

open CFSG.KC.Th CFSG.KC.Th.DceS CFSG.KC.Loop CFSG.Certificates.DceLoop
  CFSG.Certificates.DceWord

set_option exponentiation.threshold 700

theorem M576_eq : M576 = 2 ^ 576 - 1 := rfl


theorem land255_lt (x : ℕ) : Nat.land x 255 < 256 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem land_M576_lt (x : ℕ) : Nat.land x M576 < 2 ^ 576 :=
  Nat.lt_of_le_of_lt Nat.and_le_right
    (by rw [M576_eq]; exact Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)

theorem sD_mkSt {D : ℕ} (hD : D < 256) (p : ℕ) : sD (mkSt D p) = D := by
  change (D ||| p <<< 8) &&& 255 = D
  rw [show (255 : ℕ) = 2 ^ 8 - 1 from rfl, land_low, lor_shl_mod]
  exact Nat.mod_eq_of_lt (by norm_num; exact hD)

theorem sPi_mkSt {D : ℕ} (hD : D < 256) (p : ℕ) : sPi (mkSt D p) = p := by
  change (D ||| p <<< 8) >>> 8 = p
  rw [lor_shl_shr, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hD, Nat.zero_or]

theorem sD_bad : sD bad = 255 := rfl

theorem sD_lt (S : ℕ) : sD S < 256 := land255_lt S

theorem rD_lt (R : ℕ) : rD R < 256 := land255_lt R

theorem rDp_lt (R : ℕ) : rDp R < 256 := land255_lt _

theorem rPi_lt (R : ℕ) : rPi R < 2 ^ 576 := land_M576_lt _

theorem rFI_lt (R : ℕ) : rFI R < 2 ^ 576 := land_M576_lt _

theorem rN_lt (R : ℕ) : rN R < 2 ^ 576 := land_M576_lt _

theorem rNI_lt (R : ℕ) : rNI R < 2 ^ 576 := land_M576_lt _

theorem mat_lt (HB : ℕ → ℕ) (h : ℕ) : mat HB h < 2 ^ 576 := land_M576_lt _

theorem let24_lt (LT c : ℕ) : let24 LT c < 2 ^ 576 := land_M576_lt _

theorem isN_iff {TL VL NL c : ℕ} : isN TL VL NL c = true ↔ c < NL ∧ c ≠ TL ∧ c ≠ VL := by
  unfold isN
  rw [andB_iff, andB_iff, notB_iff, notB_iff, Nat.blt_eq]
  refine and_congr_right fun _ => and_congr ⟨fun h e => ?_, fun h => ?_⟩
    ⟨fun h e => ?_, fun h => ?_⟩
  · rw [e] at h
    exact absurd h (by simp)
  · exact Bool.eq_false_iff.2 fun e => h (Nat.eq_of_beq_eq_true e)
  · rw [e] at h
    exact absurd h (by simp)
  · exact Bool.eq_false_iff.2 fun e => h (Nat.eq_of_beq_eq_true e)

structure LetOK (LT LC LI TL VL NL : ℕ) : Prop where
  nl : NL < 255
  tl : TL < NL
  vl : VL < NL
  tv : TL ≠ VL
  inv : ∀ c < NL, byte LI (byte LI c) = c ∧ byte LI c < NL ∧
    byte LC (byte LI c) = Nat.xor (byte LC c) 1
  nval : ∀ c, isN TL VL NL c = true → byte LC c < 14 ∧
    mul24 (let24 LT c) (let24 LT (byte LI c)) = ident24
  tc : byte LC TL = 14
  vc : byte LC VL = 15

theorem lettersOK_spec {LT LC LI TL VL NL : ℕ} (h : DceS.lettersOK LT LC LI TL VL NL = true) :
    LetOK LT LC LI TL VL NL := by
  unfold DceS.lettersOK at h
  obtain ⟨h1, r⟩ := andB_iff.1 h
  obtain ⟨h2, r⟩ := andB_iff.1 r
  obtain ⟨h3, r⟩ := andB_iff.1 r
  obtain ⟨h4, h5⟩ := andB_iff.1 r
  have hall := (allB_iff (fun c => letterOK LT LC LI TL VL NL c) NL).1 h5
  have hTL : TL < NL := Nat.blt_eq.mp h2
  have hVL : VL < NL := Nat.blt_eq.mp h3
  have hc : ∀ c < NL, byte LC (byte LI c) = Nat.xor (byte LC c) 1 ∧
      byte LI (byte LI c) = c ∧ byte LI c < NL ∧
      Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool) false (Nat.beq (byte LC c) 15) (Nat.beq c VL))
          (Nat.beq (byte LC c) 14) (Nat.beq c TL))
        (andB (Nat.blt (byte LC c) 14)
          (Nat.beq (mul24 (let24 LT c) (let24 LT (byte LI c))) ident24))
        (isN TL VL NL c) = true := by
    intro c hc
    have e := hall c hc
    unfold letterOK at e
    obtain ⟨e1, r⟩ := andB_iff.1 e
    obtain ⟨e2, r⟩ := andB_iff.1 r
    obtain ⟨e3, e4⟩ := andB_iff.1 r
    exact ⟨Nat.eq_of_beq_eq_true e1, Nat.eq_of_beq_eq_true e2, Nat.blt_eq.mp e3, e4⟩
  have hT : TL ≠ VL := Nat.ne_of_beq_eq_false ((notB_iff).1 h4)
  have hNT : isN TL VL NL TL = false := by
    cases e2 : isN TL VL NL TL
    · rfl
    · exact absurd rfl (isN_iff.1 e2).2.1
  have hNV : isN TL VL NL VL = false := by
    cases e2 : isN TL VL NL VL
    · rfl
    · exact absurd rfl (isN_iff.1 e2).2.2
  refine ⟨Nat.blt_eq.mp h1, hTL, hVL, hT,
    fun c hc' => ⟨(hc c hc').2.1, (hc c hc').2.2.1, (hc c hc').1⟩, fun c hN => ?_, ?_, ?_⟩
  · obtain ⟨-, -, -, e⟩ := hc c (isN_iff.1 hN).1
    rw [hN] at e
    obtain ⟨e1, e2⟩ := andB_iff.1 e
    exact ⟨Nat.blt_eq.mp e1, Nat.eq_of_beq_eq_true e2⟩
  · obtain ⟨-, -, -, e⟩ := hc TL hTL
    rw [hNT, Nat.beq_refl] at e
    exact Nat.eq_of_beq_eq_true e
  · obtain ⟨-, -, -, e⟩ := hc VL hVL
    rw [hNV] at e
    have hne : Nat.beq VL TL = false :=
      Bool.eq_false_iff.2 fun e2 => hT (Nat.eq_of_beq_eq_true e2).symm
    rw [hne] at e
    change Bool.rec (motive := fun _ => Bool) false (Nat.beq (byte LC VL) 15) (Nat.beq VL VL) = true
      at e
    rw [Nat.beq_refl] at e
    exact Nat.eq_of_beq_eq_true e

section Letters

variable {LT LC LI TL VL NL : ℕ} (hL : LetOK LT LC LI TL VL NL)
include hL

theorem LetOK.tli : byte LI TL = VL := by
  obtain ⟨-, hlt, hcode⟩ := hL.inv TL hL.tl
  rw [hL.tc] at hcode
  by_contra hne
  have hnN : isN TL VL NL (byte LI TL) = false := by
    cases e : isN TL VL NL (byte LI TL)
    · rfl
    · have := (hL.nval _ e).1
      rw [hcode] at this
      exact absurd this (by decide)
  have h := isN_iff.not.1 (by rw [hnN]; decide)
  have : byte LI TL = TL := by
    by_contra hne2
    exact h ⟨hlt, hne2, hne⟩
  rw [this, hL.tc] at hcode
  exact absurd hcode (by decide)

theorem LetOK.vli : byte LI VL = TL := by
  obtain ⟨-, hlt, hcode⟩ := hL.inv VL hL.vl
  rw [hL.vc] at hcode
  by_contra hne
  have hnN : isN TL VL NL (byte LI VL) = false := by
    cases e : isN TL VL NL (byte LI VL)
    · rfl
    · have := (hL.nval _ e).1
      rw [hcode] at this
      exact absurd this (by decide)
  have h := isN_iff.not.1 (by rw [hnN]; decide)
  have : byte LI VL = VL := by
    by_contra hne2
    exact h ⟨hlt, hne, hne2⟩
  rw [this, hL.vc] at hcode
  exact absurd hcode (by decide)

theorem LetOK.isN_inv {c : ℕ} (hc : isN TL VL NL c = true) :
    isN TL VL NL (byte LI c) = true := by
  obtain ⟨h1, h2, h3⟩ := isN_iff.1 hc
  refine isN_iff.2 ⟨(hL.inv c h1).2.1, fun e => h3 ?_, fun e => h2 ?_⟩
  · rw [← (hL.inv c h1).1, e, hL.tli]
  · rw [← (hL.inv c h1).1, e, hL.vli]

end Letters

theorem toMat_zero : toMat 0 = 0 := by
  ext i j
  simp [toMat]

theorem zero_lt_576 : (0 : ℕ) < 2 ^ 576 := Nat.two_pow_pos _

theorem mul24_zero_left (X : ℕ) : mul24 0 X = 0 :=
  eq_of_toMat_eq (mul24_lt _ _) zero_lt_576 (by rw [toMat_mul24, toMat_zero, zero_mul])

theorem mul24_zero_right (X : ℕ) : mul24 X 0 = 0 :=
  eq_of_toMat_eq (mul24_lt _ _) zero_lt_576 (by rw [toMat_mul24, toMat_zero, mul_zero])

open scoped Classical in
@[expose] noncomputable def Lm (LT LI TL VL NL c : ℕ) : Mat24ˣ :=
  if h : isN TL VL NL c = true ∧ toMat (let24 LT c) * toMat (let24 LT (byte LI c)) = 1 then
    ⟨toMat (let24 LT c), toMat (let24 LT (byte LI c)), h.2, mul_eq_one_comm.1 h.2⟩
  else 1

@[expose] def Nset (TL VL NL : ℕ) : Set ℕ := {c | c < NL ∧ isN TL VL NL c = true}

@[expose] def InM (M : Subgroup Mat24ˣ) (A : ℕ) : Prop :=
  A < 2 ^ 576 ∧ ∃ y ∈ M, ((y : Mat24ˣ) : Mat24) = toMat A

open scoped Classical in
@[expose] noncomputable def mEl (M : Subgroup Mat24ˣ) (A : ℕ) : M :=
  if h : InM M A then ⟨Classical.choose h.2, (Classical.choose_spec h.2).1⟩ else 1

section Model

variable {M : Subgroup Mat24ˣ}

theorem mEl_val {A : ℕ} (h : InM M A) : (((mEl M A : M) : Mat24ˣ) : Mat24) = toMat A := by
  unfold mEl
  rw [dite_eq_left h]
  exact (Classical.choose_spec h.2).2

theorem InM_one : InM M ident24 :=
  ⟨ident24_lt, 1, Subgroup.one_mem _, by rw [toMat_ident24, Units.val_one]⟩

theorem InM_mul {A B : ℕ} (hA : InM M A) (hB : InM M B) : InM M (mul24 A B) := by
  obtain ⟨-, u, hu, eu⟩ := hA
  obtain ⟨-, v, hv, ev⟩ := hB
  exact ⟨mul24_lt _ _, u * v, Subgroup.mul_mem _ hu hv, by rw [Units.val_mul, eu, ev, toMat_mul24]⟩

theorem InM_invR {A B : ℕ} (hA : InM M A) (hB : B < 2 ^ 576) (h : mul24 A B = ident24) :
    InM M B := by
  obtain ⟨-, u, hu, eu⟩ := hA
  have e : toMat A * toMat B = 1 := by rw [← toMat_mul24, h, toMat_ident24]
  refine ⟨hB, u⁻¹, Subgroup.inv_mem _ hu, ?_⟩
  rw [← mul_one ((u⁻¹ : Mat24ˣ) : Mat24), ← e, ← mul_assoc, ← eu, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_mul]

theorem InM_invL {A B : ℕ} (hB : InM M B) (hA : A < 2 ^ 576) (h : mul24 A B = ident24) :
    InM M A := by
  obtain ⟨-, v, hv, ev⟩ := hB
  have e : toMat A * toMat B = 1 := by rw [← toMat_mul24, h, toMat_ident24]
  refine ⟨hA, v⁻¹, Subgroup.inv_mem _ hv, ?_⟩
  rw [← one_mul ((v⁻¹ : Mat24ˣ) : Mat24), ← e, mul_assoc, ← ev, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, mul_one]

theorem InM_cancelL {A B : ℕ} (hA : InM M A) (hAB : InM M (mul24 A B)) (hB : B < 2 ^ 576) :
    InM M B := by
  obtain ⟨-, y, hy, ey⟩ := hA
  obtain ⟨-, z, hz, ez⟩ := hAB
  refine ⟨hB, y⁻¹ * z, Subgroup.mul_mem _ (Subgroup.inv_mem _ hy) hz, ?_⟩
  rw [Units.val_mul, ez, toMat_mul24, ← ey, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_mul]

theorem InM_cancelR {A B : ℕ} (hB : InM M B) (hAB : InM M (mul24 A B)) (hA : A < 2 ^ 576) :
    InM M A := by
  obtain ⟨-, y, hy, ey⟩ := hB
  obtain ⟨-, z, hz, ez⟩ := hAB
  refine ⟨hA, z * y⁻¹, Subgroup.mul_mem _ hz (Subgroup.inv_mem _ hy), ?_⟩
  rw [Units.val_mul, ez, toMat_mul24, ← ey, mul_assoc, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, mul_one]

theorem InM_ne_zero : ¬InM M 0 := by
  rintro ⟨-, y, -, hy⟩
  rw [toMat_zero] at hy
  have := y.val_inv
  rw [hy, zero_mul] at this
  have h1 : (1 : Mat24) 0 0 = 0 := by rw [← this]; rfl
  exact absurd h1 (by decide)

end Model

section Rc

variable {M : Subgroup Mat24ˣ} {G : Type*} [Group G] {LT LC LI TL VL NL : ℕ}

@[expose] noncomputable def rc (φ : M →* G) (A : ℕ) : G := φ (mEl M A)

theorem mEl_eq {A : ℕ} (y : M) (hA : A < 2 ^ 576) (hy : ((y : Mat24ˣ) : Mat24) = toMat A) :
    mEl M A = y := by
  have h : InM M A := ⟨hA, y, y.2, hy⟩
  apply Subtype.ext
  apply Units.ext
  rw [mEl_val h, hy]

theorem rc_eq (φ : M →* G) {A : ℕ} (y : M) (hA : A < 2 ^ 576)
    (hy : ((y : Mat24ˣ) : Mat24) = toMat A) : rc φ A = φ y := by
  unfold rc
  rw [mEl_eq y hA hy]

theorem rc_one (φ : M →* G) : rc φ ident24 = 1 := by
  rw [rc_eq φ 1 ident24_lt (by rw [toMat_ident24]; rfl), map_one]

theorem rc_mul (φ : M →* G) {A B : ℕ} (hA : InM M A) (hB : InM M B) :
    rc φ (mul24 A B) = rc φ A * rc φ B := by
  have hAB := InM_mul hA hB
  rw [rc_eq φ (mEl M A * mEl M B) hAB.1 (by
    rw [Subgroup.coe_mul, Units.val_mul, mEl_val hA, mEl_val hB, toMat_mul24]), map_mul]
  rfl

theorem rc_invR (φ : M →* G) {A B : ℕ} (hA : InM M A) (hB : B < 2 ^ 576)
    (h : mul24 A B = ident24) : rc φ B = (rc φ A)⁻¹ := by
  have hB' := InM_invR hA hB h
  have e := rc_mul φ hA hB'
  rw [h, rc_one φ] at e
  exact (inv_eq_of_mul_eq_one_right e.symm).symm

theorem Lm_val (hL : LetOK LT LC LI TL VL NL) {c : ℕ} (hN : isN TL VL NL c = true) :
    ((Lm LT LI TL VL NL c : Mat24ˣ) : Mat24) = toMat (let24 LT c) := by
  have h : toMat (let24 LT c) * toMat (let24 LT (byte LI c)) = 1 := by
    rw [← toMat_mul24, (hL.nval c hN).2, toMat_ident24]
  unfold Lm
  rw [dite_eq_left ⟨hN, h⟩]

structure MCtx (M : Subgroup Mat24ˣ) (LT LC LI TL VL NL : ℕ) {G : Type*} [Group G] (x : ℕ → G)
    (φ : M →* G) : Prop where
  hL : LetOK LT LC LI TL VL NL
  hM : ∀ c, isN TL VL NL c = true → Lm LT LI TL VL NL c ∈ M
  hφ : ∀ c (h : isN TL VL NL c = true), φ ⟨Lm LT LI TL VL NL c, hM c h⟩ = x c
  hu : x VL = (x TL)⁻¹

variable {x : ℕ → G} {φ : M →* G} (hC : MCtx M LT LC LI TL VL NL x φ)
include hC

theorem MCtx.inM_letter {c : ℕ} (hN : isN TL VL NL c = true) : InM M (let24 LT c) :=
  ⟨let24_lt _ _, _, hC.hM c hN, Lm_val hC.hL hN⟩

theorem MCtx.rc_letter {c : ℕ} (hN : isN TL VL NL c = true) : rc φ (let24 LT c) = x c := by
  rw [rc_eq φ ⟨_, hC.hM c hN⟩ (let24_lt _ _) (Lm_val hC.hL hN)]
  exact hC.hφ c hN

end Rc

section SegHdr

variable {M : Subgroup Mat24ˣ} {G : Type*} [Group G] {LT LC LI TL VL NL : ℕ}
  {x : ℕ → G} {φ : M →* G} (hC : MCtx M LT LC LI TL VL NL x φ)
include hC

theorem rc_segProd (Wd o : ℕ) : ∀ m, segProd LT TL VL NL Wd o m ≠ 0 →
    (∀ k < m, isN TL VL NL (byte Wd (o + k)) = true) ∧ InM M (segProd LT TL VL NL Wd o m) ∧
      rc φ (segProd LT TL VL NL Wd o m) = ((List.range m).map fun k => x (byte Wd (o + k))).prod
  | 0, _ => ⟨fun k hk => absurd hk (Nat.not_lt_zero k), InM_one, rc_one φ⟩
  | m + 1, hne => by
    have hs : segProd LT TL VL NL Wd o (m + 1) = Bool.rec (motive := fun _ => ℕ) 0
        (mul24 (segProd LT TL VL NL Wd o m) (let24 LT (byte Wd (o + m))))
        (isN TL VL NL (byte Wd (o + m))) := rfl
    rw [hs] at hne ⊢
    cases hN : isN TL VL NL (byte Wd (o + m))
    · rw [hN] at hne
      exact absurd rfl hne
    · rw [hN] at hne
      dsimp only at hne ⊢
      have hne' : segProd LT TL VL NL Wd o m ≠ 0 := fun h0 => by
        rw [h0, mul24_zero_left] at hne
        exact hne rfl
      obtain ⟨h1, h2, h3⟩ := rc_segProd Wd o m hne'
      refine ⟨fun k hk => ?_, InM_mul h2 (hC.inM_letter hN), ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact h1 k hk
        · exact hN
      · rw [rc_mul φ h2 (hC.inM_letter hN), h3, hC.rc_letter hN, List.range_succ,
          List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]

end SegHdr

theorem hdrOK_spec {HB FA : ℕ → ℕ} {LT TL VL NL shA wdA NFA h d : ℕ}
    (hh : hdrOK HB FA LT TL VL NL shA wdA NFA h d = true) :
    mat HB h = ident24 ∨ (∃ a, isN TL VL NL a = true ∧ mat HB h = let24 LT a) ∨
      (∃ a b, a < h ∧ b < h ∧ mat HB h = mul24 (mat HB a) (mat HB b)) ∨
      (∃ a, a < h ∧ mul24 (mat HB h) (mat HB a) = ident24) ∨
      (∃ f, impOK FA shA wdA NFA f = true ∧ mat HB h = rN (rec FA shA wdA f)) ∨
      (∃ f, impOK FA shA wdA NFA f = true ∧ mat HB h = rFI (rec FA shA wdA f)) := by
  unfold hdrOK at hh
  beta_reduce at hh
  generalize mat HB h = H at hh ⊢
  generalize Nat.land d 7 = k at hh
  generalize bits d 3 20 = a at hh
  generalize bits d 23 20 = b at hh
  revert hh
  cases hk0 : Nat.beq k 0
  · cases hk1 : Nat.beq k 1
    · cases hk2 : Nat.beq k 2
      · cases hk3 : Nat.beq k 3
        · cases hk5 : Nat.beq k 5
          · cases hk6 : Nat.beq k 6
            · intro hh
              exact absurd hh Bool.false_ne_true
            · intro hh
              change andB (impOK FA shA wdA NFA a) (Nat.beq H (rFI (rec FA shA wdA a))) = true at hh
              obtain ⟨e1, e2⟩ := andB_iff.1 hh
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, e1, Nat.eq_of_beq_eq_true e2⟩))))
          · intro hh
            change andB (impOK FA shA wdA NFA a) (Nat.beq H (rN (rec FA shA wdA a))) = true at hh
            obtain ⟨e1, e2⟩ := andB_iff.1 hh
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, e1, Nat.eq_of_beq_eq_true e2⟩))))
        · intro hh
          change andB (Nat.blt a h) (Nat.beq (mul24 H (mat HB a)) ident24) = true at hh
          obtain ⟨e1, e2⟩ := andB_iff.1 hh
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, Nat.blt_eq.mp e1, Nat.eq_of_beq_eq_true e2⟩)))
      · intro hh
        change andB (Nat.blt a h) (andB (Nat.blt b h)
          (Nat.beq H (mul24 (mat HB a) (mat HB b)))) = true at hh
        obtain ⟨e1, r⟩ := andB_iff.1 hh
        obtain ⟨e2, e3⟩ := andB_iff.1 r
        exact Or.inr (Or.inr (Or.inl ⟨a, b, Nat.blt_eq.mp e1, Nat.blt_eq.mp e2,
          Nat.eq_of_beq_eq_true e3⟩))
    · intro hh
      change andB (isN TL VL NL a) (Nat.beq H (let24 LT a)) = true at hh
      obtain ⟨e1, e2⟩ := andB_iff.1 hh
      exact Or.inr (Or.inl ⟨a, e1, Nat.eq_of_beq_eq_true e2⟩)
  · intro hh
    change Nat.beq H ident24 = true at hh
    exact Or.inl (Nat.eq_of_beq_eq_true hh)

theorem runHdr_eq (HB FA : ℕ → ℕ) (LT TL VL NL shA wdA NFA : ℕ) (Cs : List ℕ) (S : ℕ) :
    runHdr HB FA LT TL VL NL shA wdA NFA Cs S = cntRun
      (fun k J => hdrOK HB FA LT TL VL NL shA wdA NFA k (bits J 0 43)) (fun _ => 43) 255 8 Cs S :=
  rfl

theorem andBK_iff {a b : Bool} : CFSG.KC.andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem relsNorm_spec {RR : ℕ → ℕ} {NR : ℕ} (h : CFSG.KC.relsNorm RR NR = true) :
    ∀ r < NR, Nat.shiftRight (RR r) 12 < 256 ^ bits (RR r) 2 10 := by
  have key : ∀ n, CFSG.KC.relsNorm RR n = true → ∀ r < n,
      Nat.blt (Nat.shiftRight (RR r) 12)
        (Nat.shiftLeft 1 (Nat.mul 8 (Nat.land (Nat.shiftRight (RR r) 2) 1023))) = true := by
    intro n
    induction n with
    | zero => exact fun _ r hr => absurd hr (Nat.not_lt_zero r)
    | succ n ih =>
      intro h r hr
      have h' : CFSG.KC.andB (CFSG.KC.relsNorm RR n)
          (Nat.blt (Nat.shiftRight (RR n) 12)
            (Nat.shiftLeft 1 (Nat.mul 8 (Nat.land (Nat.shiftRight (RR n) 2) 1023)))) = true := h
      rw [andBK_iff] at h'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
      · exact ih h'.1 r hr
      · exact h'.2
  intro r hr
  have h1 := key NR h r hr
  rw [Nat.blt_eq] at h1
  have e : Nat.land (Nat.shiftRight (RR r) 2) 1023 = bits (RR r) 2 10 := rfl
  rw [e] at h1
  change Nat.shiftRight (RR r) 12 < 1 <<< (8 * bits (RR r) 2 10) at h1
  rw [Nat.one_shiftLeft, pow_mul] at h1
  norm_num at h1
  exact h1

theorem relOK_spec {RR : ℕ → ℕ} {LT LC TL VL NL RH r : ℕ}
    (h : relOK RR LT LC TL VL NL RH r = true) :
    byte RH r < 39 ∧
      4 * bits (RR r) 2 10 + (mapW LC (Nat.shiftRight (RR r) 12) (bits (RR r) 2 10)) <<< 12 =
        Hsw.sel (byte RH r) ∧
      (∀ i < bits (RR r) 2 10, byte (Nat.shiftRight (RR r) 12) i < NL) ∧
      ((∀ i < bits (RR r) 2 10, isN TL VL NL (byte (Nat.shiftRight (RR r) 12) i) = true) →
        segProd LT TL VL NL (Nat.shiftRight (RR r) 12) 0 (bits (RR r) 2 10) = ident24) := by
  unfold relOK at h
  beta_reduce at h
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h⟩ := andB_iff.1 h
  obtain ⟨h3, h4⟩ := andB_iff.1 h
  refine ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2, fun i hi => Nat.blt_eq.mp
    ((allB_iff (fun i => Nat.blt (byte (Nat.shiftRight (RR r) 12) i) NL) _).1 h3 i hi),
    fun hN => ?_⟩
  rcases orB_iff.1 h4 with h5 | h5
  · rw [notB_iff] at h5
    have : Nat.rec (motive := fun _ => Bool) true (fun i ih => andB ih (isN TL VL NL
        (byte (Nat.shiftRight (RR r) 12) i))) (bits (RR r) 2 10) = true :=
      (allB_iff (fun i => isN TL VL NL (byte (Nat.shiftRight (RR r) 12) i)) _).2 hN
    rw [h5] at this
    exact absurd this Bool.false_ne_true
  · exact Nat.eq_of_beq_eq_true h5

theorem relsOK_spec {RR : ℕ → ℕ} {LT LC TL VL NL RH NR : ℕ}
    (h : relsOK RR LT LC TL VL NL RH NR = true) :
    ∀ r < NR, relOK RR LT LC TL VL NL RH r = true :=
  (allB_iff (fun r => relOK RR LT LC TL VL NL RH r) NR).1 h

@[expose] noncomputable def rval {G : Type*} [Group G] (x : ℕ → G) (e : ℕ) : G :=
  wv x (Nat.shiftRight e 12) (bits e 2 10)

theorem toMat_land_M576 (y : ℕ) : toMat (Nat.land y M576) = toMat y := by
  ext i j
  simp only [toMat, Matrix.of_apply]
  change (((y &&& M576).testBit _).toNat : ZMod 2) = _
  have hd : decide (24 * (i : ℕ) + j < 576) = true := decide_eq_true (by omega)
  rw [Nat.testBit_and, M576_eq, Nat.testBit_two_pow_sub_one, hd, Bool.and_true]

theorem mul24_land_right (A B : ℕ) : mul24 A (Nat.land B M576) = mul24 A B :=
  eq_of_toMat_eq (mul24_lt _ _) (mul24_lt _ _) (by rw [toMat_mul24, toMat_mul24, toMat_land_M576])

theorem wordOK_spec {WD RR : ℕ → ℕ} {LI NL NR WH w : ℕ} (h : wordOK WD RR LI NL NR WH w = true) :
    byte WH w < NR ∧ (∀ q < bits (WD w) 2 10, byte (Nat.shiftRight (WD w) 12) q < NL ∨
      byte (Nat.shiftRight (WD w) 12) q = 255) ∧
      chkWord LI (Nat.shiftRight (WD w) 12) (bits (WD w) 2 10)
        (Nat.shiftRight (RR (byte WH w)) 12) (bits (RR (byte WH w)) 2 10) = true := by
  unfold wordOK at h
  beta_reduce at h
  obtain ⟨e1, r⟩ := andB_iff.1 h
  obtain ⟨e2, e3⟩ := andB_iff.1 r
  refine ⟨Nat.blt_eq.mp e1, fun q hq => ?_, e3⟩
  have := (allB_iff (fun i => orB (Nat.blt (byte (Nat.shiftRight (WD w) 12) i) NL)
    (Nat.beq (byte (Nat.shiftRight (WD w) 12) i) 255)) _).1 e2 q hq
  rcases orB_iff.1 this with h1 | h1
  · exact Or.inl (Nat.blt_eq.mp h1)
  · exact Or.inr (Nat.eq_of_beq_eq_true h1)

section Words

variable {G : Type*} [Group G] {LT LC LI TL VL NL : ℕ}

theorem words_sem {x : ℕ → G} {WD RR : ℕ → ℕ} {NR WH nW : ℕ} (hL : LetOK LT LC LI TL VL NL)
    (hrels : ∀ r < NR, rval x (RR r) = 1) (hnorm : CFSG.KC.relsNorm RR NR = true)
    (hinv : ∀ c < NL, isN TL VL NL c = true → x (byte LI c) = (x c)⁻¹) (hu : x VL = (x TL)⁻¹)
    (hw : wordsOK WD RR LI NL NR WH nW = true) :
    ∀ w < nW, wv (lvE x) (Nat.shiftRight (WD w) 12) (bits (WD w) 2 10) = 1 := by
  have hall : ∀ c < NL, x (byte LI c) = (x c)⁻¹ := by
    intro c hc
    by_cases hN : isN TL VL NL c = true
    · exact hinv c hc hN
    · have : c = TL ∨ c = VL := by
        by_contra hne
        push Not at hne
        exact hN (isN_iff.2 ⟨hc, hne.1, hne.2⟩)
      rcases this with rfl | rfl
      · rw [hL.tli, hu]
      · rw [hL.vli, hu, inv_inv]
  intro w hw'
  obtain ⟨h1, h2, h3⟩ := wordOK_spec
    ((allB_iff (fun w => wordOK WD RR LI NL NR WH w) nW).1 hw w hw')
  exact chkWord_sound x (relsNorm_spec hnorm _ h1) (hrels _ h1) (fun q hq hne =>
    hall _ ((h2 q hq).resolve_right hne)) h3

end Words

theorem ident24_ne_zero : ident24 ≠ 0 := by decide +kernel

theorem usqOK_spec {RR : ℕ → ℕ} {LT LI TL VL NL NR USQ W Wi h : ℕ}
    (hu : usqOK RR LT LI TL VL NL NR USQ W Wi h = true) :
    h < NR ∧ W = segProd LT TL VL NL (Nat.shiftRight USQ 12) 0 (bits USQ 2 10) ∧
      mul24 W Wi = ident24 ∧ bits (RR h) 2 10 = bits USQ 2 10 + 2 ∧
      CFSG.KC.Th.isRot (Nat.shiftRight (RR h) 12) (bits USQ 2 10 + 2)
        (CFSG.KC.Th.wCat (Nat.lor TL (Nat.shiftLeft TL 8)) 2
          (CFSG.KC.Th.wInv LI (Nat.shiftRight USQ 12) (bits USQ 2 10))) = true := by
  unfold usqOK at hu
  beta_reduce at hu
  obtain ⟨e1, r⟩ := andB_iff.1 hu
  obtain ⟨e2, r⟩ := andB_iff.1 r
  obtain ⟨e3, r⟩ := andB_iff.1 r
  obtain ⟨e4, e5⟩ := andB_iff.1 r
  exact ⟨Nat.blt_eq.mp e1, Nat.eq_of_beq_eq_true e2, Nat.eq_of_beq_eq_true e3,
    Nat.eq_of_beq_eq_true e4, e5⟩

theorem TT_eq {T : ℕ} (hT : T < 256) : Nat.lor T (Nat.shiftLeft T 8) = T + 256 * T := by
  have := lor_mul T T 1 (by simpa using hT)
  simpa using this

theorem TT_lt {T : ℕ} (hT : T < 256) : Nat.lor T (Nat.shiftLeft T 8) < 256 ^ 2 := by
  rw [TT_eq hT]
  norm_num
  omega

theorem wv_TT {G : Type*} [Group G] (f : ℕ → G) {T : ℕ} (hT : T < 256) :
    wv f (Nat.lor T (Nat.shiftLeft T 8)) 2 = f T * f T := by
  have e := TT_eq hT
  have b0 : byteG (Nat.lor T (Nat.shiftLeft T 8)) 0 = T := by
    rw [byteG_eq, e, CFSG.Certificates.KB.Sound.byte_eq']
    simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hT]
  have b1 : byteG (Nat.lor T (Nat.shiftLeft T 8)) 1 = T := by
    rw [byteG_eq, e, CFSG.Certificates.KB.Sound.byte_eq']
    rw [pow_one, Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hT, Nat.zero_add,
      Nat.mod_eq_of_lt hT]
  unfold wv
  rw [show List.range 2 = [0, 1] from rfl]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [b0, b1]

section Usq

variable {M : Subgroup Mat24ˣ} {G : Type*} [Group G] {LT LC LI TL VL NL : ℕ}
  {x : ℕ → G} {φ : M →* G} (hC : MCtx M LT LC LI TL VL NL x φ)
  {RR : ℕ → ℕ} {NR : ℕ} (hrels : ∀ r < NR, rval x (RR r) = 1)
  (hnorm : CFSG.KC.relsNorm RR NR = true)
  (hxi : ∀ c < NL, isN TL VL NL c = true → x (byte LI c) = (x c)⁻¹)
include hC hrels hnorm hxi

theorem usq_sem {USQ W Wi h : ℕ} (hu : usqOK RR LT LI TL VL NL NR USQ W Wi h = true) :
    InM M W ∧ InM M (Nat.land Wi M576) ∧ mul24 W (Nat.land Wi M576) = ident24 ∧
      x TL * x TL = rc φ W ∧ rc φ (Nat.land Wi M576) = (rc φ W)⁻¹ := by
  obtain ⟨hh, eW, hWW, hlen, hrot⟩ := usqOK_spec hu
  have hWW' : mul24 W (Nat.land Wi M576) = ident24 := by rw [mul24_land_right]; exact hWW
  have hWne : W ≠ 0 := fun h0 => by
    rw [h0, mul24_zero_left] at hWW
    exact ident24_ne_zero hWW.symm
  rw [eW] at hWne
  obtain ⟨hN, hWm, vW⟩ := rc_segProd hC _ 0 _ hWne
  rw [← eW] at hWm vW
  have hWim := InM_invR hWm (land_M576_lt Wi) hWW'
  refine ⟨hWm, hWim, hWW', ?_, rc_invR φ hWm (land_M576_lt Wi) hWW'⟩
  obtain ⟨s, -, hs⟩ := isRot_spec hrot
  have hval := wv_rot x (relsNorm_spec hnorm h hh) (hrels h hh) s
  rw [hlen, hs] at hval
  have hTL : TL < 256 := by have := hC.hL.tl; have := hC.hL.nl; omega
  rw [show bits USQ 2 10 + 2 = 2 + bits USQ 2 10 from Nat.add_comm _ _, wv_wCat x (TT_lt hTL)
    (wInv_lt _ _ _), wv_TT x hTL, wv_wInv x _ _ _ (fun q hq => by
      have h1 := hN q hq
      rw [Nat.zero_add] at h1
      exact hxi _ (isN_iff.1 h1).1 h1)] at hval
  rw [vW, eq_of_mul_inv_eq_one hval]
  unfold wv
  simp only [Nat.zero_add]
  rfl

end Usq


theorem byte_eq_byteG (x i : ℕ) : byte x i = byteG x i := rfl

theorem relVisOK_spec {RR : ℕ → ℕ} {LT TL VL NL NR S P r s ns : ℕ}
    (h : relVisOK RR LT TL VL NL NR S P r s ns = true) :
    r < NR ∧ ns + 2 ≤ bits (RR r) 2 10 ∧
      byte (CFSG.KC.Th.rot (Nat.shiftRight (RR r) 12) (bits (RR r) 2 10) s) 0 = VL ∧
      byte (CFSG.KC.Th.rot (Nat.shiftRight (RR r) 12) (bits (RR r) 2 10) s) (ns + 1) = TL ∧
      S = segProd LT TL VL NL (CFSG.KC.Th.rot (Nat.shiftRight (RR r) 12) (bits (RR r) 2 10) s)
        1 ns ∧
      mul24 P (segProd LT TL VL NL (CFSG.KC.Th.rot (Nat.shiftRight (RR r) 12) (bits (RR r) 2 10) s)
        (ns + 2) (bits (RR r) 2 10 - (ns + 2))) = ident24 := by
  unfold relVisOK at h
  beta_reduce at h
  obtain ⟨e1, r⟩ := andB_iff.1 h
  obtain ⟨-, r⟩ := andB_iff.1 r
  obtain ⟨e3, r⟩ := andB_iff.1 r
  obtain ⟨e4, r⟩ := andB_iff.1 r
  obtain ⟨e5, r⟩ := andB_iff.1 r
  obtain ⟨e6, e7⟩ := andB_iff.1 r
  exact ⟨Nat.blt_eq.mp e1, Nat.le_of_ble_eq_true e3, Nat.eq_of_beq_eq_true e4,
    Nat.eq_of_beq_eq_true e5, Nat.eq_of_beq_eq_true e6, Nat.eq_of_beq_eq_true e7⟩

section Psi

variable {M : Subgroup Mat24ˣ} {G : Type*} [Group G] {LT LC LI TL VL NL : ℕ}
  {x : ℕ → G} {φ : M →* G} (hC : MCtx M LT LC LI TL VL NL x φ)
  {RR : ℕ → ℕ} {NR : ℕ} (hrels : ∀ r < NR, rval x (RR r) = 1)
  (hnorm : CFSG.KC.relsNorm RR NR = true)
include hC hrels hnorm

theorem relVis_sem {S P r s ns : ℕ} (h : relVisOK RR LT TL VL NL NR S P r s ns = true)
    (hS : InM M S) (hP : P < 2 ^ 576) :
    InM M P ∧ (x TL)⁻¹ * rc φ S * x TL = rc φ P := by
  obtain ⟨hr, hn, h0, h1, eS, eP⟩ := relVisOK_spec h
  set n := bits (RR r) 2 10
  set Wd := CFSG.KC.Th.rot (Nat.shiftRight (RR r) 12) n s
  have hQne : segProd LT TL VL NL Wd (ns + 2) (n - (ns + 2)) ≠ 0 := fun h0' => by
    rw [h0', mul24_zero_right] at eP
    exact ident24_ne_zero eP.symm
  obtain ⟨-, hQ, vQ⟩ := rc_segProd hC Wd (ns + 2) _ hQne
  have hSne : S ≠ 0 := fun h0' => InM_ne_zero (h0' ▸ hS)
  rw [eS] at hSne hS ⊢
  obtain ⟨-, -, vS⟩ := rc_segProd hC Wd 1 ns hSne
  have hPm : InM M P := InM_invL hQ hP eP
  refine ⟨hPm, ?_⟩
  have hinv := rc_invR φ hPm hQ.1 eP
  have hval : wv x Wd n = 1 := wv_rot x (relsNorm_spec hnorm r hr) (hrels r hr) s
  have e2 : n = (ns + 2) + (n - (ns + 2)) := by omega
  rw [e2, wv_split, show ns + 2 = (1 + ns) + 1 by omega, wv_succ, wv_split] at hval
  have hw1 : wv x Wd 1 = x VL := by
    unfold wv
    simp only [List.range_one, List.map_singleton, List.prod_singleton]
    rw [← byte_eq_byteG, h0]
  rw [hw1, ← byte_eq_byteG, show 1 + ns = ns + 1 by omega, h1, hC.hu] at hval
  have hP' : rc φ P = (rc φ (segProd LT TL VL NL Wd (ns + 2) (n - (ns + 2))))⁻¹ := by
    rw [hinv, inv_inv]
  rw [vS, hP', vQ]
  have hval' : (x TL)⁻¹ * ((List.range ns).map fun k => x (byte Wd (1 + k))).prod * x TL *
      ((List.range (n - (ns + 2))).map fun k => x (byte Wd (ns + 2 + k))).prod = 1 := hval
  exact eq_inv_of_mul_eq_one_left hval'

end Psi

@[expose] noncomputable def tPsi (HB TB : ℕ → ℕ) (e : ℕ) : ℕ := mat HB (hi20 (e40 TB e))

@[expose] noncomputable def gm (HB GB : ℕ → ℕ) (j : ℕ) : ℕ := mat HB (lo20 (e40 GB j))

@[expose] noncomputable def gi (HB GB : ℕ → ℕ) (j : ℕ) : ℕ := mat HB (hi20 (e40 GB j))

theorem runT_eq (HB TB OB RR FA : ℕ → ℕ)
    (LT TL VL NL NR nH nT osh owd om NB sel I0 shA wdA NFA : ℕ) (Cs : List ℕ) (S : ℕ) :
    runT HB TB OB RR FA LT TL VL NL NR nH nT osh owd om NB sel I0 shA wdA NFA Cs S = cntRun
      (fun k J => tOK HB TB OB RR FA LT TL VL NL NR nH nT osh owd om NB sel I0 shA wdA NFA k
        (bits J 0 59) (bits J 59 (tauBits NB))) (fun _ => Nat.add 59 (tauBits NB)) 65535 16 Cs S :=
  rfl

theorem runGom_eq (HB GB OB : ℕ → ℕ) (osh owd om NB sel I0 nH : ℕ) (Cs : List ℕ) (S : ℕ) :
    runGom HB GB OB osh owd om NB sel I0 nH Cs S = cntRun
      (fun k J => gomOK HB GB OB osh owd om NB sel I0 nH k (bits J 0 (tauBits NB)))
      (fun _ => tauBits NB) 65535 16 Cs S := rfl

theorem tOK_spec {HB TB OB RR FA : ℕ → ℕ}
    {LT TL VL NL NR nH nT osh owd om NB sel I0 shA wdA NFA e d tau : ℕ}
    (ht : tOK HB TB OB RR FA LT TL VL NL NR nH nT osh owd om NB sel I0 shA wdA NFA e d tau = true) :
    lo20 (e40 TB e) < nH ∧ hi20 (e40 TB e) < nH ∧ (∃ ep < nT, tPsi HB TB e = tSig HB TB ep) ∧
      actOK NB sel (pt OB osh owd om I0) (tSig HB TB e) (pt OB osh owd om I0) tau = true ∧
      ((∃ a b, a < e ∧ b < e ∧ tSig HB TB e = mul24 (tSig HB TB a) (tSig HB TB b) ∧
          tPsi HB TB e = mul24 (tPsi HB TB a) (tPsi HB TB b)) ∨
        (∃ r s ns, relVisOK RR LT TL VL NL NR (tSig HB TB e) (tPsi HB TB e) r s ns = true) ∨
        (∃ f, impOK FA shA wdA NFA f = true ∧ tSig HB TB e = rN (rec FA shA wdA f) ∧
          tPsi HB TB e = rFI (rec FA shA wdA f))) := by
  unfold tOK at ht
  beta_reduce at ht
  obtain ⟨e1, r⟩ := andB_iff.1 ht
  obtain ⟨e2, r⟩ := andB_iff.1 r
  obtain ⟨e3, r⟩ := andB_iff.1 r
  obtain ⟨e4, r⟩ := andB_iff.1 r
  obtain ⟨e5, e6⟩ := andB_iff.1 r
  refine ⟨Nat.blt_eq.mp e1, Nat.blt_eq.mp e2, ⟨_, Nat.blt_eq.mp e3, Nat.eq_of_beq_eq_true e4⟩,
    e5, ?_⟩
  revert e6
  cases Nat.beq (Nat.land d 3) 0
  · cases Nat.beq (Nat.land d 3) 1
    · cases Nat.beq (Nat.land d 3) 2
      · intro e6
        exact absurd e6 Bool.false_ne_true
      · intro e6
        obtain ⟨f1, f2⟩ := andB_iff.1 e6
        obtain ⟨f2, f3⟩ := andB_iff.1 f2
        exact Or.inr (Or.inr ⟨_, f1, Nat.eq_of_beq_eq_true f2, Nat.eq_of_beq_eq_true f3⟩)
    · intro e6
      exact Or.inr (Or.inl ⟨_, _, _, e6⟩)
  · intro e6
    obtain ⟨f1, r⟩ := andB_iff.1 e6
    obtain ⟨f2, r⟩ := andB_iff.1 r
    obtain ⟨f3, f4⟩ := andB_iff.1 r
    exact Or.inl ⟨_, _, Nat.blt_eq.mp f1, Nat.blt_eq.mp f2, Nat.eq_of_beq_eq_true f3,
      Nat.eq_of_beq_eq_true f4⟩

@[expose] def ImpSem {M : Subgroup Mat24ˣ} {G : Type*} [Group G] (φ : M →* G) (x : ℕ → G)
    (TL : ℕ) (FA : ℕ → ℕ) (shA wdA NFA : ℕ) : Prop :=
  ∀ f, impOK FA shA wdA NFA f = true → InM M (rN (rec FA shA wdA f)) ∧
    InM M (rFI (rec FA shA wdA f)) ∧
    (x TL)⁻¹ * rc φ (rN (rec FA shA wdA f)) * x TL = rc φ (rFI (rec FA shA wdA f))

section Header

variable {M : Subgroup Mat24ˣ} {G : Type*} [Group G] {LT LC LI TL VL NL : ℕ}
  {x : ℕ → G} {φ : M →* G} (hC : MCtx M LT LC LI TL VL NL x φ)
include hC

theorem hdr_mem {HB FA : ℕ → ℕ} {Ch : List ℕ} {nH shA wdA NFA : ℕ}
    (himp : ImpSem φ x TL FA shA wdA NFA)
    (hhdr : runHdr HB FA LT TL VL NL shA wdA NFA Ch 1 = nH + 1) : ∀ h < nH, InM M (mat HB h) := by
  rw [runHdr_eq] at hhdr
  have hi := cntRun_spec (a := 0) hhdr
  intro h
  induction h using Nat.strong_induction_on with
  | _ h ih =>
    intro hh
    obtain ⟨J, hd⟩ := hi h (Nat.zero_le _) hh
    rcases hdrOK_spec hd with e | ⟨a, ha, e⟩ | ⟨a, b, ha, hb, e⟩ | ⟨a, ha, e⟩ | ⟨f, hf, e⟩ |
      ⟨f, hf, e⟩
    · rw [e]
      exact InM_one
    · rw [e]
      exact hC.inM_letter ha
    · rw [e]
      exact InM_mul (ih a ha (by omega)) (ih b hb (by omega))
    · exact InM_invL (ih a ha (by omega)) (mat_lt HB h) e
    · rw [e]
      exact (himp f hf).1
    · rw [e]
      exact (himp f hf).2.1

end Header

theorem gomOK_spec {HB GB OB : ℕ → ℕ} {osh owd om NB sel I0 nH j tau : ℕ}
    (hg : gomOK HB GB OB osh owd om NB sel I0 nH j tau = true) :
    lo20 (e40 GB j) < nH ∧ hi20 (e40 GB j) < nH ∧
      actOK NB sel (pt OB osh owd om I0) (gm HB GB j) (pt OB osh owd om j) tau = true ∧
      mul24 (gm HB GB j) (gi HB GB j) = ident24 ∧
      (NB = 1 ∨ rowsOK NB (pt OB osh owd om j) = true) := by
  unfold gomOK at hg
  beta_reduce at hg
  obtain ⟨e1, r⟩ := andB_iff.1 hg
  obtain ⟨e2, r⟩ := andB_iff.1 r
  obtain ⟨e3, r⟩ := andB_iff.1 r
  obtain ⟨e4, e5⟩ := andB_iff.1 r
  refine ⟨Nat.blt_eq.mp e1, Nat.blt_eq.mp e2, e3, Nat.eq_of_beq_eq_true e4, ?_⟩
  cases hn : Nat.beq NB 1
  · rw [hn] at e5
    exact Or.inr e5
  · exact Or.inl (Nat.eq_of_beq_eq_true hn)

section Table

variable {M : Subgroup Mat24ˣ} {G : Type*} [Group G] {LT LC LI TL VL NL : ℕ}
  {x : ℕ → G} {φ : M →* G} (hC : MCtx M LT LC LI TL VL NL x φ)
  {RR : ℕ → ℕ} {NR : ℕ} (hrels : ∀ r < NR, rval x (RR r) = 1)
  (hnorm : CFSG.KC.relsNorm RR NR = true)
include hC hrels hnorm

theorem gom_mem {HB GB OB FA : ℕ → ℕ} {Ch Cg : List ℕ} {nH NO osh owd om NB sel I0 shA wdA NFA : ℕ}
    (himp : ImpSem φ x TL FA shA wdA NFA)
    (hhdr : runHdr HB FA LT TL VL NL shA wdA NFA Ch 1 = nH + 1)
    (hgom : runGom HB GB OB osh owd om NB sel I0 nH Cg 1 = NO + 1) :
    ∀ j < NO, InM M (gm HB GB j) ∧ InM M (gi HB GB j) ∧ mul24 (gm HB GB j) (gi HB GB j) = ident24 ∧
      (NB = 1 ∨ rowsOK NB (pt OB osh owd om j) = true) ∧
      ∃ tau, actOK NB sel (pt OB osh owd om I0) (gm HB GB j) (pt OB osh owd om j) tau = true := by
  rw [runGom_eq] at hgom
  have hi := cntRun_spec (a := 0) hgom
  have hm := hdr_mem hC himp hhdr
  intro j hj
  obtain ⟨J, hg⟩ := hi j (Nat.zero_le _) hj
  obtain ⟨h1, h2, h3, h4, h5⟩ := gomOK_spec hg
  exact ⟨hm _ h1, hm _ h2, h4, h5, _, h3⟩

theorem psi_sem {HB TB OB FA : ℕ → ℕ} {Ch Ct : List ℕ}
    {nH nT osh owd om NB sel I0 shA wdA NFA : ℕ}
    (himp : ImpSem φ x TL FA shA wdA NFA)
    (hhdr : runHdr HB FA LT TL VL NL shA wdA NFA Ch 1 = nH + 1)
    (hT : runT HB TB OB RR FA LT TL VL NL NR nH nT osh owd om NB sel I0 shA wdA NFA Ct 1 = nT + 1) :
    ∀ e < nT, InM M (tSig HB TB e) ∧ InM M (tPsi HB TB e) ∧
      (x TL)⁻¹ * rc φ (tSig HB TB e) * x TL = rc φ (tPsi HB TB e) := by
  have hm := hdr_mem hC himp hhdr
  rw [runT_eq] at hT
  have hi := cntRun_spec (a := 0) hT
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro he
    obtain ⟨J, ht⟩ := hi e (Nat.zero_le _) he
    obtain ⟨h1, h2, -, -, hk⟩ := tOK_spec ht
    have hS : InM M (tSig HB TB e) := hm _ h1
    have hP : InM M (tPsi HB TB e) := hm _ h2
    refine ⟨hS, hP, ?_⟩
    rcases hk with ⟨a, b, ha, hb, eS, eP⟩ | ⟨r, s, ns, hr⟩ | ⟨f, hf, eS, eP⟩
    · obtain ⟨sa, pa, ea⟩ := ih a ha (by omega)
      obtain ⟨sb, pb, eb⟩ := ih b hb (by omega)
      rw [eS, eP, rc_mul φ sa sb, rc_mul φ pa pb, ← ea, ← eb]
      group
    · exact (relVis_sem hC hrels hnorm hr hS (mat_lt _ _)).2
    · rw [eS, eP]
      exact (himp f hf).2.2

end Table

end CFSG.KC.Th.Spec.Dce

end
