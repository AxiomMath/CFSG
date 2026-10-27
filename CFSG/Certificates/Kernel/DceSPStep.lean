module

public import CFSG.Certificates.Kernel.DceSPHom
public import CFSG.Certificates.Kernel.DceTwWalk
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.Certificates.DSP

open CFSG.KC.Loop CFSG.KC.HNA.DceS CFSG.Certificates.DceLoop CFSG.Certificates.DceWord
  CFSG.Certificates.DceTw
open scoped Classical

set_option exponentiation.threshold 400

theorem land16_lt (x : ℕ) : Nat.land x 65535 < 65536 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem sD_mkSt {D : ℕ} (hD : D < 65536) (p : ℕ) : sD (mkSt D p) = D := by
  change (D ||| p <<< 16) &&& 65535 = D
  rw [show (65535 : ℕ) = 2 ^ 16 - 1 from rfl, land_low, lor_shl_mod]
  exact Nat.mod_eq_of_lt (by norm_num; exact hD)

theorem sPi_mkSt {D : ℕ} (hD : D < 65536) (p : ℕ) : sPi (mkSt D p) = p := by
  change (D ||| p <<< 16) >>> 16 = p
  rw [lor_shl_shr, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hD, Nat.zero_or]

theorem sD_bad : sD bad = 65535 := rfl

theorem rD_lt (R : ℕ) : rD R < 65536 := land16_lt R
theorem rDp_lt (R : ℕ) : rDp R < 65536 := land16_lt _

structure RecGood (ND NO R : ℕ) : Prop where
  d : rD R < ND
  dp : rDp R < ND
  j : rJ R ≤ NO
  p : validP (rPi R) = true
  f : validP (rFI R) = true
  pf : mulP (rPi R) (rFI R) = ONEP

theorem recOK_spec {ND NO R : ℕ} (h : recOK ND NO R = true) : RecGood ND NO R := by
  unfold recOK at h
  obtain ⟨e1, r⟩ := andL_iff.1 h
  obtain ⟨e2, r⟩ := andL_iff.1 r
  obtain ⟨e3, r⟩ := andL_iff.1 r
  obtain ⟨e4, r⟩ := andL_iff.1 r
  obtain ⟨e5, e6⟩ := andL_iff.1 r
  exact ⟨Nat.blt_eq.mp e1, Nat.blt_eq.mp e2, Nat.le_of_ble_eq_true e3, e4, e5,
    Nat.eq_of_beq_eq_true e6⟩

@[expose] def Shape (HB GB TB : ℕ → ℕ) (TL VL nT W Wi c R e S S' : ℕ) : Prop :=
  (c = 255 ∧ rJ R = 0 ∧ sD S = rD R ∧ S' = mkSt (rDp R) (mulP (rPi R) (sPi S))) ∨
  (c = 255 ∧ rJ R = 0 ∧ sD S = rDp R ∧ S' = mkSt (rD R) (mulP (rFI R) (sPi S))) ∨
  (c = TL ∧ 0 < rJ R ∧ e < nT ∧ sD S = rD R ∧ tS TB e = mulP (gm HB GB (rJ R - 1)) (sPi S) ∧
    S' = mkSt (rDp R) (mulP (mulP (rPi R) (gi HB GB (rJ R - 1))) (tP TB e))) ∨
  (c = VL ∧ 0 < rJ R ∧ e < nT ∧ sD S = rD R ∧ tS TB e = mulP (gm HB GB (rJ R - 1)) (sPi S) ∧
    S' = mkSt (rDp R) (mulP (mulP (mulP (rPi R) (gi HB GB (rJ R - 1))) (tP TB e)) Wi)) ∨
  (c = TL ∧ 0 < rJ R ∧ e < nT ∧ sD S = rDp R ∧
    tP TB e = mulP (mulP (gm HB GB (rJ R - 1)) (rFI R)) (sPi S) ∧
    S' = mkSt (rD R) (mulP (mulP (gi HB GB (rJ R - 1)) (tS TB e)) W)) ∨
  (c = VL ∧ 0 < rJ R ∧ e < nT ∧ sD S = rDp R ∧
    tP TB e = mulP (mulP (gm HB GB (rJ R - 1)) (rFI R)) (sPi S) ∧
    S' = mkSt (rD R) (mulP (gi HB GB (rJ R - 1)) (tS TB e)))

theorem bad_ne {D p : ℕ} (hD : D < 65535) : mkSt D p ≠ bad := fun h => by
  have := sD_mkSt (show D < 65536 by omega) p
  rw [h, sD_bad] at this
  omega

theorem stepE_shape {R dir S : ℕ} (h : stepE R dir S ≠ bad) :
    rJ R = 0 ∧ ((sD S = rD R ∧ stepE R dir S = mkSt (rDp R) (mulP (rPi R) (sPi S))) ∨
      (sD S = rDp R ∧ stepE R dir S = mkSt (rD R) (mulP (rFI R) (sPi S)))) := by
  unfold stepE at h ⊢
  cases h1 : Nat.beq (rJ R) (nat_lit 0)
  · rw [h1] at h
    exact absurd rfl h
  rw [h1] at h
  refine ⟨Nat.eq_of_beq_eq_true h1, ?_⟩
  dsimp only at h ⊢
  cases h2 : Nat.beq dir (nat_lit 1)
  · rw [h2] at h
    dsimp only at h ⊢
    cases h3 : Nat.beq (sD S) (rD R)
    · rw [h3] at h
      exact absurd rfl h
    · exact Or.inl ⟨Nat.eq_of_beq_eq_true h3, rfl⟩
  · rw [h2] at h
    dsimp only at h ⊢
    cases h3 : Nat.beq (sD S) (rDp R)
    · rw [h3] at h
      exact absurd rfl h
    · exact Or.inr ⟨Nat.eq_of_beq_eq_true h3, rfl⟩

theorem stepU_shape {HB GB TB : ℕ → ℕ} {nT W Wi : ℕ} {isU : Bool} {R dir e S : ℕ}
    (h : stepU HB GB TB nT W Wi isU R dir e S ≠ bad) :
    0 < rJ R ∧ e < nT ∧
      ((sD S = rD R ∧ tS TB e = mulP (gm HB GB (rJ R - 1)) (sPi S) ∧
          stepU HB GB TB nT W Wi isU R dir e S = mkSt (rDp R) (Bool.rec (motive := fun _ => ℕ)
            (mulP (mulP (rPi R) (gi HB GB (rJ R - 1))) (tP TB e))
            (mulP (mulP (mulP (rPi R) (gi HB GB (rJ R - 1))) (tP TB e)) Wi) isU)) ∨
        (sD S = rDp R ∧ tP TB e = mulP (mulP (gm HB GB (rJ R - 1)) (rFI R)) (sPi S) ∧
          stepU HB GB TB nT W Wi isU R dir e S = mkSt (rD R) (Bool.rec (motive := fun _ => ℕ)
            (mulP (mulP (gi HB GB (rJ R - 1)) (tS TB e)) W)
            (mulP (gi HB GB (rJ R - 1)) (tS TB e)) isU))) := by
  unfold stepU at h ⊢
  beta_reduce at h ⊢
  cases h1 : andB (Nat.blt (nat_lit 0) (rJ R)) (Nat.blt e nT)
  · rw [h1] at h
    exact absurd rfl h
  obtain ⟨h1a, h1b⟩ := andL_iff.1 h1
  rw [h1] at h
  refine ⟨Nat.blt_eq.mp h1a, Nat.blt_eq.mp h1b, ?_⟩
  dsimp only at h ⊢
  cases h2 : Nat.beq dir (nat_lit 1)
  · rw [h2] at h
    dsimp only at h ⊢
    cases h3 : andB (Nat.beq (sD S) (rD R))
        (Nat.beq (tS TB e) (mulP (mat HB (lo20 (e40 GB (Nat.sub (rJ R) (nat_lit 1))))) (sPi S)))
    · rw [h3] at h
      exact absurd rfl h
    · obtain ⟨h3a, h3b⟩ := andL_iff.1 h3
      exact Or.inl ⟨Nat.eq_of_beq_eq_true h3a, Nat.eq_of_beq_eq_true h3b, rfl⟩
  · rw [h2] at h
    dsimp only at h ⊢
    cases h3 : andB (Nat.beq (sD S) (rDp R))
        (Nat.beq (tP TB e) (mulP (mulP (mat HB (lo20 (e40 GB (Nat.sub (rJ R) (nat_lit 1))))) (rFI R))
          (sPi S)))
    · rw [h3] at h
      exact absurd rfl h
    · obtain ⟨h3a, h3b⟩ := andL_iff.1 h3
      exact Or.inr ⟨Nat.eq_of_beq_eq_true h3a, Nat.eq_of_beq_eq_true h3b, rfl⟩

theorem stepL_shape {HB GB TB : ℕ → ℕ} {TL VL nT W Wi c R dir e S : ℕ}
    (h : stepL HB GB TB TL VL nT W Wi c R dir e S ≠ bad) :
    Shape HB GB TB TL VL nT W Wi c R e S (stepL HB GB TB TL VL nT W Wi c R dir e S) := by
  unfold stepL at h ⊢
  by_cases c255 : c = 255
  · subst c255
    rw [show Nat.beq 255 255 = true from rfl] at h ⊢
    dsimp only at h ⊢
    obtain ⟨hj, h1 | h1⟩ := stepE_shape h
    · exact Or.inl ⟨rfl, hj, h1⟩
    · exact Or.inr (Or.inl ⟨rfl, hj, h1⟩)
  rw [Bool.eq_false_iff.2 fun e => c255 (Nat.eq_of_beq_eq_true e)] at h ⊢
  dsimp only at h ⊢
  by_cases cT : c = TL
  · subst cT
    rw [Nat.beq_refl] at h ⊢
    dsimp only at h ⊢
    obtain ⟨hj, he, h1 | h1⟩ := stepU_shape h
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, hj, he, h1⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hj, he, h1⟩))))
  rw [Bool.eq_false_iff.2 fun e => cT (Nat.eq_of_beq_eq_true e)] at h ⊢
  dsimp only at h ⊢
  by_cases cV : c = VL
  · subst cV
    rw [Nat.beq_refl] at h ⊢
    dsimp only at h ⊢
    obtain ⟨hj, he, h1 | h1⟩ := stepU_shape h
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hj, he, h1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hj, he, h1⟩))))
  rw [Bool.eq_false_iff.2 fun e => cV (Nat.eq_of_beq_eq_true e)] at h
  exact absurd rfl h

theorem Shape.sD {HB GB TB : ℕ → ℕ} {TL VL nT W Wi c R e S S' : ℕ}
    (h : Shape HB GB TB TL VL nT W Wi c R e S S') : sD S = rD R ∨ sD S = rDp R := by
  rcases h with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, -, h, -⟩ | ⟨-, -, -, h, -⟩ | ⟨-, -, -, h, -⟩ |
    ⟨-, -, -, h, -⟩
  all_goals first | exact Or.inl h | exact Or.inr h

theorem step_bad {HB GB TB : ℕ → ℕ} {TL VL nT W Wi c R dir e S ND NO : ℕ}
    (hR : RecGood ND NO R) (hND : ND < 65535) (hS : sD S = 65535) :
    sD (stepL HB GB TB TL VL nT W Wi c R dir e S) = 65535 := by
  by_contra hne
  have h : stepL HB GB TB TL VL nT W Wi c R dir e S ≠ bad := fun e => hne (by rw [e]; rfl)
  rcases (stepL_shape h).sD with e | e <;> rw [e] at hS
  · have := hR.d
    omega
  · have := hR.dp
    omega

variable {G : Type*} [Group G] {LT LI TL VL NL : ℕ}

structure SCtx (HB GB TB : ℕ → ℕ) (LT LI TL VL NL NO nT W Wi : ℕ) (x : ℕ → G)
    (φ : Mg LT TL VL NL →* G) : Prop where
  hL : LetOK LT LI TL VL NL
  hφ : ∀ c (h : c ∈ Nset TL VL NL),
    φ ⟨Lm LT TL VL NL c, Subgroup.subset_closure ⟨c, h, rfl⟩⟩ = x c
  hu : x VL = (x TL)⁻¹
  gj : ∀ j < NO, InM LT TL VL NL (gm HB GB j) ∧ InM LT TL VL NL (gi HB GB j) ∧
    mulP (gm HB GB j) (gi HB GB j) = ONEP
  ts : ∀ e < nT, InM LT TL VL NL (tS TB e) ∧ InM LT TL VL NL (tP TB e) ∧
    (x TL)⁻¹ * rc φ (tS TB e) * x TL = rc φ (tP TB e)
  wW : InM LT TL VL NL W ∧ InM LT TL VL NL Wi ∧ mulP W Wi = ONEP ∧ x TL * x TL = rc φ W

@[expose] noncomputable def uv (φ : Mg LT TL VL NL →* G) (HB GB : ℕ → ℕ) (x : ℕ → G) (J : ℕ) : G :=
  if J = 0 then 1 else (rc φ (gm HB GB (J - 1)))⁻¹ * x TL * rc φ (gm HB GB (J - 1))

@[expose] def FM (φ : Mg LT TL VL NL →* G) (HB GB : ℕ → ℕ) (x w : ℕ → G) (R : ℕ) : Prop :=
  RelT (Ncl x TL VL NL) (w (rD R) * uv φ HB GB x (rJ R)) (w (rDp R) * rc φ (rPi R))

@[expose] noncomputable def rep (φ : Mg LT TL VL NL →* G) (w : ℕ → G) (S : ℕ) : G :=
  w (sD S) * rc φ (sPi S)

theorem InM_cancelL {A B : ℕ} (hA : InM LT TL VL NL A) (hAB : InM LT TL VL NL (mulP A B))
    (hB : PV B) : InM LT TL VL NL B := by
  refine ⟨hB, ?_⟩
  have e := mP_mul hA.1 hB
  have e2 : mP B = (mP A)⁻¹ * mP (mulP A B) := by rw [e, inv_mul_cancel_left]
  rw [e2]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hA.2) hAB.2

theorem InM_cancelR {A B : ℕ} (hB : InM LT TL VL NL B) (hAB : InM LT TL VL NL (mulP A B))
    (hA : PV A) : InM LT TL VL NL A := by
  refine ⟨hA, ?_⟩
  have e := mP_mul hA hB.1
  have e2 : mP A = mP (mulP A B) * (mP B)⁻¹ := by rw [e, mul_inv_cancel_right]
  rw [e2]
  exact Subgroup.mul_mem _ hAB.2 (Subgroup.inv_mem _ hB.2)

theorem rJ_sub {ND NO R : ℕ} (hR : RecGood ND NO R) (hj : 0 < rJ R) : rJ R - 1 < NO := by
  have := hR.j
  omega

section Steps

variable {HB GB TB : ℕ → ℕ} {NO nT W Wi ND : ℕ} {x : ℕ → G} {φ : Mg LT TL VL NL →* G}
  (h : SCtx HB GB TB LT LI TL VL NL NO nT W Wi x φ) {c R e S S' : ℕ}
  (hR : RecGood ND NO R) (hsh : Shape HB GB TB TL VL nT W Wi c R e S S')
include h hR hsh

theorem step_PV (hS : PV (sPi S)) : PV (sPi S') := by
  have cP := validP_spec hR.p
  have cF := validP_spec hR.f
  rcases hsh with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, hj, he, -, -, rfl⟩ | ⟨-, hj, he, -, -, rfl⟩ |
    ⟨-, hj, he, -, -, rfl⟩ | ⟨-, hj, he, -, -, rfl⟩
  all_goals rw [sPi_mkSt (by first | exact rD_lt R | exact rDp_lt R)]
  · exact mulP_PV cP hS
  · exact mulP_PV cF hS
  · obtain ⟨-, gi1, -⟩ := h.gj _ (rJ_sub hR hj)
    exact mulP_PV (mulP_PV cP gi1.1) (h.ts e he).2.1.1
  · obtain ⟨-, gi1, -⟩ := h.gj _ (rJ_sub hR hj)
    exact mulP_PV (mulP_PV (mulP_PV cP gi1.1) (h.ts e he).2.1.1) h.wW.2.1.1
  · obtain ⟨-, gi1, -⟩ := h.gj _ (rJ_sub hR hj)
    exact mulP_PV (mulP_PV gi1.1 (h.ts e he).1.1) h.wW.1.1
  · obtain ⟨-, gi1, -⟩ := h.gj _ (rJ_sub hR hj)
    exact mulP_PV gi1.1 (h.ts e he).1.1

theorem step_fwd (hRm : InM LT TL VL NL (rPi R)) (hS : InM LT TL VL NL (sPi S)) :
    InM LT TL VL NL (sPi S') := by
  have hF := InM_invR hRm (validP_spec hR.f) hR.pf
  rcases hsh with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, hj, he, -, -, rfl⟩ | ⟨-, hj, he, -, -, rfl⟩ |
    ⟨-, hj, he, -, -, rfl⟩ | ⟨-, hj, he, -, -, rfl⟩
  all_goals rw [sPi_mkSt (by first | exact rD_lt R | exact rDp_lt R)]
  · exact InM_mul hRm hS
  · exact InM_mul hF hS
  · exact InM_mul (InM_mul hRm (h.gj _ (rJ_sub hR hj)).2.1) (h.ts e he).2.1
  · exact InM_mul (InM_mul (InM_mul hRm (h.gj _ (rJ_sub hR hj)).2.1) (h.ts e he).2.1) h.wW.2.1
  · exact InM_mul (InM_mul (h.gj _ (rJ_sub hR hj)).2.1 (h.ts e he).1) h.wW.1
  · exact InM_mul (h.gj _ (rJ_sub hR hj)).2.1 (h.ts e he).1

theorem step_back (hRm : InM LT TL VL NL (rPi R)) (hSc : PV (sPi S))
    (hS' : InM LT TL VL NL (sPi S')) : InM LT TL VL NL (sPi S) := by
  have hF := InM_invR hRm (validP_spec hR.f) hR.pf
  rcases hsh with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, hj, he, -, eT, -⟩ | ⟨-, hj, he, -, eT, -⟩ |
    ⟨-, hj, he, -, eT, -⟩ | ⟨-, hj, he, -, eT, -⟩
  · rw [sPi_mkSt (rDp_lt R)] at hS'
    exact InM_cancelL hRm hS' hSc
  · rw [sPi_mkSt (rD_lt R)] at hS'
    exact InM_cancelL hF hS' hSc
  · exact InM_cancelL (h.gj _ (rJ_sub hR hj)).1 (eT ▸ (h.ts e he).1) hSc
  · exact InM_cancelL (h.gj _ (rJ_sub hR hj)).1 (eT ▸ (h.ts e he).1) hSc
  · exact InM_cancelL (InM_mul (h.gj _ (rJ_sub hR hj)).1 hF) (eT ▸ (h.ts e he).2.1) hSc
  · exact InM_cancelL (InM_mul (h.gj _ (rJ_sub hR hj)).1 hF) (eT ▸ (h.ts e he).2.1) hSc

theorem step_own (hS : InM LT TL VL NL (sPi S)) (hS' : InM LT TL VL NL (sPi S')) :
    InM LT TL VL NL (rPi R) := by
  have cP := validP_spec hR.p
  have cF := validP_spec hR.f
  have ofF : InM LT TL VL NL (rFI R) → InM LT TL VL NL (rPi R) := fun hF =>
    InM_invL hF cP hR.pf
  rcases hsh with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, hj, he, -, -, rfl⟩ | ⟨-, hj, he, -, -, rfl⟩ |
    ⟨-, hj, he, -, eT, -⟩ | ⟨-, hj, he, -, eT, -⟩
  · rw [sPi_mkSt (rDp_lt R)] at hS'
    exact InM_cancelR hS hS' cP
  · rw [sPi_mkSt (rD_lt R)] at hS'
    exact ofF (InM_cancelR hS hS' cF)
  · rw [sPi_mkSt (rDp_lt R)] at hS'
    obtain ⟨-, gi1, -⟩ := h.gj _ (rJ_sub hR hj)
    exact InM_cancelR gi1 (InM_cancelR (h.ts e he).2.1 hS' (mulP_PV cP gi1.1)) cP
  · rw [sPi_mkSt (rDp_lt R)] at hS'
    obtain ⟨-, gi1, -⟩ := h.gj _ (rJ_sub hR hj)
    have c1 := mulP_PV cP gi1.1
    have c2 := mulP_PV c1 (h.ts e he).2.1.1
    exact InM_cancelR gi1 (InM_cancelR (h.ts e he).2.1 (InM_cancelR h.wW.2.1 hS' c2) c1) cP
  · obtain ⟨g1, -, -⟩ := h.gj _ (rJ_sub hR hj)
    have hGF := InM_cancelR hS (eT ▸ (h.ts e he).2.1) (mulP_PV g1.1 cF)
    exact ofF (InM_cancelL g1 hGF cF)
  · obtain ⟨g1, -, -⟩ := h.gj _ (rJ_sub hR hj)
    have hGF := InM_cancelR hS (eT ▸ (h.ts e he).2.1) (mulP_PV g1.1 cF)
    exact ofF (InM_cancelL g1 hGF cF)

theorem step_sem (w : ℕ → G) (hRm : InM LT TL VL NL (rPi R)) (hS : InM LT TL VL NL (sPi S)) :
    RelT (Ncl x TL VL NL) (rep φ w S * lvE x c) (rep φ w S') ↔ FM φ HB GB x w R := by
  have hF := InM_invR hRm (validP_spec hR.f) hR.pf
  have rF := rc_invR φ hRm (validP_spec hR.f) hR.pf
  have hT255 : TL ≠ 255 := by have := h.hL.tl; have := h.hL.nl; omega
  have hV255 : VL ≠ 255 := by have := h.hL.vl; have := h.hL.nl; omega
  unfold FM rep
  rcases hsh with ⟨rfl, hj, hD, rfl⟩ | ⟨rfl, hj, hD, rfl⟩ | ⟨rfl, hj, he, hD, eT, rfl⟩ |
    ⟨rfl, hj, he, hD, eT, rfl⟩ | ⟨rfl, hj, he, hD, eT, rfl⟩ | ⟨rfl, hj, he, hD, eT, rfl⟩
  · rw [sD_mkSt (rDp_lt R), sPi_mkSt (rDp_lt R), hD, rc_mul φ hRm hS, uv, ite_eq_left hj, lvE,
      ite_eq_left rfl]
    exact eps_fwd _ _ _ _
  · rw [sD_mkSt (rD_lt R), sPi_mkSt (rD_lt R), hD, rc_mul φ hF hS, rF, uv, ite_eq_left hj, lvE,
      ite_eq_left rfl]
    exact eps_bwd _ _ _ _
  all_goals
    obtain ⟨g1, gi1, ggi⟩ := h.gj _ (rJ_sub hR hj)
    obtain ⟨s1, p1, ps⟩ := h.ts e he
    have rGi := rc_invR φ g1 gi1.1 ggi
    rw [uv, ite_eq_right (by omega)]
  · rw [sD_mkSt (rDp_lt R), sPi_mkSt (rDp_lt R), hD, rc_mul φ (InM_mul hRm gi1) p1,
      rc_mul φ hRm gi1, rGi, lvE, ite_eq_right hT255]
    exact u_fwd _ _ _ _ _ _ _ _ (by rw [eT, rc_mul φ g1 hS]) ps
  · rw [sD_mkSt (rDp_lt R), sPi_mkSt (rDp_lt R), hD,
      rc_mul φ (InM_mul (InM_mul hRm gi1) p1) h.wW.2.1, rc_mul φ (InM_mul hRm gi1) p1,
      rc_mul φ hRm gi1, rGi, rc_invR φ h.wW.1 h.wW.2.1.1 h.wW.2.2.1, lvE, ite_eq_right hV255, h.hu]
    exact U_fwd _ _ _ _ _ _ _ _ _ (by rw [eT, rc_mul φ g1 hS]) ps h.wW.2.2.2
  · rw [sD_mkSt (rD_lt R), sPi_mkSt (rD_lt R), hD, rc_mul φ (InM_mul gi1 s1) h.wW.1,
      rc_mul φ gi1 s1, rGi, lvE, ite_eq_right hT255]
    exact u_bwd _ _ _ _ _ _ _ _ _ (by rw [eT, rc_mul φ (InM_mul g1 hF) hS, rc_mul φ g1 hF, rF])
      ps h.wW.2.2.2
  · rw [sD_mkSt (rD_lt R), sPi_mkSt (rD_lt R), hD, rc_mul φ gi1 s1, rGi, lvE, ite_eq_right hV255, h.hu]
    exact U_bwd _ _ _ _ _ _ _ _ (by rw [eT, rc_mul φ (InM_mul g1 hF) hS, rc_mul φ g1 hF, rF])
      ps

end Steps

end CFSG.Certificates.DSP

end
