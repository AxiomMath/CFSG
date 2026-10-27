module

public import CFSG.Certificates.Kernel.DceS5Hom
public import CFSG.Certificates.Kernel.DceTwWalk

public section

namespace CFSG.Certificates.DS5

open CFSG.KC.Loop CFSG.KC.LL.Ly7 CFSG.KC.LyA.DceS CFSG.Certificates.DceLoop
  CFSG.Certificates.DceWord CFSG.Certificates.DceTw
open scoped Classical

set_option exponentiation.threshold 400

theorem land255_lt (x : ℕ) : Nat.land x 255 < 256 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem sD_mkSt {D : ℕ} (hD : D < 256) (p : ℕ) : sD (mkSt D p) = D := by
  change (D ||| p <<< 8) &&& 255 = D
  rw [show (255 : ℕ) = 2 ^ 8 - 1 from rfl, land_low, lor_shl_mod]
  exact Nat.mod_eq_of_lt (by norm_num; exact hD)

theorem sPi_mkSt {D : ℕ} (hD : D < 256) (p : ℕ) : sPi (mkSt D p) = p := by
  change (D ||| p <<< 8) >>> 8 = p
  rw [lor_shl_shr, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hD, Nat.zero_or]

theorem sD_bad : sD bad = 255 := rfl

theorem rD_lt (R : ℕ) : rD R < 256 := land255_lt R
theorem rDp_lt (R : ℕ) : rDp R < 256 := land255_lt _

structure RecGood (ND NO R : ℕ) : Prop where
  d : rD R < ND
  dp : rDp R < ND
  j : rJ R ≤ NO
  p : validM7 (rPi R) = true
  f : validM7 (rFI R) = true
  pf : mul7 (rPi R) (rFI R) = ONE7

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
  (c = 255 ∧ rJ R = 0 ∧ sD S = rD R ∧ S' = mkSt (rDp R) (mul7 (rPi R) (sPi S))) ∨
  (c = 255 ∧ rJ R = 0 ∧ sD S = rDp R ∧ S' = mkSt (rD R) (mul7 (rFI R) (sPi S))) ∨
  (c = TL ∧ 0 < rJ R ∧ e < nT ∧ sD S = rD R ∧ tS TB e = mul7 (gm HB GB (rJ R - 1)) (sPi S) ∧
    S' = mkSt (rDp R) (mul7 (mul7 (rPi R) (gi HB GB (rJ R - 1))) (tP TB e))) ∨
  (c = VL ∧ 0 < rJ R ∧ e < nT ∧ sD S = rD R ∧ tS TB e = mul7 (gm HB GB (rJ R - 1)) (sPi S) ∧
    S' = mkSt (rDp R) (mul7 (mul7 (mul7 (rPi R) (gi HB GB (rJ R - 1))) (tP TB e)) Wi)) ∨
  (c = TL ∧ 0 < rJ R ∧ e < nT ∧ sD S = rDp R ∧
    tP TB e = mul7 (mul7 (gm HB GB (rJ R - 1)) (rFI R)) (sPi S) ∧
    S' = mkSt (rD R) (mul7 (mul7 (gi HB GB (rJ R - 1)) (tS TB e)) W)) ∨
  (c = VL ∧ 0 < rJ R ∧ e < nT ∧ sD S = rDp R ∧
    tP TB e = mul7 (mul7 (gm HB GB (rJ R - 1)) (rFI R)) (sPi S) ∧
    S' = mkSt (rD R) (mul7 (gi HB GB (rJ R - 1)) (tS TB e)))

theorem bad_ne {D p : ℕ} (hD : D < 255) : mkSt D p ≠ bad := fun h => by
  have := sD_mkSt (show D < 256 by omega) p
  rw [h, sD_bad] at this
  omega

theorem stepE_shape {R dir S : ℕ} (h : stepE R dir S ≠ bad) :
    rJ R = 0 ∧ ((sD S = rD R ∧ stepE R dir S = mkSt (rDp R) (mul7 (rPi R) (sPi S))) ∨
      (sD S = rDp R ∧ stepE R dir S = mkSt (rD R) (mul7 (rFI R) (sPi S)))) := by
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
      ((sD S = rD R ∧ tS TB e = mul7 (gm HB GB (rJ R - 1)) (sPi S) ∧
          stepU HB GB TB nT W Wi isU R dir e S = mkSt (rDp R) (Bool.rec (motive := fun _ => ℕ)
            (mul7 (mul7 (rPi R) (gi HB GB (rJ R - 1))) (tP TB e))
            (mul7 (mul7 (mul7 (rPi R) (gi HB GB (rJ R - 1))) (tP TB e)) Wi) isU)) ∨
        (sD S = rDp R ∧ tP TB e = mul7 (mul7 (gm HB GB (rJ R - 1)) (rFI R)) (sPi S) ∧
          stepU HB GB TB nT W Wi isU R dir e S = mkSt (rD R) (Bool.rec (motive := fun _ => ℕ)
            (mul7 (mul7 (gi HB GB (rJ R - 1)) (tS TB e)) W)
            (mul7 (gi HB GB (rJ R - 1)) (tS TB e)) isU))) := by
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
        (Nat.beq (tS TB e) (mul7 (mat HB (lo20 (e40 GB (Nat.sub (rJ R) (nat_lit 1))))) (sPi S)))
    · rw [h3] at h
      exact absurd rfl h
    · obtain ⟨h3a, h3b⟩ := andL_iff.1 h3
      exact Or.inl ⟨Nat.eq_of_beq_eq_true h3a, Nat.eq_of_beq_eq_true h3b, rfl⟩
  · rw [h2] at h
    dsimp only at h ⊢
    cases h3 : andB (Nat.beq (sD S) (rDp R))
        (Nat.beq (tP TB e) (mul7 (mul7 (mat HB (lo20 (e40 GB (Nat.sub (rJ R) (nat_lit 1))))) (rFI R))
          (sPi S)))
    · rw [h3] at h
      exact absurd rfl h
    · obtain ⟨h3a, h3b⟩ := andL_iff.1 h3
      exact Or.inr ⟨Nat.eq_of_beq_eq_true h3a, Nat.eq_of_beq_eq_true h3b, rfl⟩

theorem stepL_shape {HB GB TB : ℕ → ℕ} {TL VL nT W Wi c R dir e S : ℕ} (hTV : TL ≠ VL)
    (hT : TL ≠ 255) (hV : VL ≠ 255) (h : stepL HB GB TB TL VL nT W Wi c R dir e S ≠ bad) :
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

theorem step_bad {HB GB TB : ℕ → ℕ} {TL VL nT W Wi c R dir e S ND NO : ℕ} (hTV : TL ≠ VL)
    (hT : TL ≠ 255) (hV : VL ≠ 255) (hR : RecGood ND NO R) (hND : ND < 255) (hS : sD S = 255) :
    sD (stepL HB GB TB TL VL nT W Wi c R dir e S) = 255 := by
  by_contra hne
  have h : stepL HB GB TB TL VL nT W Wi c R dir e S ≠ bad := fun e => hne (by rw [e]; rfl)
  rcases (stepL_shape hTV hT hV h).sD with e | e <;> rw [e] at hS
  · have := hR.d
    omega
  · have := hR.dp
    omega

variable {G : Type*} [Group G] {LT LI TL VL NL : ℕ}

structure SCtx (HB GB TB : ℕ → ℕ) (LT LI TL VL NL NO nT W Wi : ℕ) (x : ℕ → G)
    (φ : Mg LT LI TL VL NL →* G) : Prop where
  hc : constsOK7 = true
  hL : LetOK LT LI TL VL NL
  hφ : ∀ c (h : c ∈ Nset TL VL NL),
    φ ⟨Lm LT LI TL VL NL c, Subgroup.subset_closure ⟨c, h, rfl⟩⟩ = x c
  hu : x VL = (x TL)⁻¹
  gj : ∀ j < NO, InM LT LI TL VL NL (gm HB GB j) ∧ InM LT LI TL VL NL (gi HB GB j) ∧
    mul7 (gm HB GB j) (gi HB GB j) = ONE7
  ts : ∀ e < nT, InM LT LI TL VL NL (tS TB e) ∧ InM LT LI TL VL NL (tP TB e) ∧
    (x TL)⁻¹ * rc φ (tS TB e) * x TL = rc φ (tP TB e)
  wW : InM LT LI TL VL NL W ∧ InM LT LI TL VL NL Wi ∧ mul7 W Wi = ONE7 ∧ x TL * x TL = rc φ W

@[expose] noncomputable def uv (φ : Mg LT LI TL VL NL →* G) (HB GB : ℕ → ℕ) (x : ℕ → G) (J : ℕ) : G :=
  if J = 0 then 1 else (rc φ (gm HB GB (J - 1)))⁻¹ * x TL * rc φ (gm HB GB (J - 1))

@[expose] def FM (φ : Mg LT LI TL VL NL →* G) (HB GB : ℕ → ℕ) (x w : ℕ → G) (R : ℕ) : Prop :=
  RelT (Ncl x TL VL NL) (w (rD R) * uv φ HB GB x (rJ R)) (w (rDp R) * rc φ (rPi R))

@[expose] noncomputable def rep (φ : Mg LT LI TL VL NL →* G) (w : ℕ → G) (S : ℕ) : G :=
  w (sD S) * rc φ (sPi S)

theorem InM_cancelL {A B : ℕ} (hA : InM LT LI TL VL NL A) (hAB : InM LT LI TL VL NL (mul7 A B))
    (hB : C7 B) (hc : constsOK7 = true) : InM LT LI TL VL NL B := by
  obtain ⟨cA, y, hy, ey⟩ := hA
  obtain ⟨-, z, hz, ez⟩ := hAB
  refine ⟨hB, y⁻¹ * z, Subgroup.mul_mem _ (Subgroup.inv_mem _ hy) hz, ?_⟩
  rw [Units.val_mul, ez, (mul7_sound hc cA hB).2, ← ey, ← mul_assoc, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, one_mul]

theorem InM_cancelR {A B : ℕ} (hB : InM LT LI TL VL NL B) (hAB : InM LT LI TL VL NL (mul7 A B))
    (hA : C7 A) (hc : constsOK7 = true) : InM LT LI TL VL NL A := by
  obtain ⟨cB, y, hy, ey⟩ := hB
  obtain ⟨-, z, hz, ez⟩ := hAB
  refine ⟨hA, z * y⁻¹, Subgroup.mul_mem _ hz (Subgroup.inv_mem _ hy), ?_⟩
  rw [Units.val_mul, ez, (mul7_sound hc hA cB).2, ← ey, mul_assoc, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, mul_one]

theorem rJ_sub {ND NO R : ℕ} (hR : RecGood ND NO R) (hj : 0 < rJ R) : rJ R - 1 < NO := by
  have := hR.j
  omega

section Steps

variable {HB GB TB : ℕ → ℕ} {NO nT W Wi ND : ℕ} {x : ℕ → G} {φ : Mg LT LI TL VL NL →* G}
  (h : SCtx HB GB TB LT LI TL VL NL NO nT W Wi x φ) {c R e S S' : ℕ}
  (hR : RecGood ND NO R) (hsh : Shape HB GB TB TL VL nT W Wi c R e S S')
include h hR hsh

theorem step_C7 (hS : C7 (sPi S)) : C7 (sPi S') := by
  have hc := h.hc
  have cP := valid7 hc hR.p
  have cF := valid7 hc hR.f
  rcases hsh with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, hj, he, -, -, rfl⟩ | ⟨-, hj, he, -, -, rfl⟩ |
    ⟨-, hj, he, -, -, rfl⟩ | ⟨-, hj, he, -, -, rfl⟩
  all_goals rw [sPi_mkSt (by first | exact rD_lt R | exact rDp_lt R)]
  · exact (mul7_sound hc cP hS).1
  · exact (mul7_sound hc cF hS).1
  · obtain ⟨-, gi1, -⟩ := h.gj _ (rJ_sub hR hj)
    exact (mul7_sound hc (mul7_sound hc cP gi1.1).1 (h.ts e he).2.1.1).1
  · obtain ⟨-, gi1, -⟩ := h.gj _ (rJ_sub hR hj)
    exact (mul7_sound hc (mul7_sound hc (mul7_sound hc cP gi1.1).1 (h.ts e he).2.1.1).1
      h.wW.2.1.1).1
  · obtain ⟨-, gi1, -⟩ := h.gj _ (rJ_sub hR hj)
    exact (mul7_sound hc (mul7_sound hc gi1.1 (h.ts e he).1.1).1 h.wW.1.1).1
  · obtain ⟨-, gi1, -⟩ := h.gj _ (rJ_sub hR hj)
    exact (mul7_sound hc gi1.1 (h.ts e he).1.1).1

theorem step_fwd (hRm : InM LT LI TL VL NL (rPi R)) (hS : InM LT LI TL VL NL (sPi S)) :
    InM LT LI TL VL NL (sPi S') := by
  have hc := h.hc
  have hF := InM_invR hc hRm (valid7 hc hR.f) hR.pf
  rcases hsh with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, hj, he, -, -, rfl⟩ | ⟨-, hj, he, -, -, rfl⟩ |
    ⟨-, hj, he, -, -, rfl⟩ | ⟨-, hj, he, -, -, rfl⟩
  all_goals rw [sPi_mkSt (by first | exact rD_lt R | exact rDp_lt R)]
  · exact InM_mul hc hRm hS
  · exact InM_mul hc hF hS
  · exact InM_mul hc (InM_mul hc hRm (h.gj _ (rJ_sub hR hj)).2.1) (h.ts e he).2.1
  · exact InM_mul hc (InM_mul hc (InM_mul hc hRm (h.gj _ (rJ_sub hR hj)).2.1) (h.ts e he).2.1)
      h.wW.2.1
  · exact InM_mul hc (InM_mul hc (h.gj _ (rJ_sub hR hj)).2.1 (h.ts e he).1) h.wW.1
  · exact InM_mul hc (h.gj _ (rJ_sub hR hj)).2.1 (h.ts e he).1

theorem step_back (hRm : InM LT LI TL VL NL (rPi R)) (hSc : C7 (sPi S))
    (hS' : InM LT LI TL VL NL (sPi S')) : InM LT LI TL VL NL (sPi S) := by
  have hc := h.hc
  have hF := InM_invR hc hRm (valid7 hc hR.f) hR.pf
  rcases hsh with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, hj, he, -, eT, -⟩ | ⟨-, hj, he, -, eT, -⟩ |
    ⟨-, hj, he, -, eT, -⟩ | ⟨-, hj, he, -, eT, -⟩
  · rw [sPi_mkSt (rDp_lt R)] at hS'
    exact InM_cancelL hRm hS' hSc hc
  · rw [sPi_mkSt (rD_lt R)] at hS'
    exact InM_cancelL hF hS' hSc hc
  · exact InM_cancelL (h.gj _ (rJ_sub hR hj)).1 (eT ▸ (h.ts e he).1) hSc hc
  · exact InM_cancelL (h.gj _ (rJ_sub hR hj)).1 (eT ▸ (h.ts e he).1) hSc hc
  · exact InM_cancelL (InM_mul hc (h.gj _ (rJ_sub hR hj)).1 hF) (eT ▸ (h.ts e he).2.1) hSc hc
  · exact InM_cancelL (InM_mul hc (h.gj _ (rJ_sub hR hj)).1 hF) (eT ▸ (h.ts e he).2.1) hSc hc

theorem step_own (hS : InM LT LI TL VL NL (sPi S)) (hS' : InM LT LI TL VL NL (sPi S')) :
    InM LT LI TL VL NL (rPi R) := by
  have hc := h.hc
  have cP := valid7 hc hR.p
  have cF := valid7 hc hR.f
  have ofF : InM LT LI TL VL NL (rFI R) → InM LT LI TL VL NL (rPi R) := fun hF =>
    InM_invL hc hF cP hR.pf
  rcases hsh with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, hj, he, -, -, rfl⟩ | ⟨-, hj, he, -, -, rfl⟩ |
    ⟨-, hj, he, -, eT, -⟩ | ⟨-, hj, he, -, eT, -⟩
  · rw [sPi_mkSt (rDp_lt R)] at hS'
    exact InM_cancelR hS hS' cP hc
  · rw [sPi_mkSt (rD_lt R)] at hS'
    exact ofF (InM_cancelR hS hS' cF hc)
  · rw [sPi_mkSt (rDp_lt R)] at hS'
    obtain ⟨-, gi1, -⟩ := h.gj _ (rJ_sub hR hj)
    exact InM_cancelR gi1 (InM_cancelR (h.ts e he).2.1 hS' (mul7_sound hc cP gi1.1).1 hc) cP hc
  · rw [sPi_mkSt (rDp_lt R)] at hS'
    obtain ⟨-, gi1, -⟩ := h.gj _ (rJ_sub hR hj)
    have c1 := (mul7_sound hc cP gi1.1).1
    have c2 := (mul7_sound hc c1 (h.ts e he).2.1.1).1
    exact InM_cancelR gi1 (InM_cancelR (h.ts e he).2.1 (InM_cancelR h.wW.2.1 hS' c2 hc) c1 hc) cP hc
  · obtain ⟨g1, -, -⟩ := h.gj _ (rJ_sub hR hj)
    have hGF := InM_cancelR hS (eT ▸ (h.ts e he).2.1) (mul7_sound hc g1.1 cF).1 hc
    exact ofF (InM_cancelL g1 hGF cF hc)
  · obtain ⟨g1, -, -⟩ := h.gj _ (rJ_sub hR hj)
    have hGF := InM_cancelR hS (eT ▸ (h.ts e he).2.1) (mul7_sound hc g1.1 cF).1 hc
    exact ofF (InM_cancelL g1 hGF cF hc)

theorem step_sem (w : ℕ → G) (hRm : InM LT LI TL VL NL (rPi R)) (hS : InM LT LI TL VL NL (sPi S)) :
    RelT (Ncl x TL VL NL) (rep φ w S * lvE x c) (rep φ w S') ↔ FM φ HB GB x w R := by
  have hc := h.hc
  have hF := InM_invR hc hRm (valid7 hc hR.f) hR.pf
  have rF := rc_invR hc φ hRm (valid7 hc hR.f) hR.pf
  have hT255 : TL ≠ 255 := by have := h.hL.tl; have := h.hL.nl; omega
  have hV255 : VL ≠ 255 := by have := h.hL.vl; have := h.hL.nl; omega
  unfold FM rep
  rcases hsh with ⟨rfl, hj, hD, rfl⟩ | ⟨rfl, hj, hD, rfl⟩ | ⟨rfl, hj, he, hD, eT, rfl⟩ |
    ⟨rfl, hj, he, hD, eT, rfl⟩ | ⟨rfl, hj, he, hD, eT, rfl⟩ | ⟨rfl, hj, he, hD, eT, rfl⟩
  · rw [sD_mkSt (rDp_lt R), sPi_mkSt (rDp_lt R), hD, rc_mul hc φ hRm hS, uv, ite_eq_left hj, lvE,
      ite_eq_left rfl]
    exact eps_fwd _ _ _ _
  · rw [sD_mkSt (rD_lt R), sPi_mkSt (rD_lt R), hD, rc_mul hc φ hF hS, rF, uv, ite_eq_left hj, lvE,
      ite_eq_left rfl]
    exact eps_bwd _ _ _ _
  all_goals
    obtain ⟨g1, gi1, ggi⟩ := h.gj _ (rJ_sub hR hj)
    obtain ⟨s1, p1, ps⟩ := h.ts e he
    have rGi := rc_invR hc φ g1 gi1.1 ggi
    rw [uv, ite_eq_right (by omega)]
  · rw [sD_mkSt (rDp_lt R), sPi_mkSt (rDp_lt R), hD, rc_mul hc φ (InM_mul hc hRm gi1) p1,
      rc_mul hc φ hRm gi1, rGi, lvE, ite_eq_right hT255]
    exact u_fwd _ _ _ _ _ _ _ _ (by rw [eT, rc_mul hc φ g1 hS]) ps
  · rw [sD_mkSt (rDp_lt R), sPi_mkSt (rDp_lt R), hD,
      rc_mul hc φ (InM_mul hc (InM_mul hc hRm gi1) p1) h.wW.2.1, rc_mul hc φ (InM_mul hc hRm gi1) p1,
      rc_mul hc φ hRm gi1, rGi, rc_invR hc φ h.wW.1 h.wW.2.1.1 h.wW.2.2.1, lvE, ite_eq_right hV255, h.hu]
    exact U_fwd _ _ _ _ _ _ _ _ _ (by rw [eT, rc_mul hc φ g1 hS]) ps h.wW.2.2.2
  · rw [sD_mkSt (rD_lt R), sPi_mkSt (rD_lt R), hD, rc_mul hc φ (InM_mul hc gi1 s1) h.wW.1,
      rc_mul hc φ gi1 s1, rGi, lvE, ite_eq_right hT255]
    exact u_bwd _ _ _ _ _ _ _ _ _ (by rw [eT, rc_mul hc φ (InM_mul hc g1 hF) hS, rc_mul hc φ g1 hF, rF])
      ps h.wW.2.2.2
  · rw [sD_mkSt (rD_lt R), sPi_mkSt (rD_lt R), hD, rc_mul hc φ gi1 s1, rGi, lvE, ite_eq_right hV255, h.hu]
    exact U_bwd _ _ _ _ _ _ _ _ (by rw [eT, rc_mul hc φ (InM_mul hc g1 hF) hS, rc_mul hc φ g1 hF, rF])
      ps

end Steps

end CFSG.Certificates.DS5

end
