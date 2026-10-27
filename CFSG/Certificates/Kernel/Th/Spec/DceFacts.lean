module

public import CFSG.Certificates.Kernel.Th.Spec.DceCore
public import CFSG.Certificates.Kernel.DceTwWalk
import Mathlib.Tactic.Group

public section

namespace CFSG.KC.Th.Spec.Dce

open CFSG.KC.Th CFSG.KC.Th.DceS CFSG.KC.Loop CFSG.Certificates.DceLoop
  CFSG.Certificates.DceWord CFSG.Certificates.DceTw

set_option exponentiation.threshold 700

structure RecGood (el : Bool) (ND NO R : ℕ) : Prop where
  d : rD R < ND
  dp : rDp R < ND
  j : rJ R ≤ NO
  pf : mul24 (rPi R) (rFI R) = ident24
  nn : el = true → mul24 (rN R) (rNI R) = ident24

theorem recOK_spec {el : Bool} {ND NO R : ℕ} (h : DceS.recOK ND NO el R = true) :
    RecGood el ND NO R := by
  unfold DceS.recOK at h
  obtain ⟨e1, r⟩ := andB_iff.1 h
  obtain ⟨e2, r⟩ := andB_iff.1 r
  obtain ⟨e3, r⟩ := andB_iff.1 r
  obtain ⟨e4, e5⟩ := andB_iff.1 r
  refine ⟨Nat.blt_eq.mp e1, Nat.blt_eq.mp e2, Nat.le_of_ble_eq_true e3,
    Nat.eq_of_beq_eq_true e4, fun hel => ?_⟩
  rw [hel] at e5
  exact Nat.eq_of_beq_eq_true e5

@[expose] def ShapeF (HB GB TB : ℕ → ℕ) (TL VL nT W Wi c R e S S' : ℕ) : Prop :=
  (c = 255 ∧ rJ R = 0 ∧ sD S = rD R ∧ S' = mkSt (rDp R) (mul24 (rPi R) (sPi S))) ∨
  (c = TL ∧ 0 < rJ R ∧ e < nT ∧ sD S = rD R ∧
    tSig HB TB e = mul24 (gm HB GB (rJ R - 1)) (sPi S) ∧
    S' = mkSt (rDp R) (mul24 (mul24 (rPi R) (gi HB GB (rJ R - 1))) (tPsi HB TB e))) ∨
  (c = VL ∧ 0 < rJ R ∧ e < nT ∧ sD S = rD R ∧
    tSig HB TB e = mul24 (gm HB GB (rJ R - 1)) (sPi S) ∧
    S' = mkSt (rDp R) (mul24 (mul24 (mul24 (rPi R) (gi HB GB (rJ R - 1))) (tPsi HB TB e)) Wi))

@[expose] def ShapeB (HB GB TB : ℕ → ℕ) (TL VL nT W Wi c R e S S' : ℕ) : Prop :=
  (c = 255 ∧ rJ R = 0 ∧ sD S = rDp R ∧ S' = mkSt (rD R) (mul24 (rFI R) (sPi S))) ∨
  (c = TL ∧ 0 < rJ R ∧ e < nT ∧ sD S = rDp R ∧
    tPsi HB TB e = mul24 (mul24 (gm HB GB (rJ R - 1)) (rFI R)) (sPi S) ∧
    S' = mkSt (rD R) (mul24 (mul24 (gi HB GB (rJ R - 1)) (tSig HB TB e)) W)) ∨
  (c = VL ∧ 0 < rJ R ∧ e < nT ∧ sD S = rDp R ∧
    tPsi HB TB e = mul24 (mul24 (gm HB GB (rJ R - 1)) (rFI R)) (sPi S) ∧
    S' = mkSt (rD R) (mul24 (gi HB GB (rJ R - 1)) (tSig HB TB e)))

@[expose] def ShapeD (HB GB TB : ℕ → ℕ) (TL VL nT W Wi c R dir e S S' : ℕ) : Prop :=
  (Nat.beq dir 1 = false ∧ ShapeF HB GB TB TL VL nT W Wi c R e S S') ∨
    (Nat.beq dir 1 = true ∧ ShapeB HB GB TB TL VL nT W Wi c R e S S')

theorem bad_ne {D p : ℕ} (hD : D < 255) : mkSt D p ≠ bad := fun h => by
  have := sD_mkSt (show D < 256 by omega) p
  rw [h, sD_bad] at this
  omega

theorem stepE_shape {R dir S : ℕ} (h : stepE R dir S ≠ bad) :
    rJ R = 0 ∧ ((Nat.beq dir 1 = false ∧ sD S = rD R ∧
        stepE R dir S = mkSt (rDp R) (mul24 (rPi R) (sPi S))) ∨
      (Nat.beq dir 1 = true ∧ sD S = rDp R ∧
        stepE R dir S = mkSt (rD R) (mul24 (rFI R) (sPi S)))) := by
  unfold stepE at h ⊢
  cases h1 : Nat.beq (rJ R) 0
  · rw [h1] at h
    exact absurd rfl h
  rw [h1] at h
  refine ⟨Nat.eq_of_beq_eq_true h1, ?_⟩
  dsimp only at h ⊢
  cases h2 : Nat.beq dir 1
  · rw [h2] at h
    dsimp only at h ⊢
    cases h3 : Nat.beq (sD S) (rD R)
    · rw [h3] at h
      exact absurd rfl h
    · exact Or.inl ⟨rfl, Nat.eq_of_beq_eq_true h3, rfl⟩
  · rw [h2] at h
    dsimp only at h ⊢
    cases h3 : Nat.beq (sD S) (rDp R)
    · rw [h3] at h
      exact absurd rfl h
    · exact Or.inr ⟨rfl, Nat.eq_of_beq_eq_true h3, rfl⟩

theorem stepU_shape {HB GB TB : ℕ → ℕ} {nT W Wi : ℕ} {isU : Bool} {R dir e S : ℕ}
    (h : stepU HB GB TB nT W Wi isU R dir e S ≠ bad) :
    0 < rJ R ∧ e < nT ∧
      ((Nat.beq dir 1 = false ∧ sD S = rD R ∧
          tSig HB TB e = mul24 (gm HB GB (rJ R - 1)) (sPi S) ∧
          stepU HB GB TB nT W Wi isU R dir e S = mkSt (rDp R) (Bool.rec (motive := fun _ => ℕ)
            (mul24 (mul24 (rPi R) (gi HB GB (rJ R - 1))) (tPsi HB TB e))
            (mul24 (mul24 (mul24 (rPi R) (gi HB GB (rJ R - 1))) (tPsi HB TB e)) Wi) isU)) ∨
        (Nat.beq dir 1 = true ∧ sD S = rDp R ∧
          tPsi HB TB e = mul24 (mul24 (gm HB GB (rJ R - 1)) (rFI R)) (sPi S) ∧
          stepU HB GB TB nT W Wi isU R dir e S = mkSt (rD R) (Bool.rec (motive := fun _ => ℕ)
            (mul24 (mul24 (gi HB GB (rJ R - 1)) (tSig HB TB e)) W)
            (mul24 (gi HB GB (rJ R - 1)) (tSig HB TB e)) isU))) := by
  unfold stepU at h ⊢
  beta_reduce at h ⊢
  cases h1 : andB (Nat.blt 0 (rJ R)) (Nat.blt e nT)
  · rw [h1] at h
    exact absurd rfl h
  obtain ⟨h1a, h1b⟩ := andB_iff.1 h1
  rw [h1] at h
  refine ⟨Nat.blt_eq.mp h1a, Nat.blt_eq.mp h1b, ?_⟩
  dsimp only at h ⊢
  cases h2 : Nat.beq dir 1
  · rw [h2] at h
    dsimp only at h ⊢
    cases h3 : andB (Nat.beq (sD S) (rD R))
        (Nat.beq (mat HB (lo20 (e40 TB e))) (mul24 (mat HB (lo20 (e40 GB (Nat.sub (rJ R) 1))))
          (sPi S)))
    · rw [h3] at h
      exact absurd rfl h
    · obtain ⟨h3a, h3b⟩ := andB_iff.1 h3
      exact Or.inl ⟨rfl, Nat.eq_of_beq_eq_true h3a, Nat.eq_of_beq_eq_true h3b, rfl⟩
  · rw [h2] at h
    dsimp only at h ⊢
    cases h3 : andB (Nat.beq (sD S) (rDp R))
        (Nat.beq (mat HB (hi20 (e40 TB e)))
          (mul24 (mul24 (mat HB (lo20 (e40 GB (Nat.sub (rJ R) 1)))) (rFI R)) (sPi S)))
    · rw [h3] at h
      exact absurd rfl h
    · obtain ⟨h3a, h3b⟩ := andB_iff.1 h3
      exact Or.inr ⟨rfl, Nat.eq_of_beq_eq_true h3a, Nat.eq_of_beq_eq_true h3b, rfl⟩

theorem stepL_shape {HB GB TB : ℕ → ℕ} {TL VL nT W Wi c R dir e S : ℕ} (hTV : TL ≠ VL)
    (hT : TL ≠ 255) (hV : VL ≠ 255) (h : stepL HB GB TB TL VL nT W Wi c R dir e S ≠ bad) :
    ShapeD HB GB TB TL VL nT W Wi c R dir e S (stepL HB GB TB TL VL nT W Wi c R dir e S) := by
  unfold stepL at h ⊢
  by_cases c255 : c = 255
  · subst c255
    rw [show Nat.beq 255 255 = true from rfl] at h ⊢
    dsimp only at h ⊢
    obtain ⟨hj, ⟨hd, h1⟩ | ⟨hd, h1⟩⟩ := stepE_shape h
    · exact Or.inl ⟨hd, Or.inl ⟨rfl, hj, h1⟩⟩
    · exact Or.inr ⟨hd, Or.inl ⟨rfl, hj, h1⟩⟩
  rw [Bool.eq_false_iff.2 fun e => c255 (Nat.eq_of_beq_eq_true e)] at h ⊢
  dsimp only at h ⊢
  by_cases cT : c = TL
  · subst cT
    rw [Nat.beq_refl] at h ⊢
    dsimp only at h ⊢
    obtain ⟨hj, he, ⟨hd, h1⟩ | ⟨hd, h1⟩⟩ := stepU_shape h
    · exact Or.inl ⟨hd, Or.inr (Or.inl ⟨rfl, hj, he, h1⟩)⟩
    · exact Or.inr ⟨hd, Or.inr (Or.inl ⟨rfl, hj, he, h1⟩)⟩
  rw [Bool.eq_false_iff.2 fun e => cT (Nat.eq_of_beq_eq_true e)] at h ⊢
  dsimp only at h ⊢
  by_cases cV : c = VL
  · subst cV
    rw [Nat.beq_refl] at h ⊢
    dsimp only at h ⊢
    obtain ⟨hj, he, ⟨hd, h1⟩ | ⟨hd, h1⟩⟩ := stepU_shape h
    · exact Or.inl ⟨hd, Or.inr (Or.inr ⟨rfl, hj, he, h1⟩)⟩
    · exact Or.inr ⟨hd, Or.inr (Or.inr ⟨rfl, hj, he, h1⟩)⟩
  rw [Bool.eq_false_iff.2 fun e => cV (Nat.eq_of_beq_eq_true e)] at h
  exact absurd rfl h

theorem ShapeD.sD {HB GB TB : ℕ → ℕ} {TL VL nT W Wi c R dir e S S' : ℕ}
    (h : ShapeD HB GB TB TL VL nT W Wi c R dir e S S') : sD S = rD R ∨ sD S = rDp R := by
  rcases h with ⟨-, ⟨-, -, h, -⟩ | ⟨-, -, -, h, -⟩ | ⟨-, -, -, h, -⟩⟩ |
    ⟨-, ⟨-, -, h, -⟩ | ⟨-, -, -, h, -⟩ | ⟨-, -, -, h, -⟩⟩
  · exact Or.inl h
  · exact Or.inl h
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inr h
  · exact Or.inr h

theorem step_bad {HB GB TB : ℕ → ℕ} {TL VL nT W Wi c R dir e S ND NO : ℕ} {el : Bool}
    (hTV : TL ≠ VL) (hT : TL ≠ 255) (hV : VL ≠ 255) (hR : RecGood el ND NO R) (hND : ND < 255)
    (hS : sD S = 255) : sD (stepL HB GB TB TL VL nT W Wi c R dir e S) = 255 := by
  by_contra hne
  have h : stepL HB GB TB TL VL nT W Wi c R dir e S ≠ bad := fun e => hne (by rw [e]; rfl)
  rcases (stepL_shape hTV hT hV h).sD with e | e <;> rw [e] at hS
  · have := hR.d
    omega
  · have := hR.dp
    omega

section StepGroup

variable {G : Type*} [Group G] (a b r p g σ τ u ω ν : G)

theorem ex_eps_fwd : a * p * 1 = ν * (b * (r * p)) ↔ a * 1 = ν * (b * r) := by
  have e1 : a * p * 1 = (a * 1) * p := by group
  have e2 : ν * (b * (r * p)) = (ν * (b * r)) * p := by group
  rw [e1, e2, mul_left_inj]

theorem ex_eps_bwd : b * p * 1 = ν⁻¹ * (a * (r⁻¹ * p)) ↔ a * 1 = ν * (b * r) := by
  have e1 : b * p * 1 = (b * 1) * p := by group
  have e2 : ν⁻¹ * (a * (r⁻¹ * p)) = (ν⁻¹ * (a * r⁻¹)) * p := by group
  rw [e1, e2, mul_left_inj]
  constructor
  · intro h
    calc a * 1 = ν * (ν⁻¹ * (a * r⁻¹)) * r := by group
      _ = ν * (b * 1) * r := by rw [← h]
      _ = ν * (b * r) := by group
  · intro h
    calc b * 1 = ν⁻¹ * (ν * (b * r)) * r⁻¹ := by group
      _ = ν⁻¹ * (a * 1) * r⁻¹ := by rw [← h]
      _ = ν⁻¹ * (a * r⁻¹) := by group

theorem ex_u_fwd (hp : σ = g * p) (hτ : u⁻¹ * σ * u = τ) :
    a * p * u = ν * (b * (r * g⁻¹ * τ)) ↔ a * (g⁻¹ * u * g) = ν * (b * r) := by
  have hp' : p = g⁻¹ * σ := by rw [hp]; group
  subst hp' hτ
  have e1 : a * (g⁻¹ * σ) * u = (a * (g⁻¹ * u * g)) * (g⁻¹ * (u⁻¹ * σ * u)) := by group
  have e2 : ν * (b * (r * g⁻¹ * (u⁻¹ * σ * u))) = (ν * (b * r)) * (g⁻¹ * (u⁻¹ * σ * u)) := by
    group
  rw [e1, e2, mul_left_inj]

theorem ex_U_fwd (hp : σ = g * p) (hτ : u⁻¹ * σ * u = τ) (hω : u * u = ω) :
    a * p * u⁻¹ = ν * (b * (r * g⁻¹ * τ * ω⁻¹)) ↔ a * (g⁻¹ * u * g) = ν * (b * r) := by
  have hp' : p = g⁻¹ * σ := by rw [hp]; group
  subst hp' hτ hω
  have e1 : a * (g⁻¹ * σ) * u⁻¹ =
      (a * (g⁻¹ * u * g)) * (g⁻¹ * (u⁻¹ * σ * u) * (u * u)⁻¹) := by group
  have e2 : ν * (b * (r * g⁻¹ * (u⁻¹ * σ * u) * (u * u)⁻¹)) =
      (ν * (b * r)) * (g⁻¹ * (u⁻¹ * σ * u) * (u * u)⁻¹) := by group
  rw [e1, e2, mul_left_inj]

theorem ex_u_bwd (hp : τ = g * r⁻¹ * p) (hτ : u⁻¹ * σ * u = τ) (hω : u * u = ω) :
    b * p * u = ν⁻¹ * (a * (g⁻¹ * σ * ω)) ↔ a * (g⁻¹ * u * g) = ν * (b * r) := by
  have hp' : p = r * g⁻¹ * τ := by rw [hp]; group
  subst hp' hτ hω
  have e1 : b * (r * g⁻¹ * (u⁻¹ * σ * u)) * u = (b * r * g⁻¹ * u⁻¹) * (σ * (u * u)) := by group
  have e2 : ν⁻¹ * (a * (g⁻¹ * σ * (u * u))) = (ν⁻¹ * (a * g⁻¹)) * (σ * (u * u)) := by group
  rw [e1, e2, mul_left_inj]
  constructor
  · intro h
    calc a * (g⁻¹ * u * g) = ν * (ν⁻¹ * (a * g⁻¹)) * u * g := by group
      _ = ν * (b * r * g⁻¹ * u⁻¹) * u * g := by rw [← h]
      _ = ν * (b * r) := by group
  · intro h
    calc b * r * g⁻¹ * u⁻¹ = ν⁻¹ * (ν * (b * r)) * g⁻¹ * u⁻¹ := by group
      _ = ν⁻¹ * (a * (g⁻¹ * u * g)) * g⁻¹ * u⁻¹ := by rw [← h]
      _ = ν⁻¹ * (a * g⁻¹) := by group

theorem ex_U_bwd (hp : τ = g * r⁻¹ * p) (hτ : u⁻¹ * σ * u = τ) :
    b * p * u⁻¹ = ν⁻¹ * (a * (g⁻¹ * σ)) ↔ a * (g⁻¹ * u * g) = ν * (b * r) := by
  have hp' : p = r * g⁻¹ * τ := by rw [hp]; group
  subst hp' hτ
  have e1 : b * (r * g⁻¹ * (u⁻¹ * σ * u)) * u⁻¹ = (b * r * g⁻¹ * u⁻¹) * σ := by group
  have e2 : ν⁻¹ * (a * (g⁻¹ * σ)) = (ν⁻¹ * (a * g⁻¹)) * σ := by group
  rw [e1, e2, mul_left_inj]
  constructor
  · intro h
    calc a * (g⁻¹ * u * g) = ν * (ν⁻¹ * (a * g⁻¹)) * u * g := by group
      _ = ν * (b * r * g⁻¹ * u⁻¹) * u * g := by rw [← h]
      _ = ν * (b * r) := by group
  · intro h
    calc b * r * g⁻¹ * u⁻¹ = ν⁻¹ * (ν * (b * r)) * g⁻¹ * u⁻¹ := by group
      _ = ν⁻¹ * (a * (g⁻¹ * u * g)) * g⁻¹ * u⁻¹ := by rw [← h]
      _ = ν⁻¹ * (a * g⁻¹) := by group

end StepGroup

theorem gm_lt (HB GB : ℕ → ℕ) (j : ℕ) : gm HB GB j < 2 ^ 576 := mat_lt _ _

theorem gi_lt (HB GB : ℕ → ℕ) (j : ℕ) : gi HB GB j < 2 ^ 576 := mat_lt _ _

theorem tSig_lt (HB TB : ℕ → ℕ) (e : ℕ) : tSig HB TB e < 2 ^ 576 := mat_lt _ _

theorem tPsi_lt (HB TB : ℕ → ℕ) (e : ℕ) : tPsi HB TB e < 2 ^ 576 := mat_lt _ _

section Steps

variable {M : Subgroup Mat24ˣ} {G : Type*} [Group G] {LT LC LI TL VL NL : ℕ} {x : ℕ → G}

structure SCtx (M : Subgroup Mat24ˣ) (φ : M →* G) (x : ℕ → G) (HB GB TB : ℕ → ℕ)
    (LT LC LI TL VL NL NO nT W Wi : ℕ) : Prop where
  hC : MCtx M LT LC LI TL VL NL x φ
  gj : ∀ j < NO, InM M (gm HB GB j) ∧ InM M (gi HB GB j) ∧
    mul24 (gm HB GB j) (gi HB GB j) = ident24
  ts : ∀ e < nT, InM M (tSig HB TB e) ∧ InM M (tPsi HB TB e) ∧
    (x TL)⁻¹ * rc φ (tSig HB TB e) * x TL = rc φ (tPsi HB TB e)
  wW : InM M W ∧ InM M (Nat.land Wi M576) ∧ mul24 W (Nat.land Wi M576) = ident24 ∧
    x TL * x TL = rc φ W

@[expose] noncomputable def uv (φ : M →* G) (HB GB : ℕ → ℕ) (u : G) (J : ℕ) : G :=
  if J = 0 then 1 else (rc φ (gm HB GB (J - 1)))⁻¹ * u * rc φ (gm HB GB (J - 1))

@[expose] def FMeq (φ : M →* G) (HB GB : ℕ → ℕ) (u : G) (w : ℕ → G) (R : ℕ) (ν : G) : Prop :=
  w (rD R) * uv φ HB GB u (rJ R) = ν * (w (rDp R) * rc φ (rPi R))

@[expose] noncomputable def rep (φ : M →* G) (w : ℕ → G) (S : ℕ) : G :=
  w (sD S) * rc φ (sPi S)

theorem rJ_sub {el : Bool} {ND NO R : ℕ} (hR : RecGood el ND NO R) (hj : 0 < rJ R) :
    rJ R - 1 < NO := by
  have := hR.j
  omega

section StepsCtx

variable {φ : M →* G} {HB GB TB : ℕ → ℕ} {NO nT W Wi ND : ℕ} {el : Bool}
  (h : SCtx M φ x HB GB TB LT LC LI TL VL NL NO nT W Wi) {c R e S S' : ℕ}
  (hR : RecGood el ND NO R)
include h hR

theorem step_fwd (hsh : ShapeF HB GB TB TL VL nT W Wi c R e S S') (hRm : InM M (rPi R))
    (hS : InM M (sPi S)) : InM M (sPi S') := by
  rcases hsh with ⟨-, -, -, rfl⟩ | ⟨-, hj, he, -, -, rfl⟩ | ⟨-, hj, he, -, -, rfl⟩
  · rw [sPi_mkSt (rDp_lt R)]
    exact InM_mul hRm hS
  · rw [sPi_mkSt (rDp_lt R)]
    exact InM_mul (InM_mul hRm (h.gj _ (rJ_sub hR hj)).2.1) (h.ts e he).2.1
  · rw [sPi_mkSt (rDp_lt R), ← mul24_land_right _ Wi]
    exact InM_mul (InM_mul (InM_mul hRm (h.gj _ (rJ_sub hR hj)).2.1) (h.ts e he).2.1) h.wW.2.1

theorem step_back (hsh : ShapeF HB GB TB TL VL nT W Wi c R e S S' ∨
      ShapeB HB GB TB TL VL nT W Wi c R e S S') (hRm : InM M (rPi R)) (hSc : sPi S < 2 ^ 576)
    (hS' : InM M (sPi S')) : InM M (sPi S) := by
  have hF := InM_invR hRm (rFI_lt R) hR.pf
  rcases hsh with (⟨-, -, -, rfl⟩ | ⟨-, hj, he, -, eT, -⟩ | ⟨-, hj, he, -, eT, -⟩) |
    (⟨-, -, -, rfl⟩ | ⟨-, hj, he, -, eT, -⟩ | ⟨-, hj, he, -, eT, -⟩)
  · rw [sPi_mkSt (rDp_lt R)] at hS'
    exact InM_cancelL hRm hS' hSc
  · exact InM_cancelL (h.gj _ (rJ_sub hR hj)).1 (eT ▸ (h.ts e he).1) hSc
  · exact InM_cancelL (h.gj _ (rJ_sub hR hj)).1 (eT ▸ (h.ts e he).1) hSc
  · rw [sPi_mkSt (rD_lt R)] at hS'
    exact InM_cancelL hF hS' hSc
  · exact InM_cancelL (InM_mul (h.gj _ (rJ_sub hR hj)).1 hF) (eT ▸ (h.ts e he).2.1) hSc
  · exact InM_cancelL (InM_mul (h.gj _ (rJ_sub hR hj)).1 hF) (eT ▸ (h.ts e he).2.1) hSc

theorem step_own (hsh : ShapeF HB GB TB TL VL nT W Wi c R e S S' ∨
      ShapeB HB GB TB TL VL nT W Wi c R e S S') (hS : InM M (sPi S)) (hS' : InM M (sPi S')) :
    InM M (rPi R) := by
  have ofF : InM M (rFI R) → InM M (rPi R) := fun hF => InM_invL hF (rPi_lt R) hR.pf
  rcases hsh with (⟨-, -, -, rfl⟩ | ⟨-, hj, he, -, -, rfl⟩ | ⟨-, hj, he, -, -, rfl⟩) |
    (⟨-, -, -, rfl⟩ | ⟨-, hj, he, -, eT, -⟩ | ⟨-, hj, he, -, eT, -⟩)
  · rw [sPi_mkSt (rDp_lt R)] at hS'
    exact InM_cancelR hS hS' (rPi_lt R)
  · rw [sPi_mkSt (rDp_lt R)] at hS'
    exact InM_cancelR (h.gj _ (rJ_sub hR hj)).2.1
      (InM_cancelR (h.ts e he).2.1 hS' (mul24_lt _ _)) (rPi_lt R)
  · rw [sPi_mkSt (rDp_lt R), ← mul24_land_right _ Wi] at hS'
    exact InM_cancelR (h.gj _ (rJ_sub hR hj)).2.1
      (InM_cancelR (h.ts e he).2.1 (InM_cancelR h.wW.2.1 hS' (mul24_lt _ _)) (mul24_lt _ _))
      (rPi_lt R)
  · rw [sPi_mkSt (rD_lt R)] at hS'
    exact ofF (InM_cancelR hS hS' (rFI_lt R))
  · have hGF := InM_cancelR hS (eT ▸ (h.ts e he).2.1) (mul24_lt _ _)
    exact ofF (InM_cancelL (h.gj _ (rJ_sub hR hj)).1 hGF (rFI_lt R))
  · have hGF := InM_cancelR hS (eT ▸ (h.ts e he).2.1) (mul24_lt _ _)
    exact ofF (InM_cancelL (h.gj _ (rJ_sub hR hj)).1 hGF (rFI_lt R))



theorem step_sem_fwd (w : ℕ → G) (ν : G)
    (hsh : ShapeF HB GB TB TL VL nT W Wi c R e S S') (hRm : InM M (rPi R)) (hS : InM M (sPi S)) :
    rep φ w S * lvE x c = ν * rep φ w S' ↔ FMeq φ HB GB (x TL) w R ν := by
  have hT255 : TL ≠ 255 := by have := h.hC.hL.tl; have := h.hC.hL.nl; omega
  have hV255 : VL ≠ 255 := by have := h.hC.hL.vl; have := h.hC.hL.nl; omega
  unfold FMeq rep
  rcases hsh with ⟨rfl, hj, hD, rfl⟩ | ⟨rfl, hj, he, hD, eT, rfl⟩ | ⟨rfl, hj, he, hD, eT, rfl⟩
  · rw [sD_mkSt (rDp_lt R), sPi_mkSt (rDp_lt R), hD, rc_mul φ hRm hS, uv, ite_eq_left hj, lvE,
      ite_eq_left rfl]
    exact ex_eps_fwd _ _ _ _ _
  all_goals
    obtain ⟨g1, gi1, ggi⟩ := h.gj _ (rJ_sub hR hj)
    obtain ⟨s1, p1, ps⟩ := h.ts e he
    have rGi := rc_invR φ g1 (gi_lt _ _ _) ggi
    rw [uv, ite_eq_right (by omega)]
  · rw [sD_mkSt (rDp_lt R), sPi_mkSt (rDp_lt R), hD, rc_mul φ (InM_mul hRm gi1) p1,
      rc_mul φ hRm gi1, rGi, lvE, ite_eq_right hT255]
    exact ex_u_fwd _ _ _ _ _ _ _ _ _ (by rw [eT, rc_mul φ g1 hS]) ps
  · rw [sD_mkSt (rDp_lt R), sPi_mkSt (rDp_lt R), hD, ← mul24_land_right _ Wi,
      rc_mul φ (InM_mul (InM_mul hRm gi1) p1) h.wW.2.1, rc_mul φ (InM_mul hRm gi1) p1,
      rc_mul φ hRm gi1, rGi, rc_invR φ h.wW.1 (land_M576_lt Wi) h.wW.2.2.1, lvE,
      ite_eq_right hV255, h.hC.hu]
    exact ex_U_fwd _ _ _ _ _ _ _ _ _ _ (by rw [eT, rc_mul φ g1 hS]) ps h.wW.2.2.2

theorem step_sem_bwd (w : ℕ → G) (ν : G)
    (hsh : ShapeB HB GB TB TL VL nT W Wi c R e S S') (hRm : InM M (rPi R)) (hS : InM M (sPi S)) :
    rep φ w S * lvE x c = ν⁻¹ * rep φ w S' ↔ FMeq φ HB GB (x TL) w R ν := by
  have hT255 : TL ≠ 255 := by have := h.hC.hL.tl; have := h.hC.hL.nl; omega
  have hV255 : VL ≠ 255 := by have := h.hC.hL.vl; have := h.hC.hL.nl; omega
  have hF := InM_invR hRm (rFI_lt R) hR.pf
  have rF := rc_invR φ hRm (rFI_lt R) hR.pf
  unfold FMeq rep
  rcases hsh with ⟨rfl, hj, hD, rfl⟩ | ⟨rfl, hj, he, hD, eT, rfl⟩ | ⟨rfl, hj, he, hD, eT, rfl⟩
  · rw [sD_mkSt (rD_lt R), sPi_mkSt (rD_lt R), hD, rc_mul φ hF hS, rF, uv, ite_eq_left hj, lvE,
      ite_eq_left rfl]
    exact ex_eps_bwd _ _ _ _ _
  all_goals
    obtain ⟨g1, gi1, ggi⟩ := h.gj _ (rJ_sub hR hj)
    obtain ⟨s1, p1, ps⟩ := h.ts e he
    have rGi := rc_invR φ g1 (gi_lt _ _ _) ggi
    rw [uv, ite_eq_right (by omega)]
  · rw [sD_mkSt (rD_lt R), sPi_mkSt (rD_lt R), hD, rc_mul φ (InM_mul gi1 s1) h.wW.1,
      rc_mul φ gi1 s1, rGi, lvE, ite_eq_right hT255]
    exact ex_u_bwd _ _ _ _ _ _ _ _ _ _
      (by rw [eT, rc_mul φ (InM_mul g1 hF) hS, rc_mul φ g1 hF, rF]) ps h.wW.2.2.2
  · rw [sD_mkSt (rD_lt R), sPi_mkSt (rD_lt R), hD, rc_mul φ gi1 s1, rGi, lvE,
      ite_eq_right hV255, h.hC.hu]
    exact ex_U_bwd _ _ _ _ _ _ _ _ _
      (by rw [eT, rc_mul φ (InM_mul g1 hF) hS, rc_mul φ g1 hF, rF]) ps

end StepsCtx

end Steps

section Chain

variable {G : Type*} [Group G]

@[expose] def pr (f : ℕ → G) (k : ℕ) : G := ((List.range k).map f).prod

theorem pr_succ (f : ℕ → G) (k : ℕ) : pr f (k + 1) = pr f k * f k := by
  simp only [pr, List.range_succ, List.map_append, List.prod_append, List.map_singleton,
    List.prod_singleton]

theorem pr_zero (f : ℕ → G) : pr f 0 = 1 := rfl

theorem chain_exact (a ℓ ν : ℕ → G) {n qo : ℕ} (hqo : qo < n)
    (hs : ∀ q < n, q ≠ qo → a q * ℓ q = ν q * a (q + 1))
    (hv : pr ℓ n = 1) (hcl : a n = a 0) :
    a qo * ℓ qo = ((pr ν qo)⁻¹ * (pr (fun j => ν (qo + 1 + j)) (n - qo - 1))⁻¹) * a (qo + 1) := by
  have c1 : ∀ q ≤ qo, a q = (pr ν q)⁻¹ * a 0 * pr ℓ q := by
    intro q
    induction q with
    | zero =>
      intro _
      simp [pr_zero]
    | succ q ih =>
      intro hq
      have h1 := hs q (by omega) (by omega)
      have h2 : a (q + 1) = (ν q)⁻¹ * (a q * ℓ q) := by
        rw [h1]; group
      rw [h2, ih (by omega), pr_succ, pr_succ]
      group
  have c2 : ∀ d, qo + 1 + d ≤ n →
      a (qo + 1 + d) = (pr (fun j => ν (qo + 1 + j)) d)⁻¹ * a (qo + 1) *
        pr (fun j => ℓ (qo + 1 + j)) d := by
    intro d
    induction d with
    | zero =>
      intro _
      simp [pr_zero]
    | succ d ih =>
      intro hd
      have h1 := hs (qo + 1 + d) (by omega) (by omega)
      have h2 : a (qo + 1 + d + 1) = (ν (qo + 1 + d))⁻¹ * (a (qo + 1 + d) * ℓ (qo + 1 + d)) := by
        rw [h1]; group
      rw [← Nat.add_assoc, h2, ih (by omega), pr_succ, pr_succ]
      group
  have hsplit : ∀ m k, pr ℓ (k + m) = pr ℓ k * pr (fun j => ℓ (k + j)) m := by
    intro m k
    induction m with
    | zero => simp [pr_zero]
    | succ m ih =>
      rw [← Nat.add_assoc, pr_succ, pr_succ, ih]
      group
  have f2 := c2 (n - (qo + 1)) (by omega)
  rw [show qo + 1 + (n - (qo + 1)) = n by omega, hcl] at f2
  have hP : pr ℓ n = pr ℓ (qo + 1) * pr (fun j => ℓ (qo + 1 + j)) (n - (qo + 1)) := by
    rw [← hsplit (n - (qo + 1)) (qo + 1), show qo + 1 + (n - (qo + 1)) = n by omega]
  rw [hv] at hP
  have hL : pr (fun j => ℓ (qo + 1 + j)) (n - (qo + 1)) = (pr ℓ (qo + 1))⁻¹ :=
    eq_inv_of_mul_eq_one_right hP.symm
  rw [hL] at f2
  have f3 : a (qo + 1) = pr (fun j => ν (qo + 1 + j)) (n - (qo + 1)) * a 0 * pr ℓ (qo + 1) := by
    have : a 0 * pr ℓ (qo + 1) = (pr (fun j => ν (qo + 1 + j)) (n - (qo + 1)))⁻¹ * a (qo + 1) := by
      calc a 0 * pr ℓ (qo + 1)
          = ((pr (fun j => ν (qo + 1 + j)) (n - (qo + 1)))⁻¹ * a (qo + 1) * (pr ℓ (qo + 1))⁻¹) *
              pr ℓ (qo + 1) := by rw [← f2]
        _ = _ := by group
    calc a (qo + 1) = pr (fun j => ν (qo + 1 + j)) (n - (qo + 1)) * (a 0 * pr ℓ (qo + 1)) := by
          rw [this]; group
      _ = _ := by group
  rw [show n - qo - 1 = n - (qo + 1) by omega, f3, c1 qo le_rfl, pr_succ]
  group

end Chain

@[expose] noncomputable def mR (R dir : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (rN R) (rNI R) (Nat.beq dir 1)

@[expose] def WStep (FB HB GB TB : ℕ → ℕ) (sh wd LT TL VL NL nT W Wi : ℕ) (el : Bool)
    (i Ri ft fd Wd q S A S' A' : ℕ) : Prop :=
  (isN TL VL NL (byte Wd q) = true ∧
      S' = mkSt (sD S) (mul24 (sPi S) (let24 LT (byte Wd q))) ∧ A' = A) ∨
    (isN TL VL NL (byte Wd q) = false ∧ ∃ R dir e,
      S' = stepL HB GB TB TL VL nT W Wi (byte Wd q) R dir e S ∧
      A' = Bool.rec (motive := fun _ => ℕ) A (mul24 A (mR R dir)) el ∧
      (q = ft ∧ R = Ri ∧ dir = fd ∨ q ≠ ft ∧ ∃ h < i, R = rec FB sh wd h))

@[expose] noncomputable def wBody (FB HB GB TB : ℕ → ℕ) (sh wd LT TL VL NL nT W Wi : ℕ) (el : Bool)
    (i Ri ft fd Wd n k : ℕ) (ih : ℕ → ℕ → ℕ → ℕ) (J S A : ℕ) : ℕ :=
  (fun q => (fun c =>
      Bool.rec (motive := fun _ => ℕ)
        (ih J (mkSt (sD S) (mul24 (sPi S) (let24 LT c))) A)
        ((fun own => (fun h => (fun R dir =>
            Bool.rec (motive := fun _ => ℕ) bad
              (strictN (stepL HB GB TB TL VL nT W Wi c R dir
                  (Bool.rec (motive := fun _ => ℕ) (bits J 21 17) (bits J 0 17) own) S)
                (fun S2 => ih (Nat.shiftRight J (posBits TL VL c own)) S2
                  (Bool.rec (motive := fun _ => ℕ) A
                    (mul24 A (Bool.rec (motive := fun _ => ℕ) (rN R) (rNI R) (Nat.beq dir 1))) el)))
              (orB own (Nat.blt h i)))
            (Bool.rec (motive := fun _ => ℕ) (rec FB sh wd h) Ri own)
            (Bool.rec (motive := fun _ => ℕ) (Nat.land J 1) fd own))
          (bits J 1 20))
         (Nat.beq q ft))
        (notB (isN TL VL NL c)))
      (byte Wd q)) (Nat.sub n (Nat.succ k))

theorem walkGo_spec (FB HB GB TB : ℕ → ℕ) (sh wd LT TL VL NL nT W Wi : ℕ) (el : Bool)
    (i Ri ft fd Wd n : ℕ) : ∀ k, k ≤ n →
    ∀ J S A, walkGo FB HB GB TB sh wd LT TL VL NL nT W Wi el i Ri ft fd Wd n k J S A = bad ∨
      ∃ Ss As : ℕ → ℕ, Ss (n - k) = S ∧ As (n - k) = A ∧
        walkGo FB HB GB TB sh wd LT TL VL NL nT W Wi el i Ri ft fd Wd n k J S A =
          Nat.lor (Ss n) (Nat.shiftLeft (As n) 584) ∧
        ∀ q, n - k ≤ q → q < n →
          WStep FB HB GB TB sh wd LT TL VL NL nT W Wi el i Ri ft fd Wd q (Ss q) (As q)
            (Ss (q + 1)) (As (q + 1))
  | 0, _, J, S, A => Or.inr ⟨fun _ => S, fun _ => A, rfl, rfl, rfl,
      fun q h1 h2 => absurd h2 (by omega)⟩
  | k + 1, hk, J, S, A => by
    have ih := walkGo_spec FB HB GB TB sh wd LT TL VL NL nT W Wi el i Ri ft fd Wd n k (by omega)
    have ext : ∀ S' A', WStep FB HB GB TB sh wd LT TL VL NL nT W Wi el i Ri ft fd Wd (n - (k + 1))
        S A S' A' → ∀ J',
        (walkGo FB HB GB TB sh wd LT TL VL NL nT W Wi el i Ri ft fd Wd n k J' S' A' = bad ∨
          ∃ Ss As : ℕ → ℕ, Ss (n - k) = S' ∧ As (n - k) = A' ∧
            walkGo FB HB GB TB sh wd LT TL VL NL nT W Wi el i Ri ft fd Wd n k J' S' A' =
              Nat.lor (Ss n) (Nat.shiftLeft (As n) 584) ∧
            ∀ q, n - k ≤ q → q < n →
              WStep FB HB GB TB sh wd LT TL VL NL nT W Wi el i Ri ft fd Wd q (Ss q) (As q)
                (Ss (q + 1)) (As (q + 1))) →
        walkGo FB HB GB TB sh wd LT TL VL NL nT W Wi el i Ri ft fd Wd n k J' S' A' = bad ∨
          ∃ Ss As : ℕ → ℕ, Ss (n - (k + 1)) = S ∧ As (n - (k + 1)) = A ∧
            walkGo FB HB GB TB sh wd LT TL VL NL nT W Wi el i Ri ft fd Wd n k J' S' A' =
              Nat.lor (Ss n) (Nat.shiftLeft (As n) 584) ∧
            ∀ q, n - (k + 1) ≤ q → q < n →
              WStep FB HB GB TB sh wd LT TL VL NL nT W Wi el i Ri ft fd Wd q (Ss q) (As q)
                (Ss (q + 1)) (As (q + 1)) := by
      intro S' A' hst J' h
      rcases h with h | ⟨Ss, As, h0, h0A, hn, hs⟩
      · exact Or.inl h
      refine Or.inr ⟨fun q => if q = n - (k + 1) then S else Ss q,
        fun q => if q = n - (k + 1) then A else As q, by simp, by simp, ?_, ?_⟩
      · simp only []
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        exact hn
      · intro q hq1 hq2
        simp only []
        rcases Nat.eq_or_lt_of_le hq1 with rfl | hq1
        · rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_right (by omega), ite_eq_right (by omega),
            show n - (k + 1) + 1 = n - k by omega, h0, h0A]
          exact hst
        · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
            ite_eq_right (by omega)]
          exact hs q (by omega) hq2
    change wBody FB HB GB TB sh wd LT TL VL NL nT W Wi el i Ri ft fd Wd n k
      (walkGo FB HB GB TB sh wd LT TL VL NL nT W Wi el i Ri ft fd Wd n k) J S A = bad ∨
        ∃ Ss As : ℕ → ℕ, Ss (n - (k + 1)) = S ∧ As (n - (k + 1)) = A ∧
          wBody FB HB GB TB sh wd LT TL VL NL nT W Wi el i Ri ft fd Wd n k
            (walkGo FB HB GB TB sh wd LT TL VL NL nT W Wi el i Ri ft fd Wd n k) J S A =
            Nat.lor (Ss n) (Nat.shiftLeft (As n) 584) ∧
          ∀ q, n - (k + 1) ≤ q → q < n →
            WStep FB HB GB TB sh wd LT TL VL NL nT W Wi el i Ri ft fd Wd q (Ss q) (As q)
              (Ss (q + 1)) (As (q + 1))
    unfold wBody
    simp only []
    have eq : Nat.sub n (Nat.succ k) = n - (k + 1) := rfl
    rw [eq]
    cases hN : isN TL VL NL (byte Wd (n - (k + 1)))
    ·
      dsimp only [notB]
      cases hc : orB (Nat.beq (n - (k + 1)) ft) (Nat.blt (bits J 1 20) i)
      · exact Or.inl rfl
      · dsimp only
        rw [strictN_eq]
        apply ext _ _ _ _ (ih _ _ _)
        refine Or.inr ⟨hN, _, _, _, rfl, ?_, ?_⟩
        · cases el <;> rfl
        cases ho : Nat.beq (n - (k + 1)) ft
        · rw [ho] at hc
          change Nat.blt (bits J 1 20) i = true at hc
          rw [Nat.blt_eq] at hc
          exact Or.inr ⟨Nat.ne_of_beq_eq_false ho, _, hc, rfl⟩
        · exact Or.inl ⟨Nat.eq_of_beq_eq_true ho, rfl, rfl⟩
    ·
      dsimp only [notB]
      exact ext _ _ (Or.inl ⟨hN, rfl, rfl⟩) _ (ih _ _ _)

theorem lor_shl_eq {a b k : ℕ} (ha : a < 2 ^ k) :
    Nat.lor a (Nat.shiftLeft b k) = a + b * 2 ^ k := by
  change a ||| b <<< k = _
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq, Nat.add_comm]

theorem lor_dec {a b a' b' : ℕ} (ha : a < 2 ^ 584) (ha' : a' < 2 ^ 584)
    (h : Nat.lor a (Nat.shiftLeft b 584) = Nat.lor a' (Nat.shiftLeft b' 584)) :
    a = a' ∧ b = b' := by
  rw [lor_shl_eq ha, lor_shl_eq ha'] at h
  have h1 : a = a' := by
    have := congrArg (· % 2 ^ 584) h
    simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at this
    exact this
  subst h1
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos 584) (Nat.add_left_cancel h)⟩

theorem lor_ge {a b : ℕ} (ha : a < 2 ^ 584) (hb : 0 < b) :
    2 ^ 584 ≤ Nat.lor a (Nat.shiftLeft b 584) := by
  rw [lor_shl_eq ha]
  exact Nat.le_trans (Nat.le_mul_of_pos_left _ hb) (Nat.le_add_left _ _)

theorem mkSt_lt {D p : ℕ} (hD : D < 256) (hp : p < 2 ^ 576) : mkSt D p < 2 ^ 584 := by
  change D ||| p <<< 8 < 2 ^ 584
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  have hD' : D < 2 ^ 8 := by simpa using hD
  have h1 : D.testBit i = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hD' (Nat.pow_le_pow_right (by omega) (by omega)))
  have h2 : p.testBit (i - 8) = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hp (Nat.pow_le_pow_right (by omega) (by omega)))
  rw [h1, h2]
  simp

theorem bad_lt : bad < 2 ^ 584 := by
  change 255 < 2 ^ 584
  norm_num

theorem stepL_lt {HB GB TB : ℕ → ℕ} {TL VL nT W Wi c R dir e S : ℕ} (hTV : TL ≠ VL)
    (hT : TL ≠ 255) (hV : VL ≠ 255) :
    stepL HB GB TB TL VL nT W Wi c R dir e S < 2 ^ 584 := by
  by_cases hne : stepL HB GB TB TL VL nT W Wi c R dir e S = bad
  · rw [hne]; exact bad_lt
  have hsh := stepL_shape hTV hT hV hne
  rcases hsh with ⟨-, ⟨-, -, -, h⟩ | ⟨-, -, -, -, -, h⟩ | ⟨-, -, -, -, -, h⟩⟩ |
    ⟨-, ⟨-, -, -, h⟩ | ⟨-, -, -, -, -, h⟩ | ⟨-, -, -, -, -, h⟩⟩ <;>
    rw [h] <;> exact mkSt_lt (by first | exact rD_lt R | exact rDp_lt R) (mul24_lt _ _)

theorem walkOK_spec {FB HB GB TB WD : ℕ → ℕ} {sh wd LT TL VL NL ND nH nT nW W Wi i Jf R : ℕ}
    {el : Bool}
    (h : walkOK FB HB GB TB WD sh wd LT TL VL NL ND nH nT nW W Wi el i Jf R = true) :
    ∃ ww < nW, ∃ D0 < ND, ∃ a < nH, ∃ b < nH, ∃ ft fd J,
      ft < bits (WD ww) 2 10 ∧ isN TL VL NL (byte (Nat.shiftRight (WD ww) 12) ft) = false ∧
      walkGo FB HB GB TB sh wd LT TL VL NL nT W Wi el i R ft fd (Nat.shiftRight (WD ww) 12)
        (bits (WD ww) 2 10) (bits (WD ww) 2 10) J (mkSt D0 (mul24 (mat HB a) (mat HB b)))
          ident24 =
        Nat.lor (mkSt D0 (mul24 (mat HB a) (mat HB b))) (Nat.shiftLeft ident24 584) := by
  unfold walkOK at h
  beta_reduce at h
  obtain ⟨e1, r⟩ := andB_iff.1 h
  obtain ⟨e2, r⟩ := andB_iff.1 r
  obtain ⟨e3, r⟩ := andB_iff.1 r
  obtain ⟨e4, r⟩ := andB_iff.1 r
  obtain ⟨e5, r⟩ := andB_iff.1 r
  obtain ⟨e6, e7⟩ := andB_iff.1 r
  exact ⟨_, Nat.blt_eq.mp e1, _, Nat.blt_eq.mp e2, _, Nat.blt_eq.mp e3, _, Nat.blt_eq.mp e4,
    _, _, _, Nat.blt_eq.mp e5, notB_iff.1 e6, Nat.eq_of_beq_eq_true e7⟩

section Facts

variable {M : Subgroup Mat24ˣ} {G : Type*} [Group G] {LT LC LI TL VL NL : ℕ} {x : ℕ → G}
  {φ : M →* G} {HB GB TB FB WD : ℕ → ℕ} {NO nT W Wi ND sh wd nH nW : ℕ}

@[expose] def FM (N : Subgroup G) (el : Bool) (φ : M →* G) (HB GB : ℕ → ℕ) (u : G) (w : ℕ → G)
    (R : ℕ) : Prop :=
  ∃ ν ∈ N, (el = true → ν = rc φ (rN R)) ∧ FMeq φ HB GB u w R ν

@[expose] def FOK (N : Subgroup G) (el : Bool) (φ : M →* G) (HB GB : ℕ → ℕ) (u : G) (w : ℕ → G)
    (ND NO R : ℕ) : Prop :=
  RecGood el ND NO R ∧ InM M (rPi R) ∧ (el = true → InM M (rN R)) ∧ FM N el φ HB GB u w R

theorem mR_inM {el : Bool} {ND NO R : ℕ} (hR : RecGood el ND NO R) (hel : el = true)
    (hn : InM M (rN R)) (dir : ℕ) : InM M (mR R dir) := by
  unfold mR
  cases Nat.beq dir 1
  · exact hn
  · exact InM_invR hn (rNI_lt R) (hR.nn hel)



theorem WStep_lt {FB HB GB TB : ℕ → ℕ} {sh wd LT TL VL NL nT W Wi : ℕ} {el : Bool}
    {i Ri ft fd Wd q S A S' A' : ℕ} (hTV : TL ≠ VL) (hT : TL ≠ 255) (hV : VL ≠ 255)
    (h : WStep FB HB GB TB sh wd LT TL VL NL nT W Wi el i Ri ft fd Wd q S A S' A') :
    S' < 2 ^ 584 := by
  rcases h with ⟨-, rfl, -⟩ | ⟨-, R, dir, e, rfl, -, -⟩
  · exact mkSt_lt (sD_lt _) (mul24_lt _ _)
  · exact stepL_lt hTV hT hV


theorem pr_congr {G : Type*} [Group G] {f g : ℕ → G} :
    ∀ k, (∀ q < k, f q = g q) → pr f k = pr g k
  | 0, _ => rfl
  | k + 1, h => by
    rw [pr_succ, pr_succ, pr_congr k fun q hq => h q (by omega), h k (by omega)]

theorem pr_add {G : Type*} [Group G] (f : ℕ → G) (k m : ℕ) :
    pr f (k + m) = pr f k * pr (fun j => f (k + j)) m := by
  induction m with
  | zero => simp [pr_zero]
  | succ m ih =>
    rw [← Nat.add_assoc, pr_succ, pr_succ, ih]
    group

theorem pr_mem {G : Type*} [Group G] {N : Subgroup G} {f : ℕ → G} :
    ∀ k, (∀ q < k, f q ∈ N) → pr f k ∈ N
  | 0, _ => N.one_mem
  | k + 1, h => by
    rw [pr_succ]
    exact N.mul_mem (pr_mem k fun q hq => h q (by omega)) (h k (by omega))

theorem shapeD_lt {HB GB TB : ℕ → ℕ} {TL VL nT W Wi c R dir e S S' : ℕ}
    (h : ShapeD HB GB TB TL VL nT W Wi c R dir e S S') : sPi S' < 2 ^ 576 := by
  rcases h with ⟨-, ⟨-, -, -, h⟩ | ⟨-, -, -, -, -, h⟩ | ⟨-, -, -, -, -, h⟩⟩ |
    ⟨-, ⟨-, -, -, h⟩ | ⟨-, -, -, -, -, h⟩ | ⟨-, -, -, -, -, h⟩⟩ <;>
    rw [h] <;> rw [sPi_mkSt (by first | exact rD_lt R | exact rDp_lt R)] <;> exact mul24_lt _ _

section StepsB

variable {M : Subgroup Mat24ˣ} {G : Type*} [Group G] {LT LC LI TL VL NL : ℕ} {x : ℕ → G}
  {φ : M →* G} {HB GB TB : ℕ → ℕ} {NO nT W Wi ND : ℕ} {el : Bool}
  (h : SCtx M φ x HB GB TB LT LC LI TL VL NL NO nT W Wi) {c R e S S' : ℕ}
  (hR : RecGood el ND NO R)
include h hR

theorem step_fwdB (hsh : ShapeB HB GB TB TL VL nT W Wi c R e S S') (hRm : InM M (rPi R))
    (hS : InM M (sPi S)) : InM M (sPi S') := by
  have hF := InM_invR hRm (rFI_lt R) hR.pf
  rcases hsh with ⟨-, -, -, rfl⟩ | ⟨-, hj, he, -, -, rfl⟩ | ⟨-, hj, he, -, -, rfl⟩
  · rw [sPi_mkSt (rD_lt R)]
    exact InM_mul hF hS
  · rw [sPi_mkSt (rD_lt R)]
    exact InM_mul (InM_mul (h.gj _ (rJ_sub hR hj)).2.1 (h.ts e he).1) h.wW.1
  · rw [sPi_mkSt (rD_lt R)]
    exact InM_mul (h.gj _ (rJ_sub hR hj)).2.1 (h.ts e he).1

end StepsB


theorem mR_lt (R dir : ℕ) : mR R dir < 2 ^ 576 := by
  unfold mR
  cases Nat.beq dir 1
  · exact rN_lt R
  · exact rNI_lt R

section WalkMean

variable (h : SCtx M φ x HB GB TB LT LC LI TL VL NL NO nT W Wi)
include h

theorem walk_mean {N : Subgroup G} (hND : ND < 255)
    (hhdr : ∀ k < nH, InM M (mat HB k))
    (hwords : ∀ ww < nW, wv (lvE x) (Nat.shiftRight (WD ww) 12) (bits (WD ww) 2 10) = 1)
    {el : Bool} (w : ℕ → G) {i Jf : ℕ}
    (hprev : ∀ k < i, FOK N el φ HB GB (x TL) w ND NO (rec FB sh wd k))
    (hrec : DceS.recOK ND NO el (rec FB sh wd i) = true)
    (hW : walkOK FB HB GB TB WD sh wd LT TL VL NL ND nH nT nW W Wi el i Jf (rec FB sh wd i) =
      true) :
    FOK N el φ HB GB (x TL) w ND NO (rec FB sh wd i) := by
  classical
  have hC := h.hC
  have hL := hC.hL
  have hTV := hL.tv
  have hT255 : TL ≠ 255 := by have := hL.tl; have := hL.nl; omega
  have hV255 : VL ≠ 255 := by have := hL.vl; have := hL.nl; omega
  have hRi : RecGood el ND NO (rec FB sh wd i) := recOK_spec hrec
  obtain ⟨wd0, hwd, D0, hD0, a0, ha0, b0, hb0, ft, fd, J, hft, hnN, hgo⟩ := walkOK_spec hW
  have hval := hwords wd0 hwd
  generalize Nat.shiftRight (WD wd0) 12 = Wd at hnN hgo hval
  generalize bits (WD wd0) 2 10 = n at hft hgo hval
  have hX : InM M (mul24 (mat HB a0) (mat HB b0)) := InM_mul (hhdr a0 ha0) (hhdr b0 hb0)
  have hXlt := mul24_lt (mat HB a0) (mat HB b0)
  generalize mul24 (mat HB a0) (mat HB b0) = X at hX hXlt hgo
  have hD0' : D0 < 256 := by omega
  have hS0lt : mkSt D0 X < 2 ^ 584 := mkSt_lt hD0' hXlt
  rcases walkGo_spec FB HB GB TB sh wd LT TL VL NL nT W Wi el i (rec FB sh wd i) ft fd Wd n n
      le_rfl J (mkSt D0 X) ident24 with hbad | ⟨Ss, As, h0S, h0A, hend, hst⟩
  · exfalso
    have h1 := lor_ge (b := ident24) hS0lt (Nat.pos_of_ne_zero ident24_ne_zero)
    rw [← hgo, hbad] at h1
    exact absurd h1 (Nat.not_le.2 bad_lt)
  rw [Nat.sub_self] at h0S h0A
  have hSnlt : Ss n < 2 ^ 584 := by
    have e : n = (n - 1) + 1 := by omega
    rw [e]
    exact WStep_lt hTV hT255 hV255 (hst (n - 1) (by omega) (by omega))
  obtain ⟨hSn, hAn⟩ := lor_dec hSnlt hS0lt (hend.symm.trans hgo)
  have hrecs : ∀ q < n, isN TL VL NL (byte Wd q) = false → ∃ R dir e,
      Ss (q + 1) = stepL HB GB TB TL VL nT W Wi (byte Wd q) R dir e (Ss q) ∧
      As (q + 1) = Bool.rec (motive := fun _ => ℕ) (As q) (mul24 (As q) (mR R dir)) el ∧
      RecGood el ND NO R ∧
      ((q = ft ∧ R = rec FB sh wd i ∧ dir = fd) ∨
        (q ≠ ft ∧ InM M (rPi R) ∧ (el = true → InM M (rN R)) ∧
          FM N el φ HB GB (x TL) w R)) := by
    intro q hq hN
    rcases hst q (by omega) hq with ⟨hN', -⟩ | ⟨-, R, dir, e, he, hA, hR⟩
    · rw [hN] at hN'
      exact absurd hN' Bool.false_ne_true
    rcases hR with ⟨hq1, rfl, hd⟩ | ⟨hq1, k, hk, rfl⟩
    · exact ⟨_, dir, e, he, hA, hRi, Or.inl ⟨hq1, rfl, hd⟩⟩
    · obtain ⟨g1, g2, g3, g4⟩ := hprev k hk
      exact ⟨_, dir, e, he, hA, g1, Or.inr ⟨hq1, g2, g3, g4⟩⟩
  have hNstep : ∀ q < n, isN TL VL NL (byte Wd q) = true →
      Ss (q + 1) = mkSt (sD (Ss q)) (mul24 (sPi (Ss q)) (let24 LT (byte Wd q))) ∧
        As (q + 1) = As q := by
    intro q hq hN
    rcases hst q (by omega) hq with ⟨-, he, ha⟩ | ⟨hN', -⟩
    · exact ⟨he, ha⟩
    · rw [hN] at hN'
      exact absurd hN' (by decide)
  have hbadstep : ∀ q < n, sD (Ss q) = 255 → sD (Ss (q + 1)) = 255 := by
    intro q hq hS
    cases hN : isN TL VL NL (byte Wd q)
    · obtain ⟨R, dir, e, he, -, hR, -⟩ := hrecs q hq hN
      rw [he]
      exact step_bad hTV hT255 hV255 hR hND hS
    · rw [(hNstep q hq hN).1, sD_mkSt (sD_lt _)]
      exact hS
  have hgood : ∀ q ≤ n, sD (Ss q) ≠ 255 := by
    intro q hq hS
    have key : ∀ d, q + d ≤ n → sD (Ss (q + d)) = 255 := by
      intro d
      induction d with
      | zero => exact fun _ => hS
      | succ d ih => exact fun hd => hbadstep (q + d) (by omega) (ih (by omega))
    have := key (n - q) (by omega)
    rw [show q + (n - q) = n by omega, hSn, sD_mkSt hD0'] at this
    omega
  have hshape : ∀ q < n, isN TL VL NL (byte Wd q) = false → ∃ R dir e,
      ShapeD HB GB TB TL VL nT W Wi (byte Wd q) R dir e (Ss q) (Ss (q + 1)) ∧
      As (q + 1) = Bool.rec (motive := fun _ => ℕ) (As q) (mul24 (As q) (mR R dir)) el ∧
      RecGood el ND NO R ∧
      ((q = ft ∧ R = rec FB sh wd i ∧ dir = fd) ∨
        (q ≠ ft ∧ InM M (rPi R) ∧ (el = true → InM M (rN R)) ∧
          FM N el φ HB GB (x TL) w R)) := by
    intro q hq hN
    obtain ⟨R, dir, e, he, hA, hR, hk⟩ := hrecs q hq hN
    have hne : stepL HB GB TB TL VL nT W Wi (byte Wd q) R dir e (Ss q) ≠ bad := fun e' =>
      hgood (q + 1) (by omega) (by rw [he, e']; rfl)
    refine ⟨R, dir, e, ?_, hA, hR, hk⟩
    rw [he]
    exact stepL_shape hTV hT255 hV255 hne
  have hSlt : ∀ q ≤ n, sPi (Ss q) < 2 ^ 576 := by
    intro q
    induction q with
    | zero =>
      intro _
      rw [h0S, sPi_mkSt hD0']
      exact hXlt
    | succ q ih =>
      intro hq
      cases hN : isN TL VL NL (byte Wd q)
      · obtain ⟨R, dir, e, hsh, -⟩ := hshape q (by omega) hN
        exact shapeD_lt hsh
      · rw [(hNstep q (by omega) hN).1, sPi_mkSt (sD_lt _)]
        exact mul24_lt _ _
  have hNlt : ∀ q, isN TL VL NL (byte Wd q) = true → byte Wd q ≠ 255 := fun q hN e => by
    have := (isN_iff.1 hN).1
    have := hL.nl
    omega
  have hAlt : el = true → ∀ q ≤ n, As q < 2 ^ 576 := by
    intro hel q
    induction q with
    | zero =>
      intro _
      rw [h0A]
      exact ident24_lt
    | succ q ih =>
      intro hq
      cases hN : isN TL VL NL (byte Wd q)
      · obtain ⟨R, dir, e, -, hA, -⟩ := hshape q (by omega) hN
        rw [hA, hel]
        exact mul24_lt _ _
      · rw [(hNstep q (by omega) hN).2]
        exact ih (by omega)
  have hFw : ∀ q ≤ ft, InM M (sPi (Ss q)) ∧ (el = true → InM M (As q)) := by
    intro q
    induction q with
    | zero =>
      intro _
      rw [h0S, h0A, sPi_mkSt hD0']
      exact ⟨hX, fun _ => InM_one⟩
    | succ q ih =>
      intro hq
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      cases hN : isN TL VL NL (byte Wd q)
      · obtain ⟨R, dir, e, hsh, hA, hR, hk⟩ := hshape q (by omega) hN
        rcases hk with ⟨hq', -⟩ | ⟨-, hRm, hRn, -⟩
        · omega
        refine ⟨?_, fun hel => ?_⟩
        · rcases hsh with ⟨-, hF⟩ | ⟨-, hB⟩
          · exact step_fwd h hR hF hRm ih1
          · exact step_fwdB h hR hB hRm ih1
        · rw [hA, hel]
          exact InM_mul (ih2 hel) (mR_inM hR hel (hRn hel) dir)
      · obtain ⟨he, ha⟩ := hNstep q (by omega) hN
        rw [he, sPi_mkSt (sD_lt _), ha]
        exact ⟨InM_mul ih1 (hC.inM_letter hN), ih2⟩
  have hBw : ∀ d, ft + 1 + d ≤ n →
      InM M (sPi (Ss (n - d))) ∧ (el = true → InM M (As (n - d))) := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [Nat.sub_zero, hSn, hAn, sPi_mkSt hD0']
      exact ⟨hX, fun _ => InM_one⟩
    | succ d ih =>
      intro hd
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have hq : n - (d + 1) + 1 = n - d := by omega
      rw [← hq] at ih1 ih2
      cases hN : isN TL VL NL (byte Wd (n - (d + 1)))
      · obtain ⟨R, dir, e, hsh, hA, hR, hk⟩ := hshape (n - (d + 1)) (by omega) hN
        rcases hk with ⟨hq', -⟩ | ⟨-, hRm, hRn, -⟩
        · omega
        refine ⟨step_back h hR (hsh.elim (fun h' => Or.inl h'.2) (fun h' => Or.inr h'.2)) hRm
          (hSlt _ (by omega)) ih1, fun hel => ?_⟩
        have h2 := ih2 hel
        rw [hA, hel] at h2
        exact InM_cancelR (mR_inM hR hel (hRn hel) dir) h2 (hAlt hel _ (by omega))
      · obtain ⟨he, ha⟩ := hNstep (n - (d + 1)) (by omega) hN
        rw [he, sPi_mkSt (sD_lt _)] at ih1
        refine ⟨InM_cancelR (hC.inM_letter hN) ih1 (hSlt _ (by omega)), fun hel => ?_⟩
        have h2 := ih2 hel
        rw [ha] at h2
        exact h2
  have hall : ∀ q ≤ n, InM M (sPi (Ss q)) ∧ (el = true → InM M (As q)) := by
    intro q hq
    by_cases h1 : q ≤ ft
    · exact hFw q h1
    · have := hBw (n - q) (by omega)
      rwa [Nat.sub_sub_self hq] at this
  obtain ⟨R0, dir0, e0, hsh0, hA0, hR0, hk0⟩ := hshape ft hft hnN
  rcases hk0 with ⟨-, hR0i, -⟩ | ⟨hne, -⟩
  swap
  · exact absurd rfl hne
  subst hR0i
  have hsh0' := hsh0.elim (fun h' => Or.inl h'.2) (fun h' => Or.inr h'.2)
  have hRP := step_own h hR0 hsh0' (hall ft (by omega)).1 (hall (ft + 1) (by omega)).1
  have hRN : el = true → InM M (rN (rec FB sh wd i)) := by
    intro hel
    have hm : InM M (mR (rec FB sh wd i) dir0) := by
      have h1 := (hall (ft + 1) (by omega)).2 hel
      rw [hA0, hel] at h1
      exact InM_cancelL ((hall ft (by omega)).2 hel) h1 (mR_lt _ _)
    unfold mR at hm
    cases hb : Nat.beq dir0 1
    · rw [hb] at hm
      exact hm
    · rw [hb] at hm
      exact InM_invL hm (rN_lt _) (hRi.nn hel)
  have hrel : ∀ q < n, q ≠ ft → ∃ ν ∈ N,
      rep φ w (Ss q) * lvE x (byte Wd q) = ν * rep φ w (Ss (q + 1)) ∧
      (el = true → (rc φ (As q))⁻¹ * rc φ (As (q + 1)) = ν) := by
    intro q hq hqf
    obtain ⟨hp, ha⟩ := hall q (by omega)
    cases hN : isN TL VL NL (byte Wd q)
    · obtain ⟨R, dir, e, hsh, hA, hR, hk⟩ := hshape q hq hN
      rcases hk with ⟨hq', -⟩ | ⟨-, hRm, hRn, ν, hνN, hνel, hFM⟩
      · exact absurd hq' hqf
      rcases hsh with ⟨hd, hF⟩ | ⟨hd, hB⟩
      · refine ⟨ν, hνN, (step_sem_fwd h hR w ν hF hRm hp).2 hFM, fun hel => ?_⟩
        have hmR : mR R dir = rN R := by
          unfold mR
          rw [hd]
        rw [hA, hel]
        dsimp only
        rw [hmR, rc_mul φ (ha hel) (hRn hel), hνel hel]
        group
      · refine ⟨ν⁻¹, N.inv_mem hνN, (step_sem_bwd h hR w ν hB hRm hp).2 hFM, fun hel => ?_⟩
        have hmR : mR R dir = rNI R := by
          unfold mR
          rw [hd]
        rw [hA, hel]
        dsimp only
        rw [hmR, rc_mul φ (ha hel) (InM_invR (hRn hel) (rNI_lt R) (hR.nn hel)),
          rc_invR φ (hRn hel) (rNI_lt R) (hR.nn hel), hνel hel]
        group
    · obtain ⟨he, ha'⟩ := hNstep q hq hN
      refine ⟨1, N.one_mem, ?_, fun hel => ?_⟩
      · unfold rep
        rw [he, sD_mkSt (sD_lt _), sPi_mkSt (sD_lt _), rc_mul φ hp (hC.inM_letter hN),
          hC.rc_letter hN, lvE, ite_eq_right (hNlt q hN)]
        group
      · rw [ha']
        group
  choose! ν' hν'N hν'rel hν'A using hrel
  have hv : pr (fun q => lvE x (byte Wd q)) n = 1 := hval
  have hcl : rep φ w (Ss n) = rep φ w (Ss 0) := by rw [hSn, h0S]
  have hch := chain_exact (fun q => rep φ w (Ss q)) (fun q => lvE x (byte Wd q)) ν' hft
    (fun q hq hne => (hν'rel q hq hne)) hv hcl
  set νo := (pr ν' ft)⁻¹ * (pr (fun j => ν' (ft + 1 + j)) (n - ft - 1))⁻¹ with hνo
  have hνoN : νo ∈ N :=
    N.mul_mem (N.inv_mem (pr_mem ft fun q hq => hν'N q (by omega) (by omega)))
      (N.inv_mem (pr_mem _ fun j hj => hν'N _ (by omega) (by omega)))
  have hρ : el = true → rc φ (mR (rec FB sh wd i) dir0) = νo := by
    intro hel
    have hAm := fun q (hq : q ≤ n) => (hall q hq).2 hel
    have hprρ : ∀ k ≤ n, pr (fun q => (rc φ (As q))⁻¹ * rc φ (As (q + 1))) k =
        (rc φ (As 0))⁻¹ * rc φ (As k) := by
      intro k
      induction k with
      | zero =>
        intro _
        simp [pr_zero]
      | succ k ih =>
        intro hk
        rw [pr_succ, ih (by omega)]
        group
    have h1 : pr (fun q => (rc φ (As q))⁻¹ * rc φ (As (q + 1))) n = 1 := by
      rw [hprρ n le_rfl, hAn, h0A, rc_one φ]
      group
    have hsplit : pr (fun q => (rc φ (As q))⁻¹ * rc φ (As (q + 1))) n =
        pr (fun q => (rc φ (As q))⁻¹ * rc φ (As (q + 1))) ft *
          ((rc φ (As ft))⁻¹ * rc φ (As (ft + 1))) *
          pr (fun j => (rc φ (As (ft + 1 + j)))⁻¹ * rc φ (As (ft + 1 + j + 1)))
            (n - ft - 1) := by
      have e : n = (ft + 1) + (n - ft - 1) := by omega
      conv_lhs => rw [e]
      rw [pr_add, pr_succ]
    have c1 : pr (fun q => (rc φ (As q))⁻¹ * rc φ (As (q + 1))) ft = pr ν' ft :=
      pr_congr ft fun q hq => hν'A q (by omega) (by omega) hel
    have c2 : pr (fun j => (rc φ (As (ft + 1 + j)))⁻¹ * rc φ (As (ft + 1 + j + 1)))
        (n - ft - 1) = pr (fun j => ν' (ft + 1 + j)) (n - ft - 1) :=
      pr_congr _ fun j hj => hν'A _ (by omega) (by omega) hel
    have hρft : (rc φ (As ft))⁻¹ * rc φ (As (ft + 1)) = rc φ (mR (rec FB sh wd i) dir0) := by
      rw [hA0, hel]
      dsimp only
      rw [rc_mul φ (hAm ft (by omega)) (mR_inM hRi hel (hRN hel) dir0)]
      group
    rw [hsplit, c1, c2, hρft] at h1
    calc rc φ (mR (rec FB sh wd i) dir0)
        = (pr ν' ft)⁻¹ * (pr ν' ft * rc φ (mR (rec FB sh wd i) dir0) *
            pr (fun j => ν' (ft + 1 + j)) (n - ft - 1)) *
          (pr (fun j => ν' (ft + 1 + j)) (n - ft - 1))⁻¹ := by group
      _ = νo := by rw [h1, hνo]; group
  have hFM : FM N el φ HB GB (x TL) w (rec FB sh wd i) := by
    rcases hsh0 with ⟨hd, hF⟩ | ⟨hd, hB⟩
    · refine ⟨νo, hνoN, fun hel => ?_,
        (step_sem_fwd h hR0 w νo hF hRP (hall ft (by omega)).1).1 hch⟩
      have hmR : mR (rec FB sh wd i) dir0 = rN (rec FB sh wd i) := by
        unfold mR
        rw [hd]
      rw [← hρ hel, hmR]
    · refine ⟨νo⁻¹, N.inv_mem hνoN, fun hel => ?_,
        (step_sem_bwd h hR0 w νo⁻¹ hB hRP (hall ft (by omega)).1).1 (by rw [inv_inv]; exact hch)⟩
      have hmR : mR (rec FB sh wd i) dir0 = rNI (rec FB sh wd i) := by
        unfold mR
        rw [hd]
      rw [← hρ hel, hmR, rc_invR φ (hRN hel) (rNI_lt _) (hRi.nn hel), inv_inv]
  exact ⟨hRi, hRP, hRN, hFM⟩

end WalkMean


theorem treeOK_spec {HB GB : ℕ → ℕ} {el : Bool} {nx R : ℕ} (h : DceS.treeOK HB GB el nx R = true) :
    0 < rJ R ∧ rDp R = nx ∧ rD R < nx ∧ rPi R = ident24 ∧ (el = true → rN R = ident24) ∧
      (nx = 1 → gm HB GB (rJ R - 1) = ident24) := by
  unfold DceS.treeOK at h
  obtain ⟨e1, r⟩ := andB_iff.1 h
  obtain ⟨e2, r⟩ := andB_iff.1 r
  obtain ⟨e3, r⟩ := andB_iff.1 r
  obtain ⟨e4, r⟩ := andB_iff.1 r
  obtain ⟨e5, e6⟩ := andB_iff.1 r
  refine ⟨Nat.blt_eq.mp e1, Nat.eq_of_beq_eq_true e2, Nat.blt_eq.mp e3, Nat.eq_of_beq_eq_true e4,
    fun hel => ?_, fun hnx => ?_⟩
  · rw [hel] at e5
    exact Nat.eq_of_beq_eq_true e5
  · have : Nat.beq nx 1 = true := by rw [hnx]; exact Nat.beq_refl 1
    rw [this] at e6
    exact Nat.eq_of_beq_eq_true e6

theorem axiomOK_spec {HB : ℕ → ℕ} {nH Jf R : ℕ} {el : Bool}
    (h : DceS.axiomOK HB nH el Jf R = true) :
    rD R = 0 ∧ rJ R = 0 ∧ rDp R = 0 ∧ ∃ a < nH, ∃ b < nH, rPi R = mul24 (mat HB a) (mat HB b) ∧
      (el = true → rN R = rFI R) := by
  unfold DceS.axiomOK at h
  beta_reduce at h
  obtain ⟨e1, r⟩ := andB_iff.1 h
  obtain ⟨e2, r⟩ := andB_iff.1 r
  obtain ⟨e3, r⟩ := andB_iff.1 r
  obtain ⟨e4, r⟩ := andB_iff.1 r
  obtain ⟨e5, r⟩ := andB_iff.1 r
  obtain ⟨e6, e7⟩ := andB_iff.1 r
  refine ⟨Nat.eq_of_beq_eq_true e1, Nat.eq_of_beq_eq_true e2, Nat.eq_of_beq_eq_true e3, _,
    Nat.blt_eq.mp e4, _, Nat.blt_eq.mp e5, Nat.eq_of_beq_eq_true e6, fun hel => ?_⟩
  rw [hel] at e7
  exact Nat.eq_of_beq_eq_true e7

theorem runFacts_eq (FB HB GB TB WD : ℕ → ℕ)
    (sh wd LT TL VL NL ND NO nH nT nW W Wi : ℕ) (el : Bool) (Cs : List ℕ) (S : ℕ) :
    DceS.runFacts FB HB GB TB WD sh wd LT TL VL NL ND NO nH nT nW W Wi el Cs S =
      factsG (factG (DceS.recOK ND NO el) (DceS.treeOK HB GB el) (DceS.axiomOK HB nH el)
        (fun i Jf R => walkOK FB HB GB TB WD sh wd LT TL VL NL ND nH nT nW W Wi el i Jf R)
        (rec FB sh wd)) Cs S := rfl

abbrev FChk (HB GB TB FB WD : ℕ → ℕ) (LT TL VL NL ND NO nH nT nW W Wi sh wd : ℕ) (el : Bool) :=
  FactOK (DceS.recOK ND NO el) (DceS.treeOK HB GB el) (DceS.axiomOK HB nH el)
    (fun i Jf R => walkOK FB HB GB TB WD sh wd LT TL VL NL ND nH nT nW W Wi el i Jf R)
    (rec FB sh wd)

section FactsMean

variable {M : Subgroup Mat24ˣ} {G : Type*} [Group G] {LT LC LI TL VL NL : ℕ} {x : ℕ → G}
  {φ : M →* G} {HB GB TB FB WD : ℕ → ℕ} {NO nT W Wi ND sh wd nH nW NF : ℕ} {el : Bool}

theorem exists_w {nxf : ℕ → ℕ}
    (hf : ∀ i < NF, FChk HB GB TB FB WD LT TL VL NL ND NO nH nT nW W Wi sh wd el i (nxf i)
      (nxf (i + 1))) :
    ∃ w : ℕ → G, w 0 = 1 ∧ ∀ i < NF, nxf (i + 1) = nxf i + 1 →
      w (rDp (rec FB sh wd i)) = w (rD (rec FB sh wd i)) *
        uv φ HB GB (x TL) (rJ (rec FB sh wd i)) := by
  have htree : ∀ i < NF, nxf (i + 1) = nxf i + 1 →
      DceS.treeOK HB GB el (nxf i) (rec FB sh wd i) = true := by
    intro i hi ht
    rcases (hf i hi).2 with ⟨-, h⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · exact h
    · omega
    · omega
  refine exists_tree NF (fun i => nxf (i + 1) = nxf i + 1) (fun i => rD (rec FB sh wd i))
    (fun i => rDp (rec FB sh wd i)) (fun i => uv φ HB GB (x TL) (rJ (rec FB sh wd i)))
    (fun i hi ht => ?_) (fun i hi i' hi' ht ht' e => ?_)
  · obtain ⟨-, h2, h3, -⟩ := treeOK_spec (htree i hi ht)
    show rD (rec FB sh wd i) < rDp (rec FB sh wd i)
    omega
  · exact tree_unique hf rDp (fun nx R h => (treeOK_spec h).2.1) hi hi' ht ht' e

variable (h : SCtx M φ x HB GB TB LT LC LI TL VL NL NO nT W Wi)
include h

theorem facts_mean {N : Subgroup G} (hφN : ∀ m, φ m ∈ N) (hND : ND < 255)
    (hhdr : ∀ k < nH, InM M (mat HB k))
    (hwords : ∀ ww < nW, wv (lvE x) (Nat.shiftRight (WD ww) 12) (bits (WD ww) 2 10) = 1)
    {nxf : ℕ → ℕ}
    (hf : ∀ i < NF, FChk HB GB TB FB WD LT TL VL NL ND NO nH nT nW W Wi sh wd el i (nxf i)
      (nxf (i + 1)))
    (w : ℕ → G) (hw0 : w 0 = 1) (hwt : ∀ i < NF, nxf (i + 1) = nxf i + 1 →
      w (rDp (rec FB sh wd i)) = w (rD (rec FB sh wd i)) *
        uv φ HB GB (x TL) (rJ (rec FB sh wd i))) :
    ∀ i < NF, FOK N el φ HB GB (x TL) w ND NO (rec FB sh wd i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    obtain ⟨hrk, hk⟩ := hf i hi
    have hR := recOK_spec hrk
    rcases hk with ⟨ht, htk⟩ | ⟨-, Jf, hax⟩ | ⟨-, Jf, hwk⟩
    · obtain ⟨-, -, -, hP, hNn, -⟩ := treeOK_spec htk
      refine ⟨hR, hP ▸ InM_one, fun hel => (hNn hel) ▸ InM_one,
        1, N.one_mem, fun hel => by rw [hNn hel, rc_one φ], ?_⟩
      unfold FMeq
      rw [hP, rc_one φ, mul_one, one_mul, hwt i hi ht]
    · obtain ⟨e1, e2, e3, a, ha, b, hb, hP, hNeq⟩ := axiomOK_spec hax
      have hm : InM M (rPi (rec FB sh wd i)) := hP ▸ InM_mul (hhdr a ha) (hhdr b hb)
      refine ⟨hR, hm, fun hel => ?_, rc φ (rFI (rec FB sh wd i)), hφN _, fun hel => ?_, ?_⟩
      · rw [hNeq hel]
        exact InM_invR hm (rFI_lt _) hR.pf
      · rw [hNeq hel]
      · unfold FMeq
        rw [e1, e2, e3, uv, ite_eq_left rfl, hw0, one_mul, one_mul,
          rc_invR φ hm (rFI_lt _) hR.pf]
        group
    · exact walk_mean h hND hhdr hwords w (fun k hk => ih k hk (by omega)) hrk hwk

end FactsMean

end Facts

end CFSG.KC.Th.Spec.Dce

end
