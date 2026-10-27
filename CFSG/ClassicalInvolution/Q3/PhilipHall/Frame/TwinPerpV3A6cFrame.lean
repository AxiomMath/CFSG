module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6cFrameRel

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

variable {n : ℕ}


local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

section Calc

variable {Y : Type} [Group Y]

structure FrameCalc (t a₁ a₂ a₃ a₄ : Y) : Prop where
  tt : t * t = 1
  s₁ : a₁ * a₁ = t
  s₂ : a₂ * a₂ = t
  s₃ : a₃ * a₃ = t
  s₄ : a₄ * a₄ = t
  t₁ : t * a₁ = a₁ * t
  t₂ : t * a₂ = a₂ * t
  t₃ : t * a₃ = a₃ * t
  t₄ : t * a₄ = a₄ * t
  c₁₂ : a₁ * a₂ = a₂ * a₁
  c₁₃ : a₁ * a₃ = a₃ * a₁
  c₁₄ : a₁ * a₄ = a₄ * a₁
  c₂₃ : a₂ * a₃ = a₃ * a₂
  c₂₄ : a₂ * a₄ = a₄ * a₂
  c₃₄ : a₃ * a₄ = a₄ * a₃

theorem conj_eq_of_comm {k x : Y} (h : k * x = x * k) : k * x * k⁻¹ = x := by
  rw [h]
  group

theorem two_trans_alg {u t τ j r s : Y} (M : Subgroup Y) (hjM : j ∈ M) (hrM : r ∈ M) (hsM : s ∈ M)
    (ht2 : t * t = 1) (hτ2 : τ * τ = 1) (htτ : t * τ = τ * t)
    (hju : j * u * j⁻¹ = u * t) (hjt : j * t * j⁻¹ = t) (hjτ : j * τ * j⁻¹ = τ * t)
    (hru : r * u * r⁻¹ = u) (hrt : r * t * r⁻¹ = t) (hrτ : r * τ * r⁻¹ = τ * t)
    (hst : s * t * s⁻¹ = τ * t) (hsu : s * u * s⁻¹ = u ∨ s * u * s⁻¹ = u * τ) :
    ∀ x, (x = u * t ∨ x = u * τ ∨ x = u * τ * t) →
      ∃ g ∈ M, g * u * g⁻¹ = u ∧ g * (u * t) * g⁻¹ = x := by
  have cm : ∀ (g p q : Y), g * (p * q) * g⁻¹ = (g * p * g⁻¹) * (g * q * g⁻¹) := fun g p q => by group
  have cc : ∀ (a b p : Y), (a * b) * p * (a * b)⁻¹ = a * (b * p * b⁻¹) * a⁻¹ := fun a b p => by group
  have ci : ∀ (b p q : Y), b * p * b⁻¹ = q → b⁻¹ * q * b = p := fun b p q h => by rw [← h]; group
  have tt' : ∀ y : Y, y * t * t = y := fun y => by rw [mul_assoc, ht2, mul_one]
  have jP1 : j * (u * t) * j⁻¹ = u := by rw [cm, hju, hjt, tt']
  have jP2 : j * (u * τ) * j⁻¹ = u * τ := by
    rw [cm, hju, hjτ]
    calc u * t * (τ * t) = u * (t * τ) * t := by group
      _ = u * (τ * t) * t := by rw [htτ]
      _ = u * τ := by rw [mul_assoc, tt']
  have jiP1 : j⁻¹ * (u * t) * j = u := ci j u (u * t) hju
  have jiP0 : j⁻¹ * u * j = u * t := ci j (u * t) u jP1
  have rP2 : r * (u * τ) * r⁻¹ = u * τ * t := by rw [cm, hru, hrτ, mul_assoc]
  have rP3 : r * (u * τ * t) * r⁻¹ = u * τ := by
    rw [cm, cm, hru, hrτ, hrt]
    calc u * (τ * t) * t = u * τ * (t * t) := by group
      _ = u * τ := by rw [ht2, mul_one]
  rcases hsu with hs0 | hs1
  · have sP1 : s * (u * t) * s⁻¹ = u * τ * t := by rw [cm, hs0, hst, mul_assoc]
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨1, M.one_mem, by group, by group⟩
    · exact ⟨r * s, M.mul_mem hrM hsM, by rw [cc, hs0, hru], by rw [cc, sP1, rP3]⟩
    · exact ⟨s, hsM, hs0, sP1⟩
  · have sP1 : s * (u * t) * s⁻¹ = u * t := by
      rw [cm, hs1, hst]
      calc u * τ * (τ * t) = u * (τ * τ) * t := by group
        _ = u * t := by rw [hτ2, mul_one]
    have g1u : (j * s * j⁻¹) * u * (j * s * j⁻¹)⁻¹ = u := by
      calc (j * s * j⁻¹) * u * (j * s * j⁻¹)⁻¹ = j * (s * (j⁻¹ * u * j) * s⁻¹) * j⁻¹ := by group
        _ = u := by rw [jiP0, sP1, jP1]
    have g1t : (j * s * j⁻¹) * (u * t) * (j * s * j⁻¹)⁻¹ = u * τ := by
      calc (j * s * j⁻¹) * (u * t) * (j * s * j⁻¹)⁻¹ = j * (s * (j⁻¹ * (u * t) * j) * s⁻¹) * j⁻¹ := by
            group
        _ = u * τ := by rw [jiP1, hs1, jP2]
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨1, M.one_mem, by group, by group⟩
    · exact ⟨j * s * j⁻¹, M.mul_mem (M.mul_mem hjM hsM) (M.inv_mem hjM), g1u, g1t⟩
    · refine ⟨r * (j * s * j⁻¹), M.mul_mem hrM (M.mul_mem (M.mul_mem hjM hsM) (M.inv_mem hjM)), ?_, ?_⟩
      · rw [cc, g1u, hru]
      · rw [cc, g1t, rP2]

theorem tau_sq {t a₁ a₂ a₃ a₄ : Y} (F : FrameCalc t a₁ a₂ a₃ a₄) :
    a₁ * a₂ * a₃ * a₄ * (a₁ * a₂ * a₃ * a₄) = 1 := by
  have c12 : Commute a₁ a₂ := F.c₁₂
  have c13 : Commute a₁ a₃ := F.c₁₃
  have c14 : Commute a₁ a₄ := F.c₁₄
  have c23 : Commute a₂ a₃ := F.c₂₃
  have c24 : Commute a₂ a₄ := F.c₂₄
  have c34 : Commute a₃ a₄ := F.c₃₄
  have h12_3 : Commute (a₁ * a₂) a₃ := c13.mul_left c23
  have h123_4 : Commute (a₁ * a₂ * a₃) a₄ := (c14.mul_left c24).mul_left c34
  have h : (a₁ * a₂ * a₃ * a₄) ^ 2 = 1 := by
    rw [h123_4.mul_pow, h12_3.mul_pow, c12.mul_pow, pow_two a₁, pow_two a₂, pow_two a₃, pow_two a₄,
      F.s₁, F.s₂, F.s₃, F.s₄, F.tt, one_mul, F.tt]
  rwa [pow_two] at h

theorem t_tau_comm {t a₁ a₂ a₃ a₄ : Y} (F : FrameCalc t a₁ a₂ a₃ a₄) :
    t * (a₁ * a₂ * a₃ * a₄) = a₁ * a₂ * a₃ * a₄ * t := by
  have h1 : Commute t a₁ := F.t₁
  have h2 : Commute t a₂ := F.t₂
  have h3 : Commute t a₃ := F.t₃
  have h4 : Commute t a₄ := F.t₄
  exact ((h1.mul_right h2).mul_right h3).mul_right h4

theorem refl₁_act {t a₁ a₂ a₃ a₄ j : Y} (F : FrameCalc t a₁ a₂ a₃ a₄) (hj1 : j * a₁ * j⁻¹ = a₁ * t)
    (hj2 : j * a₂ = a₂ * j) (hj3 : j * a₃ = a₃ * j) (hj4 : j * a₄ = a₄ * j) (hjt : j * t = t * j) :
    j * (a₁ * a₂) * j⁻¹ = a₁ * a₂ * t ∧ j * (a₁ * a₂ * a₃ * a₄) * j⁻¹ = a₁ * a₂ * a₃ * a₄ * t ∧
      j * t * j⁻¹ = t := by
  have e2 := conj_eq_of_comm hj2
  have e3 := conj_eq_of_comm hj3
  have e4 := conj_eq_of_comm hj4
  refine ⟨?_, ?_, conj_eq_of_comm hjt⟩
  · calc j * (a₁ * a₂) * j⁻¹ = (j * a₁ * j⁻¹) * (j * a₂ * j⁻¹) := by group
      _ = a₁ * t * a₂ := by rw [hj1, e2]
      _ = a₁ * (t * a₂) := by group
      _ = a₁ * (a₂ * t) := by rw [F.t₂]
      _ = a₁ * a₂ * t := by group
  · calc j * (a₁ * a₂ * a₃ * a₄) * j⁻¹
        = (j * a₁ * j⁻¹) * (j * a₂ * j⁻¹) * (j * a₃ * j⁻¹) * (j * a₄ * j⁻¹) := by group
      _ = a₁ * t * a₂ * a₃ * a₄ := by rw [hj1, e2, e3, e4]
      _ = a₁ * (t * a₂) * a₃ * a₄ := by group
      _ = a₁ * (a₂ * t) * a₃ * a₄ := by rw [F.t₂]
      _ = a₁ * a₂ * (t * a₃) * a₄ := by group
      _ = a₁ * a₂ * (a₃ * t) * a₄ := by rw [F.t₃]
      _ = a₁ * a₂ * a₃ * (t * a₄) := by group
      _ = a₁ * a₂ * a₃ * (a₄ * t) := by rw [F.t₄]
      _ = a₁ * a₂ * a₃ * a₄ * t := by group

theorem refl₃_act {t a₁ a₂ a₃ a₄ r : Y} (F : FrameCalc t a₁ a₂ a₃ a₄) (hr3 : r * a₃ * r⁻¹ = a₃ * t)
    (hr1 : r * a₁ = a₁ * r) (hr2 : r * a₂ = a₂ * r) (hr4 : r * a₄ = a₄ * r) (hrt : r * t = t * r) :
    r * (a₁ * a₂) * r⁻¹ = a₁ * a₂ ∧ r * (a₁ * a₂ * a₃ * a₄) * r⁻¹ = a₁ * a₂ * a₃ * a₄ * t ∧
      r * t * r⁻¹ = t := by
  have e1 := conj_eq_of_comm hr1
  have e2 := conj_eq_of_comm hr2
  have e4 := conj_eq_of_comm hr4
  refine ⟨?_, ?_, conj_eq_of_comm hrt⟩
  · calc r * (a₁ * a₂) * r⁻¹ = (r * a₁ * r⁻¹) * (r * a₂ * r⁻¹) := by group
      _ = a₁ * a₂ := by rw [e1, e2]
  · calc r * (a₁ * a₂ * a₃ * a₄) * r⁻¹
        = (r * a₁ * r⁻¹) * (r * a₂ * r⁻¹) * (r * a₃ * r⁻¹) * (r * a₄ * r⁻¹) := by group
      _ = a₁ * a₂ * (a₃ * t) * a₄ := by rw [e1, e2, hr3, e4]
      _ = a₁ * a₂ * a₃ * (t * a₄) := by group
      _ = a₁ * a₂ * a₃ * (a₄ * t) := by rw [F.t₄]
      _ = a₁ * a₂ * a₃ * a₄ * t := by group

end Calc

section Frame

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y : Y}

theorem frameCalc_of (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) : FrameCalc t a₁ a₂ a₃ a₄ := by
  have hf := frame_fn H fr
  have hab := abelianOf H
  have htW := tmemOf H
  refine ⟨(stdOf H).datum.hz.sq, (hf 0).2, (hf 1).2, (hf 2).2, (hf 3).2, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · exact hab _ htW _ fr.h₁.2
  · exact hab _ htW _ fr.h₂.2
  · exact hab _ htW _ fr.h₃.2
  · exact hab _ htW _ fr.h₄.2
  · exact hab _ fr.h₁.2 _ fr.h₂.2
  · exact hab _ fr.h₁.2 _ fr.h₃.2
  · exact hab _ fr.h₁.2 _ fr.h₄.2
  · exact hab _ fr.h₂.2 _ fr.h₃.2
  · exact hab _ fr.h₂.2 _ fr.h₄.2
  · exact hab _ fr.h₃.2 _ fr.h₄.2

theorem exists_inverting (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {J : Subgroup Y}
    (hJ : J ∈ twinSet Ω[R] K) {a : Y} (ha : a ∈ J) (ha2 : a * a = t) :
    ∃ j ∈ J, j * a * j⁻¹ = a * t := by
  have hq := q8Of H hJ
  have ht1 : t ≠ 1 := (uniqInvOf H hJ).ne_one
  have hat : a ≠ 1 := by
    rintro rfl
    exact ht1 (by rw [← ha2, one_mul])
  have hat' : a ≠ t := by
    intro h
    rw [h] at ha2
    exact ht1 (ha2.symm.trans hq.z_sq)
  obtain ⟨m, hm, hnc⟩ := hq.exists_noncomm a ha hat hat'
  refine ⟨m, hm, ?_⟩
  have h1 := hq.comm_eq m hm a ha (fun e => hnc e.symm)
  calc m * a * m⁻¹ = (m * a * m⁻¹ * a⁻¹) * a := by group
    _ = t * a := by rw [h1]
    _ = a * t := hq.z_central a ha

end Frame

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c
