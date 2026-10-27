module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6fP

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6f

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
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open scoped commutatorElement


local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

section Defs

variable {Y : Type} [Group Y]

abbrev tauE (t y : Y) : Y := y * t * y⁻¹

abbrev xE (t y h : Y) : Y := h * (y * t * y⁻¹) * h⁻¹

@[expose] def e3 (t y h : Y) : Subgroup Y := Subgroup.closure ({t, tauE t y, xE t y h} : Set Y)

theorem t_mem_e3 (t y h : Y) : t ∈ e3 t y h := Subgroup.subset_closure (by simp)

theorem tau_mem_e3 (t y h : Y) : tauE t y ∈ e3 t y h := Subgroup.subset_closure (by simp)

theorem x_mem_e3 (t y h : Y) : xE t y h ∈ e3 t y h := Subgroup.subset_closure (by simp)

theorem xE_eq (t y h : Y) : xE t y h = (h * y) * t * (h * y)⁻¹ := by
  simp only [xE]
  group

theorem inv_eq_self_of_sq {a : Y} (h : a * a = 1) : a⁻¹ = a := inv_eq_of_mul_eq_one_right h

end Defs

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y h : Y}

structure LCtx (n : ℕ) {Y : Type} [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ W : Subgroup Y) (a₁ a₂ a₃ a₄ y h : Y) where
  C : A6eCtx n R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y
  hx : AE6Hx Ω[R] W (u₁ * u₂) t (tauE t y) h
  hE : IsElemAbelian2 (e3 t y h) 3
  hEt : e3 t y h ≤ ae6P Ω[R] t
  hEτ : e3 t y h ≤ ae6P Ω[R] (tauE t y)
  hEx : e3 t y h ≤ ae6P Ω[R] (xE t y h)

section LCtxFacts

variable (Z : LCtx n R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h)

include Z in
theorem E3_facts :
    t * t = 1 ∧ tauE t y * tauE t y = 1 ∧ xE t y h * xE t y h = 1 ∧
      t * tauE t y = tauE t y * t ∧ t * xE t y h = xE t y h * t ∧
      tauE t y * xE t y h = xE t y h * tauE t y ∧ t ≠ 1 ∧ tauE t y ≠ 1 ∧ xE t y h ≠ 1 ∧
      tauE t y ≠ t ∧ xE t y h ≠ t ∧ xE t y h ≠ tauE t y ∧ xE t y h ≠ t * tauE t y := by
  have hd := Z.C.H.ex.1.datum
  have htt : t * t = 1 := hd.hz.sq
  have hττ : tauE t y * tauE t y = 1 := by
    simp only [tauE]
    calc y * t * y⁻¹ * (y * t * y⁻¹) = y * (t * t) * y⁻¹ := by group
      _ = 1 := by rw [htt]; group
  have hxx : xE t y h * xE t y h = 1 := by
    simp only [xE]
    calc h * (y * t * y⁻¹) * h⁻¹ * (h * (y * t * y⁻¹) * h⁻¹)
        = h * ((y * t * y⁻¹) * (y * t * y⁻¹)) * h⁻¹ := by group
      _ = 1 := by rw [hττ]; group
  have hsq := Z.hE.2
  have hcomm : ∀ {a b : Y}, a ∈ e3 t y h → b ∈ e3 t y h → a * b = b * a := fun ha hb =>
    TC.Thin.comm_of_sq hsq ha hb
  have htD : t ∈ ae6D Ω[R] W (u₁ * u₂) := Z.C.t_mem_D
  have hτD : tauE t y ∈ ae6D Ω[R] W (u₁ * u₂) := Z.C.tau_mem_D
  have hxD : xE t y h ∉ ae6D Ω[R] W (u₁ * u₂) := Z.hx.2.1
  have ht1 : t ≠ 1 := hd.hz.ne_one
  refine ⟨htt, hττ, hxx, hcomm (t_mem_e3 t y h) (tau_mem_e3 t y h),
    hcomm (t_mem_e3 t y h) (x_mem_e3 t y h), hcomm (tau_mem_e3 t y h) (x_mem_e3 t y h), ht1, ?_, ?_,
    A6Hx.tau_ne_t Z.C.H Z.C.fr, ?_, ?_, ?_⟩
  · intro e
    apply ht1
    have : t = y⁻¹ * (y * t * y⁻¹) * y := by group
    rw [this]
    simp only [tauE] at e
    rw [e]
    group
  · intro e
    exact hxD (by rw [e]; exact (ae6D Ω[R] W (u₁ * u₂)).one_mem)
  · intro e
    exact hxD (by rw [e]; exact htD)
  · intro e
    exact hxD (by rw [e]; exact hτD)
  · intro e
    exact hxD (by rw [e]; exact (ae6D Ω[R] W (u₁ * u₂)).mul_mem htD hτD)

include Z in
theorem E3_elems {e : Y} (he : e ∈ e3 t y h) :
    e = 1 ∨ e = t ∨ e = tauE t y ∨ e = xE t y h ∨ e = t * tauE t y ∨ e = t * xE t y h ∨
      e = tauE t y * xE t y h ∨ e = t * (tauE t y * xE t y h) := by
  obtain ⟨htt, hττ, hxx, htτ, htx, hτx, -⟩ := E3_facts Z
  exact ChainFrame.mem_closure_eight htt hττ hxx htτ htx hτx he

include Z in
theorem ae6P_le_normalizer {g : Y} (hcE : g * t * g⁻¹ ∈ e3 t y h)
    (hEc : e3 t y h ≤ ae6P Ω[R] (g * t * g⁻¹)) :
    ae6P Ω[R] (g * t * g⁻¹) ≤ Subgroup.normalizer (e3 t y h : Set Y) := by
  have fwd : ∀ q ∈ ae6P Ω[R] (g * t * g⁻¹), ∀ e ∈ e3 t y h, q * e * q⁻¹ ∈ e3 t y h := by
    intro q hq e he
    rcases comm_ae6P_conj Z.C g hq (hEc he) with h' | h'
    · rw [h']
      exact he
    · rw [h']
      exact (e3 t y h).mul_mem he hcE
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro e
  refine ⟨fwd q hq e, fun he => ?_⟩
  have := fwd q⁻¹ ((ae6P Ω[R] (g * t * g⁻¹)).inv_mem hq) (q * e * q⁻¹) he
  simpa [mul_assoc] using this

include Z in
theorem ae6P_le_L_t : ae6P Ω[R] t ≤ ae6L Ω[R] t (tauE t y) (xE t y h) :=
  iSup₂_le fun J hJ => le_iSup₂_of_le J (Or.inl (Or.inl hJ)) le_rfl

include Z in
theorem ae6P_le_L_tau : ae6P Ω[R] (tauE t y) ≤ ae6L Ω[R] t (tauE t y) (xE t y h) :=
  iSup₂_le fun J hJ => le_iSup₂_of_le J (Or.inl (Or.inr hJ)) le_rfl

include Z in
theorem ae6P_le_L_x : ae6P Ω[R] (xE t y h) ≤ ae6L Ω[R] t (tauE t y) (xE t y h) :=
  iSup₂_le fun J hJ => le_iSup₂_of_le J (Or.inr hJ) le_rfl

include Z in
theorem L_le_normalizer :
    ae6L Ω[R] t (tauE t y) (xE t y h) ≤ Subgroup.normalizer (e3 t y h : Set Y) := by
  refine iSup₂_le fun J hJ => ?_
  rcases hJ with (hJ | hJ) | hJ
  · refine (A6Hx.le_ae6P hJ.1 hJ.2).trans ?_
    have := ae6P_le_normalizer Z (g := 1) (by simpa using t_mem_e3 t y h) (by simpa using Z.hEt)
    simpa using this
  · refine (A6Hx.le_ae6P hJ.1 hJ.2).trans ?_
    exact ae6P_le_normalizer Z (g := y) (tau_mem_e3 t y h) Z.hEτ
  · refine (A6Hx.le_ae6P hJ.1 hJ.2).trans ?_
    have hx' : xE t y h = (h * y) * t * (h * y)⁻¹ := xE_eq t y h
    have h1 : (h * y) * t * (h * y)⁻¹ ∈ e3 t y h := hx' ▸ x_mem_e3 t y h
    have h2 : e3 t y h ≤ ae6P Ω[R] ((h * y) * t * (h * y)⁻¹) := hx' ▸ Z.hEx
    have := ae6P_le_normalizer Z (g := h * y) h1 h2
    rwa [← hx'] at this

include Z in
theorem E3_le_L : e3 t y h ≤ ae6L Ω[R] t (tauE t y) (xE t y h) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro z (hz | hz | hz)
  · rw [hz]; exact ae6P_le_L_t Z (Z.hEt (t_mem_e3 t y h))
  · rw [hz]; exact ae6P_le_L_tau Z (Z.hEτ (tau_mem_e3 t y h))
  · rw [hz]; exact ae6P_le_L_x Z (Z.hEx (x_mem_e3 t y h))

include Z in
theorem exists_conj_t_of_mem_E3 {e : Y} (he : e ∈ e3 t y h) (h1 : e ≠ 1) :
    ∃ ℓ ∈ ae6L Ω[R] t (tauE t y) (xE t y h), ℓ * t * ℓ⁻¹ = e := by
  obtain ⟨htt, hττ, hxx, htτ, htx, hτx, ht1, hτ1, hx1, hτt, hxt, hxτ, hxtτ⟩ := E3_facts Z
  set L := ae6L Ω[R] t (tauE t y) (xE t y h) with hL
  let Orb : Y → Prop := fun e => ∃ ℓ ∈ L, ℓ * t * ℓ⁻¹ = e
  have step : ∀ (g e : Y), g * t * g⁻¹ ∈ e3 t y h → e3 t y h ≤ ae6P Ω[R] (g * t * g⁻¹) →
      ae6P Ω[R] (g * t * g⁻¹) ≤ L → e ∈ e3 t y h → Orb e → e ≠ 1 → e ≠ g * t * g⁻¹ →
      Orb (e * (g * t * g⁻¹)) := by
    intro g e hcE hEc hPL he ⟨ℓ, hℓ, hℓe⟩ h1 hc
    obtain ⟨j, hj, hje⟩ := exists_move_ae6P_conj Z.C g (hEc he) h1 hc
    refine ⟨j * ℓ, L.mul_mem (hPL hj) hℓ, ?_⟩
    calc j * ℓ * t * (j * ℓ)⁻¹ = j * (ℓ * t * ℓ⁻¹) * j⁻¹ := by group
      _ = e * (g * t * g⁻¹) := by rw [hℓe, hje]
  have hxe := xE_eq t y h
  have hsq1 : ∀ {a : Y}, a * a = 1 → a⁻¹ = a := fun {a} h => inv_eq_self_of_sq h
  have stepT : ∀ e : Y, e ∈ e3 t y h → Orb e → e ≠ 1 → e ≠ t → Orb (e * t) := by
    intro e he ho h1 hc
    have := step 1 e (by simpa using t_mem_e3 t y h) (by simpa using Z.hEt)
      (by simpa using ae6P_le_L_t Z) he ho h1 (by simpa using hc)
    simpa using this
  have stepτ : ∀ e : Y, e ∈ e3 t y h → Orb e → e ≠ 1 → e ≠ tauE t y → Orb (e * tauE t y) :=
    fun e he ho h1 hc => step y e (tau_mem_e3 t y h) Z.hEτ (ae6P_le_L_tau Z) he ho h1 hc
  have stepX : ∀ e : Y, e ∈ e3 t y h → Orb e → e ≠ 1 → e ≠ xE t y h → Orb (e * xE t y h) := by
    intro e he ho h1 hc
    have h1' : (h * y) * t * (h * y)⁻¹ ∈ e3 t y h := hxe ▸ x_mem_e3 t y h
    have h2' : e3 t y h ≤ ae6P Ω[R] ((h * y) * t * (h * y)⁻¹) := hxe ▸ Z.hEx
    have h3' : ae6P Ω[R] ((h * y) * t * (h * y)⁻¹) ≤ L := hxe ▸ ae6P_le_L_x Z
    have := step (h * y) e h1' h2' h3' he ho h1 (hxe ▸ hc)
    rwa [← hxe] at this
  have key : ∀ {a b : Y}, a * a = 1 → a * b = 1 → b = a := fun {a b} ha hab =>
    (inv_eq_of_mul_eq_one_right hab).symm.trans (inv_eq_self_of_sq ha)
  have o_t : Orb t := ⟨1, L.one_mem, by group⟩
  have mem_t := t_mem_e3 t y h
  have mem_τ := tau_mem_e3 t y h
  have mem_x := x_mem_e3 t y h
  have mul_mem' : ∀ {a b : Y}, a ∈ e3 t y h → b ∈ e3 t y h → a * b ∈ e3 t y h :=
    fun ha hb => (e3 t y h).mul_mem ha hb
  have o_tτ : Orb (t * tauE t y) := stepτ t mem_t o_t ht1 (Ne.symm hτt)
  have o_τ : Orb (tauE t y) := by
    have := stepT (t * tauE t y) (mul_mem' mem_t mem_τ) o_tτ
      (fun e => hτt (key htt e)) (fun e => hτ1 (mul_left_cancel (e.trans (mul_one t).symm)))
    have e : t * tauE t y * t = tauE t y := by rw [htτ, mul_assoc, htt, mul_one]
    rwa [e] at this
  have o_tx : Orb (t * xE t y h) := stepX t mem_t o_t ht1 (Ne.symm hxt)
  have o_x : Orb (xE t y h) := by
    have := stepT (t * xE t y h) (mul_mem' mem_t mem_x) o_tx
      (fun e => hxt (key htt e)) (fun e => hx1 (mul_left_cancel (e.trans (mul_one t).symm)))
    have e : t * xE t y h * t = xE t y h := by rw [htx, mul_assoc, htt, mul_one]
    rwa [e] at this
  have o_xτ : Orb (xE t y h * tauE t y) := stepτ _ mem_x o_x hx1 hxτ
  have o_xτt : Orb (xE t y h * tauE t y * t) := by
    refine stepT _ (mul_mem' mem_x mem_τ) o_xτ (fun e => hxτ (key hxx e).symm) ?_
    intro e
    apply hxtτ
    calc xE t y h = xE t y h * (tauE t y * tauE t y) := by rw [hττ, mul_one]
      _ = xE t y h * tauE t y * tauE t y := (mul_assoc _ _ _).symm
      _ = t * tauE t y := by rw [e]
  rcases E3_elems Z he with e | e | e | e | e | e | e | e
  · exact absurd e h1
  · rw [e]; exact o_t
  · rw [e]; exact o_τ
  · rw [e]; exact o_x
  · rw [e]; exact o_tτ
  · rw [e]; exact o_tx
  · rw [e, hτx]; exact o_xτ
  · rw [e]
    have e2 : t * (tauE t y * xE t y h) = xE t y h * tauE t y * t := by
      calc t * (tauE t y * xE t y h) = (t * tauE t y) * xE t y h := by group
        _ = (tauE t y * t) * xE t y h := by rw [htτ]
        _ = tauE t y * (t * xE t y h) := by group
        _ = tauE t y * (xE t y h * t) := by rw [htx]
        _ = (tauE t y * xE t y h) * t := by group
        _ = (xE t y h * tauE t y) * t := by rw [hτx]
    rw [e2]; exact o_xτt

end LCtxFacts

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6f
