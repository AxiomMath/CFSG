module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.FrobSum
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.OrthFrame
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
open QuadraticMap Module

section
variable {K V : Type*} [Field K] [CharP K 2] [Finite K] [AddCommGroup V] [Module K V]

theorem char_two_cancel {a b : K} (h : a + b = 0) : a = b := by
  have := eq_neg_of_add_eq_zero_left h
  rwa [CharTwo.neg_eq] at this

theorem exists_fixed_decomp (σ : K ≃+* K) (hσ : ∀ x, σ x = x ^ 2)
    (T : V →ₛₗ[(σ : K →+* K)] V) (hTT : ∀ v, T (T v) = v) {ω : K} (hω : ω ^ 2 + ω = 1)
    (S : Submodule K V) (hS : ∀ v ∈ S, T v ∈ S) {v : V} (hv : v ∈ S) :
    ∃ u ∈ S, ∃ w ∈ S, T u = u ∧ T w = w ∧ v = u + ω • w := by
  have hω' : ω ^ 2 - ω = 1 := by rw [CharTwo.sub_eq_add]; exact hω
  have hTs : ∀ (c : K) v, T (c • v) = c ^ 2 • T v := fun c v => by
    rw [map_smulₛₗ, RingHom.coe_coe, hσ]
  have h2 : ∀ v : V, v + v = 0 := add_self_eq_zero_module K
  have hw : T (v + T v) = v + T v := by rw [map_add, hTT, add_comm]
  refine ⟨v + ω • (v + T v), S.add_mem hv (S.smul_mem _ (S.add_mem hv (hS v hv))), v + T v,
    S.add_mem hv (hS v hv), ?_, hw, ?_⟩
  · rw [map_add, hTs, hw]
    calc T v + ω ^ 2 • (v + T v)
        = (v + ω • (v + T v)) + (ω ^ 2 - ω) • (v + T v) + (T v - v) := by module
      _ = (v + ω • (v + T v)) + (1 : K) • (v + T v) + (T v - v) := by rw [hω']
      _ = (v + ω • (v + T v)) + (T v + T v) := by module
      _ = v + ω • (v + T v) := by rw [h2 (T v), add_zero]
  · calc v = v + (ω • (v + T v) + ω • (v + T v)) := by rw [h2, add_zero]
      _ = v + ω • (v + T v) + ω • (v + T v) := by abel

variable [FiniteDimensional K V]

theorem exists_good_vector (hK : Nat.card K = 4) (σ : K ≃+* K) (hσ : ∀ x, σ x = x ^ 2)
    (Q : QuadraticForm K V) (T : V →ₛₗ[(σ : K →+* K)] V) (hTT : ∀ v, T (T v) = v)
    (hTQ : ∀ v, Q (T v) = σ (Q v)) (W : Submodule K V) (hWT : ∀ v ∈ W, T v ∈ W)
    (hWnd : ∀ w ∈ W, (∀ u ∈ W, polar Q w u = 0) → w = 0) (hdim : 4 ≤ finrank K W) :
    ∃ e ∈ W, Q e = 0 ∧ polar Q e (T e) = 1 := by
  classical
  obtain ⟨ω, hω⟩ := F4_exists_omega hK
  have hTs : ∀ (c : K) v, T (c • v) = c ^ 2 • T v := fun c v => by
    rw [map_smulₛₗ, RingHom.coe_coe, hσ]
  have hQfix : ∀ u, T u = u → Q u = 0 ∨ Q u = 1 := fun u hu => by
    have := hTQ u
    rw [hu, hσ] at this
    exact F4_sq_eq_self this.symm
  have hBfix : ∀ u w, T u = u → T w = w → polar Q u w = 0 ∨ polar Q u w = 1 := by
    intro u w hu hw
    have := polar_semilinear T hTQ u w
    rw [hu, hw, hσ] at this
    exact F4_sq_eq_self this.symm
  have hdec := fun {S : Submodule K V} (hS : ∀ v ∈ S, T v ∈ S) {v : V} (hv : v ∈ S) =>
    exists_fixed_decomp σ hσ T hTT hω S hS hv
  have hext : ∀ (S : Submodule K V), (∀ v ∈ S, T v ∈ S) →
      (∀ u ∈ S, ∀ u' ∈ S, T u = u → T u' = u' → polar Q u u' = 0) →
      ∀ z ∈ S, ∀ z' ∈ S, polar Q z z' = 0 := by
    intro S hS hf z hz z' hz'
    obtain ⟨u, hu, w, hw, hTu, hTw, rfl⟩ := hdec hS hz
    obtain ⟨u', hu', w', hw', hTu', hTw', rfl⟩ := hdec hS hz'
    simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, smul_eq_mul,
      hf u hu u' hu' hTu hTu', hf u hu w' hw' hTu hTw', hf w hw u' hu' hTw hTu',
      hf w hw w' hw' hTw hTw']
    simp
  obtain ⟨x, hxW, hTx, hQx⟩ : ∃ x ∈ W, T x = x ∧ Q x = 1 := by
    by_contra hcon
    push Not at hcon
    have h0 : ∀ u ∈ W, ∀ u' ∈ W, T u = u → T u' = u' → polar Q u u' = 0 := by
      intro u hu u' hu' hTu hTu'
      have hs : T (u + u') = u + u' := by rw [map_add, hTu, hTu']
      have e1 : Q u = 0 := (hQfix u hTu).resolve_right (fun h => hcon u hu hTu h)
      have e2 : Q u' = 0 := (hQfix u' hTu').resolve_right (fun h => hcon u' hu' hTu' h)
      have e3 : Q (u + u') = 0 :=
        (hQfix _ hs).resolve_right (fun h => hcon _ (W.add_mem hu hu') hs h)
      have := QuadraticMap.map_add Q u u'
      rw [e1, e2, e3] at this
      simpa using this.symm
    have hall := hext W hWT h0
    have hbot : W = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      exact (Submodule.mem_bot K).mpr (hWnd w hw (fun u hu => hall w hw u hu))
    rw [hbot, finrank_bot] at hdim
    omega
  obtain ⟨y, hyW, hTy, hxy, hQy⟩ : ∃ y ∈ W, T y = y ∧ polar Q x y = 1 ∧ Q y = 1 := by
    by_contra hno
    push Not at hno
    obtain ⟨y₀, hy₀W, hTy₀, hxy₀⟩ : ∃ y ∈ W, T y = y ∧ polar Q x y = 1 := by
      by_contra h2
      push Not at h2
      have hx0 : ∀ v ∈ W, polar Q x v = 0 := by
        intro v hv
        obtain ⟨u, hu, w, hw, hTu, hTw, rfl⟩ := hdec hWT hv
        have hu0 : polar Q x u = 0 := (hBfix x u hTx hTu).resolve_right (h2 u hu hTu)
        have hw0 : polar Q x w = 0 := (hBfix x w hTx hTw).resolve_right (h2 w hw hTw)
        rw [polar_add_right, polar_smul_right, hu0, hw0]
        simp
      have := hWnd x hxW (fun u hu => hx0 u hu)
      rw [this, QuadraticMap.map_zero] at hQx
      exact zero_ne_one hQx
    have hQy₀ : Q y₀ = 0 := (hQfix y₀ hTy₀).resolve_right (hno y₀ hy₀W hTy₀ hxy₀)
    have key : ∀ z ∈ W, T z = z → polar Q x z = 0 → Q z = polar Q y₀ z := by
      intro z hz hTz hxz
      have hs : T (y₀ + z) = y₀ + z := by rw [map_add, hTy₀, hTz]
      have h1 : Q (y₀ + z) = 0 := (hQfix _ hs).resolve_right
        (hno _ (W.add_mem hy₀W hz) hs (by rw [polar_add_right, hxy₀, hxz, add_zero]))
      have := QuadraticMap.map_add Q y₀ z
      rw [h1, hQy₀, zero_add] at this
      exact char_two_cancel this.symm
    have hiso : ∀ z ∈ W, ∀ z' ∈ W, T z = z → T z' = z' → polar Q x z = 0 → polar Q x z' = 0 →
        polar Q z z' = 0 := by
      intro z hz z' hz' hTz hTz' hxz hxz'
      have hs : T (z + z') = z + z' := by rw [map_add, hTz, hTz']
      have hxs : polar Q x (z + z') = 0 := by rw [polar_add_right, hxz, hxz', add_zero]
      have k1 := key z hz hTz hxz
      have k2 := key z' hz' hTz' hxz'
      have k3 := key (z + z') (W.add_mem hz hz') hs hxs
      have := QuadraticMap.map_add Q z z'
      rw [k3, k1, k2, polar_add_right] at this
      simpa using this
    let Sx : Submodule K V := W ⊓ LinearMap.ker (polarBilin Q x)
    have hSx : ∀ v, v ∈ Sx ↔ v ∈ W ∧ polar Q x v = 0 := fun v => by
      simp [Sx, LinearMap.mem_ker, polarBilin_apply_apply]
    have hSxT : ∀ v ∈ Sx, T v ∈ Sx := by
      intro v hv
      rw [hSx] at hv ⊢
      refine ⟨hWT v hv.1, ?_⟩
      have := polar_semilinear T hTQ x v
      rw [hTx, hv.2, map_zero] at this
      exact this
    have hSxiso := hext Sx hSxT (fun u hu u' hu' hTu hTu' =>
      hiso u ((hSx u).mp hu).1 u' ((hSx u').mp hu').1 hTu hTu' ((hSx u).mp hu).2 ((hSx u').mp hu').2)
    let B' : LinearMap.BilinForm K W := (polarBilin Q).compl₁₂ W.subtype W.subtype
    have hB' : ∀ a b : W, B' a b = polar Q (a : V) (b : V) := fun a b => by
      simp [B', polarBilin_apply_apply]
    let x' : W := ⟨x, hxW⟩
    let y₀' : W := ⟨y₀, hy₀W⟩
    let φ : W →ₗ[K] K := B' x'
    have hφ : ∀ a : W, φ a = polar Q x (a : V) := fun a => hB' x' a
    have hφsurj : LinearMap.range φ = ⊤ := by
      rw [eq_top_iff]
      intro c _
      exact ⟨c • y₀', by rw [map_smul, hφ]; simp [y₀', hxy₀]⟩
    have hZdim : finrank K (LinearMap.ker φ) + 1 = finrank K W := by
      have := LinearMap.finrank_range_add_finrank_ker φ
      rw [hφsurj, finrank_top, finrank_self] at this
      omega
    have hZiso : ∀ a ∈ LinearMap.ker φ, ∀ b ∈ LinearMap.ker φ, B' a b = 0 := by
      intro a ha b hb
      rw [hB']
      rw [LinearMap.mem_ker, hφ] at ha hb
      exact hSxiso a.1 ((hSx _).mpr ⟨a.2, ha⟩) b.1 ((hSx _).mpr ⟨b.2, hb⟩)
    have hker : LinearMap.ker B' = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      rw [LinearMap.mem_ker] at ha
      refine (Submodule.mem_bot K).mpr (Subtype.ext ?_)
      have := hWnd a.1 a.2 (fun u hu => by
        have := congrArg (fun f => f ⟨u, hu⟩) ha
        simpa [hB'] using this)
      simpa using this
    have hle : LinearMap.ker φ ≤ B'.orthogonal (LinearMap.ker φ) := by
      intro a ha
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro b hb
      exact hZiso b hb a ha
    have h1 := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := B') (LinearMap.ker φ)
    have h2 := Submodule.finrank_mono hle
    rw [hker, inf_bot_eq, finrank_bot, add_zero] at h1
    omega
  refine ⟨x + ω • y, W.add_mem hxW (W.smul_mem _ hyW), ?_, ?_⟩
  · rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, polar_smul_right, hQx, hQy, hxy]
    simp only [smul_eq_mul]
    have : (1 : K) + ω * ω * 1 + ω * 1 = 1 + (ω ^ 2 + ω) := by ring
    rw [this, hω]
    exact CharTwo.add_self_eq_zero 1
  · have hTe : T (x + ω • y) = x + ω ^ 2 • y := by rw [map_add, hTs, hTx, hTy]
    rw [hTe, polar_add_left, polar_add_right, polar_add_right, polar_smul_left, polar_smul_right,
      polar_smul_left, polar_smul_right, polar_self_char_two, polar_self_char_two,
      polar_comm Q y x, hxy]
    simp only [smul_eq_mul, mul_one, mul_zero, zero_add, add_zero]
    exact hω

end

end CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
