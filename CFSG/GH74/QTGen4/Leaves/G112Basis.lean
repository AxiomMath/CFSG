module

public import CFSG.GH74.QTGen4.Leaves.G112Bits
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.GH74.QTGen4.Leaves.G112

section Basis

open Module

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (b : Basis (Fin 4) (ZMod 2) V)

@[expose] noncomputable def enc (v : V) : Nat := encC (b.equivFun v)

theorem enc_add (v w : V) : enc b (v + w) = enc b v ^^^ enc b w := by
  simp only [enc, map_add, encC_add]

theorem enc_smul (a : ZMod 2) (v : V) : enc b (a • v) = if a = 1 then enc b v else 0 := by
  simp only [enc, map_smul, encC_smul]

theorem enc_lt (v : V) : enc b v < 16 := encC_lt _

theorem enc_inj {v w : V} (h : enc b v = enc b w) : v = w :=
  b.equivFun.injective (encC_inj _ _ h)

theorem enc_basis (i : Fin 4) : enc b (b i) = 2 ^ (i : Nat) := by
  have : b.equivFun (b i) = Pi.single i 1 := by
    ext j
    simp [Basis.equivFun_self, Pi.single_apply, eq_comm]
  rw [enc, this, encC_single]

theorem enc_testBit (v : V) (i : Fin 4) : (enc b v).testBit i = decide (b.equivFun v i = 1) :=
  encC_testBit _ _

@[expose] noncomputable def mat (σ : V →ₗ[ZMod 2] V) : Lin :=
  ⟨enc b (σ (b 0)), enc b (σ (b 1)), enc b (σ (b 2)), enc b (σ (b 3))⟩

theorem ap_enc (σ : V →ₗ[ZMod 2] V) (v : V) : ap (mat b σ) (enc b v) = enc b (σ v) := by
  have h0 : (enc b v).testBit 0 = decide (b.equivFun v 0 = 1) := enc_testBit b v 0
  have h1 : (enc b v).testBit 1 = decide (b.equivFun v 1 = 1) := enc_testBit b v 1
  have h2 : (enc b v).testBit 2 = decide (b.equivFun v 2 = 1) := enc_testBit b v 2
  have h3 : (enc b v).testBit 3 = decide (b.equivFun v 3 = 1) := enc_testBit b v 3
  rw [ap, h0, h1, h2, h3]
  conv_rhs => rw [← b.sum_equivFun v]
  simp only [map_smul, Fin.sum_univ_four, map_add, enc_add, enc_smul, mat,
    Basis.equivFun_apply]
  by_cases e0 : b.repr v 0 = 1 <;> by_cases e1 : b.repr v 1 = 1 <;>
    by_cases e2 : b.repr v 2 = 1 <;> by_cases e3 : b.repr v 3 = 1 <;> simp [e0, e1, e2, e3]

theorem mat_mul (σ τ : V ≃ₗ[ZMod 2] V) :
    mat b (σ * τ).toLinearMap = comp (mat b σ.toLinearMap) (mat b τ.toLinearMap) := by
  have h : ∀ i, ap (mat b σ.toLinearMap) (enc b (τ (b i))) = enc b ((σ * τ) (b i)) :=
    fun i => ap_enc b σ.toLinearMap (τ (b i))
  show (⟨enc b ((σ * τ) (b 0)), enc b ((σ * τ) (b 1)), enc b ((σ * τ) (b 2)),
      enc b ((σ * τ) (b 3))⟩ : Lin) =
    ⟨ap (mat b σ.toLinearMap) (enc b (τ (b 0))), ap (mat b σ.toLinearMap) (enc b (τ (b 1))),
      ap (mat b σ.toLinearMap) (enc b (τ (b 2))), ap (mat b σ.toLinearMap) (enc b (τ (b 3)))⟩
  rw [h 0, h 1, h 2, h 3]

theorem mat_one : mat b (1 : V ≃ₗ[ZMod 2] V).toLinearMap = idL := by
  show (⟨enc b (b 0), enc b (b 1), enc b (b 2), enc b (b 3)⟩ : Lin) = ⟨1, 2, 4, 8⟩
  rw [enc_basis, enc_basis, enc_basis, enc_basis]
  rfl

theorem mat_inj {σ τ : V ≃ₗ[ZMod 2] V} (h : mat b σ.toLinearMap = mat b τ.toLinearMap) :
    σ = τ := by
  have h0 : enc b (σ (b 0)) = enc b (τ (b 0)) := congrArg Lin.c0 h
  have h1 : enc b (σ (b 1)) = enc b (τ (b 1)) := congrArg Lin.c1 h
  have h2 : enc b (σ (b 2)) = enc b (τ (b 2)) := congrArg Lin.c2 h
  have h3 : enc b (σ (b 3)) = enc b (τ (b 3)) := congrArg Lin.c3 h
  apply LinearEquiv.toLinearMap_injective
  apply b.ext
  intro i
  fin_cases i
  · exact enc_inj b h0
  · exact enc_inj b h1
  · exact enc_inj b h2
  · exact enc_inj b h3

theorem bf_encC : ∀ x y : Fin 4 → ZMod 2,
    bf (encC x) (encC y) = decide (x 0 * y 3 + x 3 * y 0 + x 1 * y 2 + x 2 * y 1 = 1) := by
  decide

@[expose] def Jm : Fin 4 → Fin 4 → ZMod 2 := ![![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 1, 0, 0], ![1, 0, 0, 0]]

theorem bf_enc (B : LinearMap.BilinForm (ZMod 2) V) (hJ : ∀ i j, B (b i) (b j) = Jm i j)
    (v w : V) : bf (enc b v) (enc b w) = decide (B v w = 1) := by
  have key : ∀ x y : Fin 4 → ZMod 2,
      B (∑ i, x i • b i) (∑ j, y j • b j) = x 0 * y 3 + x 3 * y 0 + x 1 * y 2 + x 2 * y 1 := by
    intro x y
    simp only [Fin.sum_univ_four, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul, hJ, Jm]
    simp
    ring
  have hB : B v w = b.equivFun v 0 * b.equivFun w 3 + b.equivFun v 3 * b.equivFun w 0 +
      b.equivFun v 1 * b.equivFun w 2 + b.equivFun v 2 * b.equivFun w 1 := by
    have := key (b.equivFun v) (b.equivFun w)
    rwa [b.sum_equivFun, b.sum_equivFun] at this
  rw [enc, enc, bf_encC, hB]

end Basis

section Adapted

open Module

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

theorem V_add_self (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v]
  have : (2 : ZMod 2) = 0 := by decide
  rw [this, zero_smul]

theorem V_neg_eq (v : V) : -v = v := neg_eq_of_add_eq_zero_right (V_add_self v)

theorem V_sub_eq (a b : V) : a - b = a + b := by
  rw [sub_eq_add_neg, V_neg_eq]

theorem zmod2_eq_of_add_eq_zero : ∀ p q : ZMod 2, p + q = 0 → p = q := by decide

theorem two_indep (a c : ZMod 2) (p q : V) (hp : p ≠ 0) (hq : q ≠ 0) (hpq : p ≠ q)
    (h : a • p + c • q = 0) : a = 0 ∧ c = 0 := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases c with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · simp at h; exact absurd h hq
  · simp at h; exact absurd h hp
  · simp only [one_smul] at h
    exact absurd (eq_neg_of_add_eq_zero_left h |>.trans (V_neg_eq q)) hpq

theorem zmod2_two : (2 : ZMod 2) = 0 := by decide

theorem zmod2_add_self : ∀ a : ZMod 2, a + a = 0 := by decide

theorem exists_adapted_basis [Finite V] (B : LinearMap.BilinForm (ZMod 2) V)
    (hd : Module.finrank (ZMod 2) V = 4) (halt : ∀ v, B v v = 0)
    (hnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    (t : V ≃ₗ[ZMod 2] V) (hiso : ∀ v w, B (t v) (t w) = B v w) (ht2 : t * t = 1)
    (hrk : Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 2)
    (hB : ∀ v, B v (t v) = 0) (v₁ : V) (hv₁ : v₁ ≠ 0)
    (hv₁U : v₁ ∈ LinearMap.range (t.toLinearMap - LinearMap.id)) :
    ∃ b : Basis (Fin 4) (ZMod 2) V, b 0 = v₁ ∧ (∀ i j, B (b i) (b j) = Jm i j) ∧
      t (b 0) = b 0 ∧ t (b 1) = b 1 ∧ t (b 2) = b 2 + b 0 ∧ t (b 3) = b 3 + b 1 ∧
      ∀ u, u ∈ LinearMap.range (t.toLinearMap - LinearMap.id) ↔
        b.equivFun u 2 = 0 ∧ b.equivFun u 3 = 0 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : FiniteDimensional (ZMod 2) V := Module.finite_of_finrank_pos (by omega)
  set N : V →ₗ[ZMod 2] V := t.toLinearMap - LinearMap.id with hNdef
  have hNapp : ∀ v, N v = t v - v := fun v => by simp [hNdef]
  have htt : ∀ v, t (t v) = v := fun v => by
    have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) ht2
    simpa using this
  have htv : ∀ v, t v = v + N v := fun v => by rw [hNapp]; abel
  have hNN : ∀ v, N (N v) = 0 := fun v => by
    calc N (N v) = (v - t v) - (t v - v) := by rw [hNapp (N v), hNapp v, map_sub, htt]
      _ = (v + v) - (t v + t v) := by abel
      _ = 0 := by rw [V_add_self v, V_add_self (t v), sub_zero]
  have hU : LinearMap.range N = LinearMap.ker N := by
    have hle : LinearMap.range N ≤ LinearMap.ker N := by
      rintro u ⟨x, rfl⟩
      exact hNN x
    have hker : Module.finrank (ZMod 2) (LinearMap.ker N) = 2 := by
      have := LinearMap.finrank_range_add_finrank_ker N
      omega
    exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hrk, hker])
  have hN0 : ∀ u ∈ LinearMap.range N, N u = 0 := fun u hu => by
    have := hU ▸ hu
    exact LinearMap.mem_ker.1 this
  have hfix : ∀ u ∈ LinearMap.range N, t u = u := fun u hu => by
    rw [htv u, hN0 u hu, add_zero]
  obtain ⟨u₂, hu₂U, hu₂0, hu₂v⟩ : ∃ u₂ ∈ LinearMap.range N, u₂ ≠ 0 ∧ u₂ ≠ v₁ := by
    by_contra hcon
    push Not at hcon
    have hle : LinearMap.range N ≤ Submodule.span (ZMod 2) {v₁} := by
      intro u hu
      rw [Submodule.mem_span_singleton]
      by_cases h0 : u = 0
      · exact ⟨0, by simp [h0]⟩
      · exact ⟨1, by simp [hcon u hu h0]⟩
    have h1 := Submodule.finrank_mono hle
    have h2 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {v₁}) = 1 :=
      finrank_span_singleton hv₁
    omega
  obtain ⟨x₁₀, hx₁₀⟩ := hv₁U
  obtain ⟨x₂, hx₂⟩ := hu₂U
  have hindep : ∀ x₁ x₂ : V, N x₁ = v₁ → N x₂ = u₂ →
      LinearIndependent (ZMod 2) ![v₁, u₂, x₁, x₂] := by
    intro y₁ y₂ h1 h2
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg4 : g 0 • v₁ + g 1 • u₂ + g 2 • y₁ + g 3 • y₂ = 0 := by
      simpa [Fin.sum_univ_four] using hg
    have hN := congrArg N hg4
    simp only [map_add, map_smul, map_zero, h1, h2, hN0 v₁ ⟨x₁₀, hx₁₀⟩, hN0 u₂ ⟨x₂, hx₂⟩,
      smul_zero, zero_add] at hN
    obtain ⟨hg2, hg3⟩ := two_indep _ _ v₁ u₂ hv₁ hu₂0 (Ne.symm hu₂v) hN
    rw [hg2, hg3] at hg4
    simp only [zero_smul, add_zero] at hg4
    obtain ⟨hg0, hg1⟩ := two_indep _ _ v₁ u₂ hv₁ hu₂0 (Ne.symm hu₂v) hg4
    intro i
    fin_cases i
    · exact hg0
    · exact hg1
    · exact hg2
    · exact hg3
  have hbasis : ∀ x₁ x₂ : V, N x₁ = v₁ → N x₂ = u₂ →
      ∃ b : Basis (Fin 4) (ZMod 2) V, ⇑b = ![v₁, u₂, x₁, x₂] := fun x₁ x₂ h1 h2 =>
    ⟨basisOfLinearIndependentOfCardEqFinrank (hindep x₁ x₂ h1 h2) (by simp [hd]),
      coe_basisOfLinearIndependentOfCardEqFinrank _ _⟩
  have hsym : ∀ a b, B a b = B b a := fun a b => by
    have h := halt (a + b)
    simp only [map_add, LinearMap.add_apply, halt] at h
    have h' : B a b + B b a = 0 := by linear_combination h
    exact zmod2_eq_of_add_eq_zero _ _ h'
  have hUU : ∀ x y, B (N x) (N y) = 0 := fun x y => by
    have h1 : B (t x) (t y) = B x y := hiso x y
    have h2 : B x (t y) = B (t x) y := by
      have := hiso x (t y)
      rw [htt] at this
      exact this.symm
    have hNapp' : ∀ v, N v = t v + v := fun v => by rw [hNapp, V_sub_eq]
    rw [hNapp' x, hNapp' y]
    simp only [map_add, LinearMap.add_apply, h1, h2]
    linear_combination (B x y + B (t x) y) * zmod2_two
  have hxN : ∀ x, B x (N x) = 0 := fun x => by
    have hNapp' : N x = t x + x := by rw [hNapp, V_sub_eq]
    rw [hNapp', map_add, hB, halt]
    exact add_zero _
  have hxx : ∀ x₁ x₂ : V, N x₁ = v₁ → N x₂ = u₂ → B x₁ u₂ = B x₂ v₁ := by
    intro x₁ x₂ h1 h2
    have h := hxN (x₁ + x₂)
    rw [show N (x₁ + x₂) = v₁ + u₂ by rw [map_add, h1, h2]] at h
    simp only [map_add, LinearMap.add_apply] at h
    have e1 : B x₁ v₁ = 0 := by rw [← h1]; exact hxN x₁
    have e2 : B x₂ u₂ = 0 := by rw [← h2]; exact hxN x₂
    rw [e1, e2] at h
    have h' : B x₁ u₂ + B x₂ v₁ = 0 := by linear_combination h
    exact zmod2_eq_of_add_eq_zero _ _ h'
  have hBx2 : B v₁ x₂ = 1 := by
    obtain ⟨b0, hb0⟩ := hbasis x₁₀ x₂ hx₁₀ hx₂
    by_contra hne
    have h0 : B v₁ x₂ = 0 := by
      rcases zmod2_cases (B v₁ x₂) with h | h
      · exact h
      · exact absurd h hne
    have hz : B v₁ = 0 := by
      apply b0.ext
      intro i
      fin_cases i
      · simp [hb0, halt]
      · simp only [hb0]
        show B v₁ u₂ = 0
        rw [← hx₁₀, ← hx₂]; exact hUU _ _
      · simp only [hb0]
        show B v₁ x₁₀ = 0
        rw [hsym, ← hx₁₀]; exact hxN _
      · simp only [hb0]
        exact h0
    exact hv₁ (hnd v₁ fun w => by rw [hz]; rfl)
  set c : ZMod 2 := B x₁₀ x₂ with hc
  set x₁ : V := x₁₀ + c • v₁ with hx₁def
  have hNx₁ : N x₁ = v₁ := by
    rw [hx₁def, map_add, map_smul, hx₁₀, hN0 v₁ ⟨x₁₀, hx₁₀⟩, smul_zero, add_zero]
  have hBx12 : B x₁ x₂ = 0 := by
    rw [hx₁def]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hBx2,
      mul_one]
    rw [← hc]
    exact zmod2_add_self _
  obtain ⟨b, hb⟩ := hbasis x₁ x₂ hNx₁ hx₂
  have hb0 : b 0 = v₁ := by rw [hb]; rfl
  have hb1 : b 1 = u₂ := by rw [hb]; rfl
  have hb2 : b 2 = x₁ := by rw [hb]; rfl
  have hb3 : b 3 = x₂ := by rw [hb]; rfl
  have hxx' := hxx x₁ x₂ hNx₁ hx₂
  have hv1v1 : B v₁ v₁ = 0 := halt _
  have hv1u2 : B v₁ u₂ = 0 := by rw [← hNx₁, ← hx₂]; exact hUU _ _
  have hv1x1 : B v₁ x₁ = 0 := by rw [hsym, ← hNx₁]; exact hxN _
  have hu2v1 : B u₂ v₁ = 0 := by rw [hsym]; exact hv1u2
  have hu2x1 : B u₂ x₁ = 1 := by rw [hsym, hxx', hsym]; exact hBx2
  have hu2x2 : B u₂ x₂ = 0 := by rw [hsym, ← hx₂]; exact hxN _
  have hx1v1 : B x₁ v₁ = 0 := by rw [hsym]; exact hv1x1
  have hx1u2 : B x₁ u₂ = 1 := by rw [hsym]; exact hu2x1
  have hx2v1 : B x₂ v₁ = 1 := by rw [hsym]; exact hBx2
  have hx2u2 : B x₂ u₂ = 0 := by rw [hsym]; exact hu2x2
  have hx2x1 : B x₂ x₁ = 0 := by rw [hsym]; exact hBx12
  refine ⟨b, hb0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Jm, hb0, hb1, hb2, hb3, hv1v1, hv1u2, hv1x1, hBx2, hu2v1, halt, hu2x1, hu2x2, hx1v1,
        hx1u2, hBx12, hx2v1, hx2u2, hx2x1]
  · rw [hb0]; exact hfix v₁ ⟨x₁₀, hx₁₀⟩
  · rw [hb1]; exact hfix u₂ ⟨x₂, hx₂⟩
  · rw [hb2, hb0, htv x₁, hNx₁]
  · rw [hb3, hb1, htv x₂, hx₂]
  · intro u
    have hNb0 : N (b 0) = 0 := by rw [hb0]; exact hN0 v₁ ⟨x₁₀, hx₁₀⟩
    have hNb1 : N (b 1) = 0 := by rw [hb1]; exact hN0 u₂ ⟨x₂, hx₂⟩
    have hNb2 : N (b 2) = b 0 := by rw [hb2, hb0, hNx₁]
    have hNb3 : N (b 3) = b 1 := by rw [hb3, hb1, hx₂]
    constructor
    · rintro ⟨x, rfl⟩
      have hNx : N x = b.equivFun x 2 • b 0 + b.equivFun x 3 • b 1 := by
        have hx := b.sum_equivFun x
        simp only [Fin.sum_univ_four] at hx
        calc N x = N (b.equivFun x 0 • b 0 + b.equivFun x 1 • b 1 + b.equivFun x 2 • b 2 +
              b.equivFun x 3 • b 3) := by rw [hx]
          _ = b.equivFun x 2 • b 0 + b.equivFun x 3 • b 1 := by
            simp only [map_add, map_smul, hNb0, hNb1, hNb2, hNb3, smul_zero, zero_add]
      rw [hNx]
      simp
    · rintro ⟨h2, h3⟩
      have hu : b.equivFun u 0 • b 0 + b.equivFun u 1 • b 1 = u := by
        have := b.sum_equivFun u
        simp only [Fin.sum_univ_four, h2, h3, zero_smul, add_zero] at this
        exact this
      refine ⟨b.equivFun u 0 • b 2 + b.equivFun u 1 • b 3, ?_⟩
      rw [map_add, map_smul, map_smul, hNb2, hNb3]
      exact hu

end Adapted

end CFSG.GH74.QTGen4.Leaves.G112
