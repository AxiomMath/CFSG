module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitConeCheck
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitDich
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainZ4Coord

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Matrix Stage1 CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem trace_toMat (M : Array ℕ) : (toMat 6 6 M).trace = bz (btrace M) := by
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_six, toMat_apply, btrace, bz_xor]
  rfl

theorem false_of_dual (A₀ A₁ A₂ C₀ C₁ C₂ Z₀ Z₁ Z₂ X : Mat6)
    (h₀ : A₀ * X + X * A₀ = C₀) (h₁ : A₁ * X + X * A₁ = C₁) (h₂ : A₂ * X + X * A₂ = C₂)
    (hZ : (Z₀ * A₀ + A₀ * Z₀) + ((Z₁ * A₁ + A₁ * Z₁) + (Z₂ * A₂ + A₂ * Z₂)) = 0)
    (hC : (Z₀ * C₀).trace + (Z₁ * C₁).trace + (Z₂ * C₂).trace = 1) : False := by
  have key : ∀ Z A : Mat6, (Z * (A * X + X * A)).trace = ((Z * A + A * Z) * X).trace := by
    intro Z A
    rw [mul_add, add_mul, Matrix.trace_add, Matrix.trace_add, ← mul_assoc, ← mul_assoc,
      Matrix.trace_mul_cycle Z X A]
  rw [← h₀, ← h₁, ← h₂, key, key, key, ← Matrix.trace_add, ← Matrix.trace_add, ← add_mul,
    ← add_mul, add_assoc, hZ, zero_mul, Matrix.trace_zero] at hC
  exact zero_ne_one hC

theorem two_smul_lift4_mul_left (A : Mat6) (M : Matrix (Fin 6) (Fin 6) (ZMod 4)) :
    (2 : ZMod 4) • (lift4 A * M) = (2 : ZMod 4) • lift4 (A * M.map red4) := by
  rw [two_smul_eq_lift4, Matrix.map_mul, map_red4_lift4]

theorem two_smul_lift4_mul_right (A : Mat6) (M : Matrix (Fin 6) (Fin 6) (ZMod 4)) :
    (2 : ZMod 4) • (M * lift4 A) = (2 : ZMod 4) • lift4 (M.map red4 * A) := by
  rw [two_smul_eq_lift4, Matrix.map_mul, map_red4_lift4]

theorem two_smul_lift4_inj {X Y : Mat6} (h : (2 : ZMod 4) • lift4 X = (2 : ZMod 4) • lift4 Y) :
    X = Y := by
  have h2 : (2 : ZMod 4) • lift4 (X + Y) = 0 := by
    rw [two_smul_lift4_add, h, ← add_smul, show (2 : ZMod 4) + 2 = 0 by decide, zero_smul]
  have := two_smul_lift4_eq_zero h2
  calc X = X + Y + Y := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = Y := by rw [this, zero_add]

theorem neg_two_smul (M : Matrix (Fin 6) (Fin 6) (ZMod 4)) :
    -((2 : ZMod 4) • M) = (2 : ZMod 4) • M := by
  rw [← neg_smul, show -(2 : ZMod 4) = 2 by decide]

theorem lift4_zero' : lift4 (0 : Mat6) = 0 := by
  ext i j
  simp [lift4]

theorem lift4_one' : lift4 (1 : Mat6) = 1 := by
  ext i j
  simp only [lift4, map_apply, one_apply]
  split_ifs <;> rfl

theorem sq_expand (τ X N : Mat6) (hsq : lift4 τ * lift4 τ = 1 + (2 : ZMod 4) • lift4 N) :
    (lift4 τ + (2 : ZMod 4) • lift4 X) * (lift4 τ + (2 : ZMod 4) • lift4 X) =
      1 + (2 : ZMod 4) • lift4 (N + (τ * X + X * τ)) := by
  have h1 : lift4 τ * ((2 : ZMod 4) • lift4 X) = (2 : ZMod 4) • lift4 (τ * X) := by
    rw [mul_smul_comm, two_smul_lift4_mul_left, map_red4_lift4]
  have h2 : (2 : ZMod 4) • lift4 X * lift4 τ = (2 : ZMod 4) • lift4 (X * τ) := by
    rw [smul_mul_assoc, two_smul_lift4_mul_right, map_red4_lift4]
  have h3 : (2 : ZMod 4) • lift4 X * ((2 : ZMod 4) • lift4 X) = 0 := by
    rw [smul_mul_assoc, mul_smul_comm, two_smul_two_smul]
  rw [add_mul, mul_add, mul_add, hsq, h1, h2, h3, add_zero, two_smul_lift4_add,
    two_smul_lift4_add]
  abel

theorem mul_expand_left (τ X : Mat6) (M : Matrix (Fin 6) (Fin 6) (ZMod 4)) :
    (lift4 τ + (2 : ZMod 4) • lift4 X) * M =
      lift4 τ * M + (2 : ZMod 4) • lift4 (X * M.map red4) := by
  rw [add_mul, smul_mul_assoc, two_smul_lift4_mul_left]

theorem mul_expand_right (τ X : Mat6) (M : Matrix (Fin 6) (Fin 6) (ZMod 4)) :
    M * (lift4 τ + (2 : ZMod 4) • lift4 X) =
      M * lift4 τ + (2 : ZMod 4) • lift4 (M.map red4 * X) := by
  rw [mul_add, mul_smul_comm, two_smul_lift4_mul_right]

theorem eq_of_add_eq_zero2 {N W : Mat6} (h : N + W = 0) : W = N := by
  calc W = N + W + N := by rw [add_comm N W, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = N := by rw [h, zero_add]

theorem sq_eqn (τ X N : Mat6) (hsq : lift4 τ * lift4 τ = 1 + (2 : ZMod 4) • lift4 N)
    (b : Bool) (h : (lift4 τ + (2 : ZMod 4) • lift4 X) * (lift4 τ + (2 : ZMod 4) • lift4 X) =
      if b then -1 else 1) :
    τ * X + X * τ = if b then N + 1 else N := by
  rw [sq_expand τ X N hsq] at h
  cases b
  · have h' : (2 : ZMod 4) • lift4 (N + (τ * X + X * τ)) = 0 := by
      have := congrArg (· - 1) h
      simpa only [Bool.false_eq_true, ↓reduceIte, add_sub_cancel_left, sub_self] using this
    exact eq_of_add_eq_zero2 (two_smul_lift4_eq_zero h')
  · have h' : (2 : ZMod 4) • lift4 (N + (τ * X + X * τ)) = (2 : ZMod 4) • lift4 1 := by
      have := congrArg (· - 1) h
      simp only [↓reduceIte, add_sub_cancel_left] at this
      rw [this, lift4_one']
      ext i j
      simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.one_apply, Matrix.smul_apply,
        smul_eq_mul]
      split_ifs <;> decide
    have := two_smul_lift4_inj h'
    simp only [↓reduceIte]
    calc τ * X + X * τ = N + (τ * X + X * τ) + N := by
          rw [add_comm N, add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = N + 1 := by rw [this, add_comm]

theorem comm_eqn (τ X : Mat6) (M : Matrix (Fin 6) (Fin 6) (ZMod 4)) (K : Mat6) (b : Bool)
    (hK : (if b then lift4 τ * M + M * lift4 τ else lift4 τ * M - M * lift4 τ) =
      (2 : ZMod 4) • lift4 K)
    (h : (lift4 τ + (2 : ZMod 4) • lift4 X) * M =
      if b then -(M * (lift4 τ + (2 : ZMod 4) • lift4 X))
      else M * (lift4 τ + (2 : ZMod 4) • lift4 X)) :
    M.map red4 * X + X * M.map red4 = K := by
  rw [mul_expand_left, mul_expand_right] at h
  refine two_smul_lift4_inj ?_
  rw [← hK, two_smul_lift4_add]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    symm
    calc lift4 τ * M - M * lift4 τ = (lift4 τ * M + (2 : ZMod 4) • lift4 (X * M.map red4)) -
          (2 : ZMod 4) • lift4 (X * M.map red4) - M * lift4 τ := by abel
      _ = (M * lift4 τ + (2 : ZMod 4) • lift4 (M.map red4 * X)) -
          (2 : ZMod 4) • lift4 (X * M.map red4) - M * lift4 τ := by rw [h]
      _ = (2 : ZMod 4) • lift4 (M.map red4 * X) + -((2 : ZMod 4) • lift4 (X * M.map red4)) := by
          abel
      _ = _ := by rw [neg_two_smul]
  · simp only [↓reduceIte] at h ⊢
    symm
    calc lift4 τ * M + M * lift4 τ = (lift4 τ * M + (2 : ZMod 4) • lift4 (X * M.map red4)) -
          (2 : ZMod 4) • lift4 (X * M.map red4) + M * lift4 τ := by abel
      _ = -(M * lift4 τ + (2 : ZMod 4) • lift4 (M.map red4 * X)) -
          (2 : ZMod 4) • lift4 (X * M.map red4) + M * lift4 τ := by rw [h]
      _ = -((2 : ZMod 4) • lift4 (M.map red4 * X)) + -((2 : ZMod 4) • lift4 (X * M.map red4)) := by
          abel
      _ = _ := by rw [neg_two_smul, neg_two_smul]

theorem coneGenCheck_parts {ε : Eps} {j : ℕ} (hj : coneGenCheck ε j = true) :
    toMat 6 6 (wordRows ε ((coneWords ε).getD j [])) *ᵥ (Pi.single 0 1 : V6) = Pi.single 0 1 ∧
    toMat 6 6 (wordRows ε ((coneWords ε).getD j [])) * toMat 6 6 tauRows =
      toMat 6 6 tauRows * toMat 6 6 (wordRows ε ((coneWords ε).getD j [])) ∧
    ∀ b : Bool, (if b then lift4 (toMat 6 6 tauRows) * prodW ε (c0Mat ε) ((coneWords ε).getD j []) +
        prodW ε (c0Mat ε) ((coneWords ε).getD j []) * lift4 (toMat 6 6 tauRows)
      else lift4 (toMat 6 6 tauRows) * prodW ε (c0Mat ε) ((coneWords ε).getD j []) -
        prodW ε (c0Mat ε) ((coneWords ε).getD j []) * lift4 (toMat 6 6 tauRows)) =
      (2 : ZMod 4) • lift4 (toMat 6 6 (coneK ε j b)) := by
  simp only [coneGenCheck, Bool.and_eq_true, beq_iff_eq] at hj
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hj
  have he₀ : (Pi.single 0 1 : V6) = toVec 6 1 := by rw [← toVec_two_pow' 0]; rfl
  refine ⟨by rw [he₀, mulVec_toVec, h2], by rw [← toMat_bmul, ← toMat_bmul, h1], fun b => ?_⟩
  cases b
  · have := congrArg toMat4 h3
    rw [toMat4_sub4, toMat4_mul4, toMat4_mul4, toMat4_lift2, toMat4_prod4, toMat4_add4,
      toMat4_lift2, ← two_smul (ZMod 4)] at this
    simpa only [Bool.false_eq_true, ↓reduceIte] using this
  · have := congrArg toMat4 h4
    rw [toMat4_add4, toMat4_mul4, toMat4_mul4, toMat4_lift2, toMat4_prod4, toMat4_add4,
      toMat4_lift2, ← two_smul (ZMod 4)] at this
    simpa only [↓reduceIte] using this

theorem dualCheck_parts {ε : Eps} {s₀ s₁ s₂ : Bool} (h : dualCheck ε s₀ s₁ s₂ = true) :
    let Z := coneDual ε s₀ s₁ s₂
    let O₁ := toMat 6 6 (wordRows ε ((coneWords ε).getD 0 []))
    let O₂ := toMat 6 6 (wordRows ε ((coneWords ε).getD 1 []))
    (toMat 6 6 Z.1 * toMat 6 6 tauRows + toMat 6 6 tauRows * toMat 6 6 Z.1) +
      ((toMat 6 6 Z.2.1 * O₁ + O₁ * toMat 6 6 Z.2.1) +
        (toMat 6 6 Z.2.2 * O₂ + O₂ * toMat 6 6 Z.2.2)) = 0 ∧
    (toMat 6 6 Z.1 * toMat 6 6 (if s₀ then bxor 6 coneN id6 else coneN)).trace +
      (toMat 6 6 Z.2.1 * toMat 6 6 (coneK ε 0 s₁)).trace +
      (toMat 6 6 Z.2.2 * toMat 6 6 (coneK ε 1 s₂)).trace = 1 := by
  simp only [dualCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · have := congrArg (toMat 6 6) h1
    simpa only [toMat_bxor, anti, toMat_bmul, toMat_zero6] using this
  · have := congrArg bz h2
    rw [bz_xor, bz_xor, bz_true] at this
    rw [← toMat_bmul, ← toMat_bmul, ← toMat_bmul, trace_toMat, trace_toMat, trace_toMat]
    exact this

section Cert


theorem splitConeCheck_parts (ε : Eps) :
    tauRows = CPrime.reflRows ε 1 ∧
    mul4 (lift2 tauRows) (lift2 tauRows) = add4 one4 (add4 (lift2 coneN) (lift2 coneN)) ∧
    coneGenCheck ε 0 = true ∧ coneGenCheck ε 1 = true ∧
      ∀ s₀ s₁ s₂, dualCheck ε s₀ s₁ s₂ = true := by
  have h := splitConeCheck_spec ε
  simp only [splitConeCheck, Bool.and_eq_true, beq_iff_eq, List.all_cons, List.all_nil,
    Bool.and_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, h4, fun s₀ s₁ s₂ => ?_⟩
  cases s₀ <;> cases s₁ <;> cases s₂ <;> simp_all

theorem tauMat_eq (ε : Eps) : tauMat ε = toMat 6 6 tauRows := by
  rw [tauMat, ← (splitConeCheck_parts ε).1]

theorem no_cone_lift (ε : Eps) (T : Matrix (Fin 6) (Fin 6) (ZMod 4))
    (hT : T.map red4 = tauMat ε) (s₀ s₁ s₂ : Bool) (h2 : T * T = if s₀ then -1 else 1)
    (h₁ : T * prodW ε (c0Mat ε) ((coneWords ε).getD 0 []) =
      if s₁ then -(prodW ε (c0Mat ε) ((coneWords ε).getD 0 []) * T)
      else prodW ε (c0Mat ε) ((coneWords ε).getD 0 []) * T)
    (h₂ : T * prodW ε (c0Mat ε) ((coneWords ε).getD 1 []) =
      if s₂ then -(prodW ε (c0Mat ε) ((coneWords ε).getD 1 []) * T)
      else prodW ε (c0Mat ε) ((coneWords ε).getD 1 []) * T) : False := by
  obtain ⟨htau, hsq, hg0, hg1, hdual⟩ := splitConeCheck_parts ε
  set τ := toMat 6 6 tauRows
  have hτ : tauMat ε = τ := by rw [tauMat, ← htau]
  obtain ⟨X, hX⟩ := eq_lift4_add T
  rw [hT, hτ] at hX
  have hsq' : lift4 τ * lift4 τ = 1 + (2 : ZMod 4) • lift4 (toMat 6 6 coneN) := by
    have := congrArg toMat4 hsq
    rwa [toMat4_mul4, toMat4_add4, toMat4_one4, toMat4_add4, toMat4_lift2, toMat4_lift2,
      ← two_smul (ZMod 4)] at this
  have E₀ := sq_eqn τ X _ hsq' s₀ (by rw [← hX]; exact h2)
  have hred : ∀ j, (prodW ε (c0Mat ε) ((coneWords ε).getD j [])).map red4 =
      toMat 6 6 (wordRows ε ((coneWords ε).getD j [])) := fun j => by
    rw [map_red4_prodW, urMat6_fst_eq]
  have E₁ := comm_eqn τ X _ _ s₁ ((coneGenCheck_parts hg0).2.2 s₁) (by rw [← hX]; exact h₁)
  have E₂ := comm_eqn τ X _ _ s₂ ((coneGenCheck_parts hg1).2.2 s₂) (by rw [← hX]; exact h₂)
  rw [hred] at E₁ E₂
  obtain ⟨hZ, hC⟩ := dualCheck_parts (hdual s₀ s₁ s₂)
  refine false_of_dual _ _ _ _ _ _ _ _ _ X ?_ E₁ E₂ hZ hC
  rw [E₀]
  cases s₀
  · rfl
  · simp only [↓reduceIte, toMat_bxor, toMat_id6]

end Cert

end CFSG.EvenSmallLie.OmegaEight.Chain
