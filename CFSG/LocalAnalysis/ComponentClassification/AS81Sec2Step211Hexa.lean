module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaStab

public section

namespace CFSG.ComponentClassification.AS81.Hexa

theorem foldl_xor_testBit (imgs : List ℕ) (L : List ℕ) (acc₁ acc₂ v w : ℕ) :
    L.foldl (fun acc i => if (v ^^^ w).testBit i then acc ^^^ imgs[i]! else acc) (acc₁ ^^^ acc₂) =
      L.foldl (fun acc i => if v.testBit i then acc ^^^ imgs[i]! else acc) acc₁ ^^^
        L.foldl (fun acc i => if w.testBit i then acc ^^^ imgs[i]! else acc) acc₂ := by
  induction L generalizing acc₁ acc₂ with
  | nil => rfl
  | cons i L ih =>
    simp only [List.foldl_cons]
    rw [← ih]
    congr 1
    rw [Nat.testBit_xor]
    cases v.testBit i <;> cases w.testBit i <;>
      simp only [Bool.xor_false, Bool.xor_true, Bool.not_true, Bool.not_false, ite_true,
        ite_false, Bool.false_eq_true]
    all_goals simp only [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm, Nat.xor_self,
      Nat.xor_zero]

theorem linV_xor (imgs : List ℕ) (v w : ℕ) : linV imgs (v ^^^ w) = linV imgs v ^^^ linV imgs w := by
  unfold linV
  have := foldl_xor_testBit imgs (List.range 6) 0 0 v w
  rwa [Nat.xor_zero] at this

@[expose] def linF (imgs : List ℕ) (h : ∀ v : Fin 64, linV imgs v.val < 64) (v : Fin 64) :
    Fin 64 :=
  ⟨linV imgs v.val, h v⟩

theorem linF_xorF (imgs : List ℕ) (h : ∀ v : Fin 64, linV imgs v.val < 64) (v w : Fin 64) :
    linF imgs h (xorF v w) = xorF (linF imgs h v) (linF imgs h w) :=
  Fin.ext (linV_xor imgs v.val w.val)

@[expose] def omegaImgs : List ℕ := [2, 3, 8, 12, 32, 48]

theorem omegaImgs_lt : ∀ v : Fin 64, linV omegaImgs v.val < 64 := by decide

@[expose] def omegaF (v : Fin 64) : Fin 64 := linF omegaImgs omegaImgs_lt v

theorem omegaF_omegaF_omegaF : ∀ v : Fin 64, omegaF (omegaF (omegaF v)) = v := by decide

@[expose] def omegaPerm : Equiv.Perm (Fin 64) where
  toFun := omegaF
  invFun v := omegaF (omegaF v)
  left_inv v := omegaF_omegaF_omegaF v
  right_inv v := omegaF_omegaF_omegaF v

theorem omegaPerm_apply (v : Fin 64) : omegaPerm v = omegaF v := rfl

theorem omegaPerm_ne_sq : omegaPerm ≠ omegaPerm * omegaPerm := fun h => by
  have := congrArg (fun σ : Equiv.Perm (Fin 64) => σ 1) h
  simp only [Equiv.Perm.mul_apply, omegaPerm_apply] at this
  exact absurd this (by decide)

theorem inv_omegaPerm_sq : (omegaPerm * omegaPerm)⁻¹ = omegaPerm := by
  rw [inv_eq_iff_mul_eq_one]
  exact Equiv.ext fun v => by
    simp only [Equiv.Perm.mul_apply, omegaPerm_apply, Equiv.Perm.one_apply]
    exact omegaF_omegaF_omegaF v

theorem omegaPerm_cube : omegaPerm * omegaPerm * omegaPerm = 1 :=
  Equiv.ext fun v => by
    simp only [Equiv.Perm.mul_apply, omegaPerm_apply, Equiv.Perm.one_apply]
    exact omegaF_omegaF_omegaF v

theorem conj_omegaPerm_eq {τ : Equiv.Perm (Fin 64)} {j : ℕ} (hj : Odd j) (hτj : τ ^ j = 1)
    (hτ : τ * omegaPerm * τ⁻¹ = omegaPerm ∨ τ * omegaPerm * τ⁻¹ = omegaPerm * omegaPerm) :
    τ * omegaPerm * τ⁻¹ = omegaPerm := by
  rcases hτ with h | h
  · exact h
  exfalso
  have h2 : τ * (omegaPerm * omegaPerm) * τ⁻¹ = omegaPerm := by
    calc τ * (omegaPerm * omegaPerm) * τ⁻¹
        = (τ * omegaPerm * τ⁻¹) * (τ * omegaPerm * τ⁻¹) := by group
      _ = omegaPerm * omegaPerm * omegaPerm * omegaPerm := by rw [h]; group
      _ = omegaPerm := by rw [omegaPerm_cube, one_mul]
  have key : ∀ m : ℕ,
      τ ^ (2 * m + 1) * omegaPerm * (τ ^ (2 * m + 1))⁻¹ = omegaPerm * omegaPerm := by
    intro m
    induction m with
    | zero => simpa using h
    | succ m ih =>
      calc τ ^ (2 * (m + 1) + 1) * omegaPerm * (τ ^ (2 * (m + 1) + 1))⁻¹
          = τ * (τ * (τ ^ (2 * m + 1) * omegaPerm * (τ ^ (2 * m + 1))⁻¹) * τ⁻¹) * τ⁻¹ := by
            rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, pow_succ, pow_succ]
            group
        _ = omegaPerm * omegaPerm := by
            rw [ih, h2]
            exact h
  obtain ⟨m, rfl⟩ := hj
  have := key m
  rw [hτj, one_mul, inv_one, mul_one] at this
  exact omegaPerm_ne_sq this

theorem omegaPerm_ne_one : omegaPerm ≠ 1 := fun h =>
  absurd (congrArg (fun σ : Equiv.Perm (Fin 64) => σ 1) h) (by decide)

theorem omegaPerm_mul_omegaPerm_ne_one : omegaPerm * omegaPerm ≠ 1 := fun h =>
  absurd (congrArg (fun σ : Equiv.Perm (Fin 64) => σ 1) h) (by decide)

theorem omegaPerm_pow_three : omegaPerm ^ 3 = 1 := by
  rw [pow_succ, pow_two]
  exact omegaPerm_cube

theorem omegaPerm_mul_omegaPerm_sq : (omegaPerm * omegaPerm) ^ 2 = omegaPerm := by
  rw [sq]
  calc omegaPerm * omegaPerm * (omegaPerm * omegaPerm)
      = omegaPerm * omegaPerm * omegaPerm * omegaPerm := by group
    _ = omegaPerm := by rw [omegaPerm_cube, one_mul]

theorem orderOf_omegaPerm : orderOf omegaPerm = 3 :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  orderOf_eq_prime omegaPerm_pow_three omegaPerm_ne_one

@[expose] def fixOvalsCheck : Bool :=
  [1, 2, 3].all fun a => [4, 8, 12].all fun c => [16, 32, 48].all fun e =>
    !(hexaOval[3]!).contains (a ^^^ c ^^^ e) ||
      [1, 2, 3].all fun b => [4, 8, 12].all fun d => [16, 32, 48].all fun f =>
        !(hexaOval[3]!).contains (b ^^^ d ^^^ f) ||
          !((hexaOval[4]!).contains (linV [a, b, c, d, e, f] 30) &&
            (hexaOval[4]!).contains (linV [a, b, c, d, e, f] 39)) ||
          [a, b, c, d, e, f] == [1, 2, 4, 8, 16, 32] ||
          [a, b, c, d, e, f] == [2, 3, 8, 12, 32, 48] ||
          [a, b, c, d, e, f] == [3, 1, 12, 4, 48, 16]

theorem fixOvalsCheck_eq : fixOvalsCheck = true := by decide

theorem linV_one : ∀ v : Fin 64, linV [1, 2, 4, 8, 16, 32] v.val = v.val := by decide

theorem linV_omega_sq :
    ∀ v : Fin 64, linV [3, 1, 12, 4, 48, 16] v.val = (omegaF (omegaF v)).val := by decide

theorem linV_21 (a b c d e f : ℕ) : linV [a, b, c, d, e, f] 21 = 0 ^^^ a ^^^ c ^^^ e := rfl

theorem linV_42 (a b c d e f : ℕ) : linV [a, b, c, d, e, f] 42 = 0 ^^^ b ^^^ d ^^^ f := rfl

theorem mem_of_mem_four {x a b c : ℕ} (h : x ∈ [0, a, b, c]) (h0 : x ≠ 0) : x ∈ [a, b, c] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with h | h | h | h
  · exact absurd h h0
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem fixOvals_spec {a b c d e f : ℕ} (ha : a ∈ [1, 2, 3]) (hb : b ∈ [1, 2, 3])
    (hc : c ∈ [4, 8, 12]) (hd : d ∈ [4, 8, 12]) (he : e ∈ [16, 32, 48]) (hf : f ∈ [16, 32, 48])
    (h21 : a ^^^ c ^^^ e ∈ hexaOval[3]!) (h42 : b ^^^ d ^^^ f ∈ hexaOval[3]!)
    (h30 : linV [a, b, c, d, e, f] 30 ∈ hexaOval[4]!)
    (h39 : linV [a, b, c, d, e, f] 39 ∈ hexaOval[4]!) :
    [a, b, c, d, e, f] = [1, 2, 4, 8, 16, 32] ∨ [a, b, c, d, e, f] = [2, 3, 8, 12, 32, 48] ∨
      [a, b, c, d, e, f] = [3, 1, 12, 4, 48, 16] := by
  have key := fixOvalsCheck_eq
  unfold fixOvalsCheck at key
  have k := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 key a ha) c hc) e he
  rw [List.contains_iff_mem.2 h21, Bool.not_true, Bool.false_or] at k
  have k' := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 k b hb) d hd) f hf
  rw [List.contains_iff_mem.2 h42, List.contains_iff_mem.2 h30, List.contains_iff_mem.2 h39]
    at k'
  simp only [Bool.not_true, Bool.false_or, Bool.and_self, Bool.or_eq_true, beq_iff_eq] at k'
  exact or_assoc.mp k'

theorem eq_of_fix_ovals {f : Equiv.Perm (Fin 64)} (hadd : ∀ v w, f (xorF v w) = xorF (f v) (f w))
    (hfix : ∀ i < 6, ∀ x : Fin 64, x.val ∈ hexaOval[i]! → (f x).val ∈ hexaOval[i]!) :
    f = 1 ∨ f = omegaPerm ∨ f = omegaPerm * omegaPerm := by
  have hf0 : f 0 = 0 := map_zero_of_add hadd
  have hne : ∀ x : Fin 64, x ≠ 0 → (f x).val ≠ 0 := fun x hx h =>
    hx (f.injective ((Fin.ext h).trans hf0.symm))
  have hlin : ∀ x : Fin 64, (f x).val =
      linV [(f 1).val, (f 2).val, (f 4).val, (f 8).val, (f 16).val, (f 32).val] x.val :=
    val_eq_linV hadd
  have ha := mem_of_mem_four (hfix 0 (by norm_num) 1 (by decide)) (hne 1 (by decide))
  have hb := mem_of_mem_four (hfix 0 (by norm_num) 2 (by decide)) (hne 2 (by decide))
  have hc := mem_of_mem_four (hfix 1 (by norm_num) 4 (by decide)) (hne 4 (by decide))
  have hd := mem_of_mem_four (hfix 1 (by norm_num) 8 (by decide)) (hne 8 (by decide))
  have he := mem_of_mem_four (hfix 2 (by norm_num) 16 (by decide)) (hne 16 (by decide))
  have hf := mem_of_mem_four (hfix 2 (by norm_num) 32 (by decide)) (hne 32 (by decide))
  have h21 : linV [(f 1).val, (f 2).val, (f 4).val, (f 8).val, (f 16).val, (f 32).val] 21 ∈
      hexaOval[3]! := by
    have h := hfix 3 (by norm_num) 21 (by decide)
    rw [hlin] at h
    exact h
  have h42 : linV [(f 1).val, (f 2).val, (f 4).val, (f 8).val, (f 16).val, (f 32).val] 42 ∈
      hexaOval[3]! := by
    have h := hfix 3 (by norm_num) 42 (by decide)
    rw [hlin] at h
    exact h
  have h30 : linV [(f 1).val, (f 2).val, (f 4).val, (f 8).val, (f 16).val, (f 32).val] 30 ∈
      hexaOval[4]! := by
    have h := hfix 4 (by norm_num) 30 (by decide)
    rw [hlin] at h
    exact h
  have h39 : linV [(f 1).val, (f 2).val, (f 4).val, (f 8).val, (f 16).val, (f 32).val] 39 ∈
      hexaOval[4]! := by
    have h := hfix 4 (by norm_num) 39 (by decide)
    rw [hlin] at h
    exact h
  rw [linV_21, Nat.zero_xor] at h21
  rw [linV_42, Nat.zero_xor] at h42
  rcases fixOvals_spec ha hb hc hd he hf h21 h42 h30 h39 with h | h | h
  · left
    refine Equiv.ext fun x => Fin.ext ?_
    rw [hlin, h, linV_one, Equiv.Perm.one_apply]
  · right; left
    refine Equiv.ext fun x => Fin.ext ?_
    rw [hlin, h, omegaPerm_apply]
    rfl
  · right; right
    refine Equiv.ext fun x => Fin.ext ?_
    rw [hlin, h, linV_omega_sq, Equiv.Perm.mul_apply, omegaPerm_apply, omegaPerm_apply]

@[expose] def shiftImgs : List ℕ := [4, 8, 16, 32, 1, 2]

theorem shiftImgs_lt : ∀ v : Fin 64, linV shiftImgs v.val < 64 := by decide

@[expose] def shiftF (v : Fin 64) : Fin 64 := linF shiftImgs shiftImgs_lt v

@[expose] def diagImgs : List ℕ := [1, 2, 8, 12, 48, 16]

theorem diagImgs_lt : ∀ v : Fin 64, linV diagImgs v.val < 64 := by decide

@[expose] def diagF (v : Fin 64) : Fin 64 := linF diagImgs diagImgs_lt v

theorem shiftF_three : ∀ v : Fin 64, shiftF (shiftF (shiftF v)) = v := by decide

theorem diagF_three : ∀ v : Fin 64, diagF (diagF (diagF v)) = v := by decide

@[expose] def shiftP : Equiv.Perm (Fin 64) where
  toFun := shiftF
  invFun v := shiftF (shiftF v)
  left_inv v := shiftF_three v
  right_inv v := shiftF_three v

@[expose] def diagP : Equiv.Perm (Fin 64) where
  toFun := diagF
  invFun v := diagF (diagF v)
  left_inv v := diagF_three v
  right_inv v := diagF_three v

theorem shiftF_shiftF_mem : ∀ v : Fin 64,
    (v.val ∈ hexaOval[1]! → (shiftF (shiftF v)).val ∈ hexaOval[0]!) ∧
    (v.val ∈ hexaOval[2]! → (shiftF (shiftF v)).val ∈ hexaOval[1]!) ∧
    (v.val ∈ hexaOval[0]! → (shiftF (shiftF v)).val ∈ hexaOval[2]!) ∧
    (v.val ∈ hexaOval[3]! → (shiftF (shiftF v)).val ∈ hexaOval[3]!) ∧
    (v.val ∈ hexaOval[4]! → (shiftF (shiftF v)).val ∈ hexaOval[4]!) ∧
    (v.val ∈ hexaOval[5]! → (shiftF (shiftF v)).val ∈ hexaOval[5]!) := by
  decide

theorem diagF_diagF_mem : ∀ v : Fin 64,
    (v.val ∈ hexaOval[0]! → (diagF (diagF v)).val ∈ hexaOval[0]!) ∧
    (v.val ∈ hexaOval[1]! → (diagF (diagF v)).val ∈ hexaOval[1]!) ∧
    (v.val ∈ hexaOval[2]! → (diagF (diagF v)).val ∈ hexaOval[2]!) ∧
    (v.val ∈ hexaOval[4]! → (diagF (diagF v)).val ∈ hexaOval[3]!) ∧
    (v.val ∈ hexaOval[5]! → (diagF (diagF v)).val ∈ hexaOval[4]!) ∧
    (v.val ∈ hexaOval[3]! → (diagF (diagF v)).val ∈ hexaOval[5]!) := by
  decide

@[expose] def scalF (i : Fin 3) (v : Fin 64) : Fin 64 :=
  if i = 0 then v else if i = 1 then omegaF v else omegaF (omegaF v)

theorem commutator_check : ∀ i j : Fin 3,
    shiftF (scalF i (diagF (scalF j 1))) ≠ diagF (scalF j (shiftF (scalF i 1))) := by
  decide

theorem eq_scalF_of {s : Equiv.Perm (Fin 64)}
    (hs : s = 1 ∨ s = omegaPerm ∨ s = omegaPerm * omegaPerm) :
    ∃ i : Fin 3, ∀ v, s v = scalF i v := by
  rcases hs with rfl | rfl | rfl
  · exact ⟨0, fun v => rfl⟩
  · exact ⟨1, fun v => rfl⟩
  · exact ⟨2, fun v => rfl⟩

theorem exists_scalF_eq_shiftF {f : Equiv.Perm (Fin 64)}
    (hfa : ∀ v w, f (xorF v w) = xorF (f v) (f w))
    (hf : ∀ v : Fin 64,
      (v.val ∈ hexaOval[0]! → (f v).val ∈ hexaOval[1]!) ∧
      (v.val ∈ hexaOval[1]! → (f v).val ∈ hexaOval[2]!) ∧
      (v.val ∈ hexaOval[2]! → (f v).val ∈ hexaOval[0]!) ∧
      (v.val ∈ hexaOval[3]! → (f v).val ∈ hexaOval[3]!) ∧
      (v.val ∈ hexaOval[4]! → (f v).val ∈ hexaOval[4]!) ∧
      (v.val ∈ hexaOval[5]! → (f v).val ∈ hexaOval[5]!)) :
    ∃ i : Fin 3, ∀ v, f v = shiftF (scalF i v) := by
  have hsa : ∀ v w : Fin 64,
      (shiftP⁻¹ * f) (xorF v w) = xorF ((shiftP⁻¹ * f) v) ((shiftP⁻¹ * f) w) := fun v w => by
    show shiftF (shiftF (f (xorF v w))) = xorF (shiftF (shiftF (f v))) (shiftF (shiftF (f w)))
    rw [hfa, shiftF, shiftF, linF_xorF, ← shiftF, ← shiftF, shiftF, linF_xorF]
    rfl
  have hsf : ∀ i < 6, ∀ x : Fin 64, x.val ∈ hexaOval[i]! →
      ((shiftP⁻¹ * f) x).val ∈ hexaOval[i]! := by
    intro i hi x hx
    show (shiftF (shiftF (f x))).val ∈ hexaOval[i]!
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hf x
    interval_cases i
    · exact (shiftF_shiftF_mem (f x)).1 (h0 hx)
    · exact (shiftF_shiftF_mem (f x)).2.1 (h1 hx)
    · exact (shiftF_shiftF_mem (f x)).2.2.1 (h2 hx)
    · exact (shiftF_shiftF_mem (f x)).2.2.2.1 (h3 hx)
    · exact (shiftF_shiftF_mem (f x)).2.2.2.2.1 (h4 hx)
    · exact (shiftF_shiftF_mem (f x)).2.2.2.2.2 (h5 hx)
  obtain ⟨i, hi⟩ := eq_scalF_of (eq_of_fix_ovals hsa hsf)
  refine ⟨i, fun v => ?_⟩
  rw [← hi]
  show f v = shiftF (shiftF (shiftF (f v)))
  rw [shiftF_three]

theorem exists_scalF_eq_diagF {g : Equiv.Perm (Fin 64)}
    (hga : ∀ v w, g (xorF v w) = xorF (g v) (g w))
    (hg : ∀ v : Fin 64,
      (v.val ∈ hexaOval[0]! → (g v).val ∈ hexaOval[0]!) ∧
      (v.val ∈ hexaOval[1]! → (g v).val ∈ hexaOval[1]!) ∧
      (v.val ∈ hexaOval[2]! → (g v).val ∈ hexaOval[2]!) ∧
      (v.val ∈ hexaOval[3]! → (g v).val ∈ hexaOval[4]!) ∧
      (v.val ∈ hexaOval[4]! → (g v).val ∈ hexaOval[5]!) ∧
      (v.val ∈ hexaOval[5]! → (g v).val ∈ hexaOval[3]!)) :
    ∃ j : Fin 3, ∀ v, g v = diagF (scalF j v) := by
  have hta : ∀ v w : Fin 64,
      (diagP⁻¹ * g) (xorF v w) = xorF ((diagP⁻¹ * g) v) ((diagP⁻¹ * g) w) := fun v w => by
    show diagF (diagF (g (xorF v w))) = xorF (diagF (diagF (g v))) (diagF (diagF (g w)))
    rw [hga, diagF, diagF, linF_xorF, ← diagF, ← diagF, diagF, linF_xorF]
    rfl
  have htg : ∀ i < 6, ∀ x : Fin 64, x.val ∈ hexaOval[i]! →
      ((diagP⁻¹ * g) x).val ∈ hexaOval[i]! := by
    intro i hi x hx
    show (diagF (diagF (g x))).val ∈ hexaOval[i]!
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hg x
    interval_cases i
    · exact (diagF_diagF_mem (g x)).1 (h0 hx)
    · exact (diagF_diagF_mem (g x)).2.1 (h1 hx)
    · exact (diagF_diagF_mem (g x)).2.2.1 (h2 hx)
    · exact (diagF_diagF_mem (g x)).2.2.2.1 (h3 hx)
    · exact (diagF_diagF_mem (g x)).2.2.2.2.1 (h4 hx)
    · exact (diagF_diagF_mem (g x)).2.2.2.2.2 (h5 hx)
  obtain ⟨j, hj⟩ := eq_scalF_of (eq_of_fix_ovals hta htg)
  refine ⟨j, fun v => ?_⟩
  rw [← hj]
  show g v = diagF (diagF (diagF (g v)))
  rw [diagF_three]

theorem exists_scalF_scalF_eq : ∀ i : Fin 3, ∃ j : Fin 3, ∀ v, scalF i (scalF j v) = v := by
  decide

@[expose] def axisProj0 (v : Fin 64) : Fin 64 := xorF (xorF v (diagF v)) (diagF (diagF v))

@[expose] def axisProj1 (v : Fin 64) : Fin 64 :=
  xorF (xorF v (omegaF (omegaF (diagF v)))) (omegaF (diagF (diagF v)))

@[expose] def axisProj2 (v : Fin 64) : Fin 64 :=
  xorF (xorF v (omegaF (diagF v))) (omegaF (omegaF (diagF (diagF v))))

theorem axisProj_cases : ∀ v : Fin 64, v ≠ 0 →
    axisProj0 v = 1 ∨ axisProj0 v = 2 ∨ axisProj0 v = 3 ∨ axisProj1 v = 4 ∨ axisProj1 v = 8 ∨
      axisProj1 v = 12 ∨ axisProj2 v = 16 ∨ axisProj2 v = 32 ∨ axisProj2 v = 48 := by
  decide

theorem eq_xorF_bits : ∀ w : Fin 64, w = xorF (xorF (xorF (xorF (xorF
    (if w.val.testBit 0 then 1 else 0) (if w.val.testBit 1 then 2 else 0))
    (if w.val.testBit 2 then 4 else 0)) (if w.val.testBit 3 then 8 else 0))
    (if w.val.testBit 4 then 16 else 0)) (if w.val.testBit 5 then 32 else 0) := by
  decide

theorem forall_of_closed (p : Fin 64 → Prop) (hxor : ∀ v w, p v → p w → p (xorF v w))
    (hω : ∀ v, p v → p (omegaF v)) (hS : ∀ v, p v → p (shiftF v))
    (hD : ∀ v, p v → p (diagF v)) {v : Fin 64} (hv0 : v ≠ 0) (hv : p v) (w : Fin 64) : p w := by
  have h0 : p (axisProj0 v) := hxor _ _ (hxor _ _ hv (hD _ hv)) (hD _ (hD _ hv))
  have h1 : p (axisProj1 v) :=
    hxor _ _ (hxor _ _ hv (hω _ (hω _ (hD _ hv)))) (hω _ (hD _ (hD _ hv)))
  have h2 : p (axisProj2 v) :=
    hxor _ _ (hxor _ _ hv (hω _ (hD _ hv))) (hω _ (hω _ (hD _ (hD _ hv))))
  have hω' : ∀ u u', omegaF u = u' → p u → p u' := fun u u' h hu => h ▸ hω u hu
  have hS' : ∀ u u', shiftF u = u' → p u → p u' := fun u u' h hu => h ▸ hS u hu
  have hone : p 1 := by
    rcases axisProj_cases v hv0 with h | h | h | h | h | h | h | h | h
    · rw [h] at h0; exact h0
    · rw [h] at h0; exact hω' 3 1 (by decide) (hω' 2 3 (by decide) h0)
    · rw [h] at h0; exact hω' 3 1 (by decide) h0
    · rw [h] at h1; exact hS' 16 1 (by decide) (hS' 4 16 (by decide) h1)
    · rw [h] at h1
      exact hS' 16 1 (by decide) (hS' 4 16 (by decide)
        (hω' 12 4 (by decide) (hω' 8 12 (by decide) h1)))
    · rw [h] at h1
      exact hS' 16 1 (by decide) (hS' 4 16 (by decide) (hω' 12 4 (by decide) h1))
    · rw [h] at h2; exact hS' 16 1 (by decide) h2
    · rw [h] at h2
      exact hS' 16 1 (by decide) (hω' 48 16 (by decide) (hω' 32 48 (by decide) h2))
    · rw [h] at h2; exact hS' 16 1 (by decide) (hω' 48 16 (by decide) h2)
  have h4 : p 4 := hS' 1 4 (by decide) hone
  have h16 : p 16 := hS' 4 16 (by decide) h4
  have h2' : p 2 := hω' 1 2 (by decide) hone
  have h8 : p 8 := hω' 4 8 (by decide) h4
  have h32 : p 32 := hω' 16 32 (by decide) h16
  have h0' : p 0 := hxor 1 1 hone hone
  rw [eq_xorF_bits w]
  refine hxor _ _ (hxor _ _ (hxor _ _ (hxor _ _ (hxor _ _ ?_ ?_) ?_) ?_) ?_) ?_ <;> split_ifs
  all_goals assumption

theorem ne_of_ovals {f g : Equiv.Perm (Fin 64)}
    (hfa : ∀ v w, f (xorF v w) = xorF (f v) (f w)) (hga : ∀ v w, g (xorF v w) = xorF (g v) (g w))
    (hf : ∀ v : Fin 64,
      (v.val ∈ hexaOval[0]! → (f v).val ∈ hexaOval[1]!) ∧
      (v.val ∈ hexaOval[1]! → (f v).val ∈ hexaOval[2]!) ∧
      (v.val ∈ hexaOval[2]! → (f v).val ∈ hexaOval[0]!) ∧
      (v.val ∈ hexaOval[3]! → (f v).val ∈ hexaOval[3]!) ∧
      (v.val ∈ hexaOval[4]! → (f v).val ∈ hexaOval[4]!) ∧
      (v.val ∈ hexaOval[5]! → (f v).val ∈ hexaOval[5]!))
    (hg : ∀ v : Fin 64,
      (v.val ∈ hexaOval[0]! → (g v).val ∈ hexaOval[0]!) ∧
      (v.val ∈ hexaOval[1]! → (g v).val ∈ hexaOval[1]!) ∧
      (v.val ∈ hexaOval[2]! → (g v).val ∈ hexaOval[2]!) ∧
      (v.val ∈ hexaOval[3]! → (g v).val ∈ hexaOval[4]!) ∧
      (v.val ∈ hexaOval[4]! → (g v).val ∈ hexaOval[5]!) ∧
      (v.val ∈ hexaOval[5]! → (g v).val ∈ hexaOval[3]!)) :
    f * g ≠ g * f := by
  obtain ⟨i, hi⟩ := exists_scalF_eq_shiftF hfa hf
  obtain ⟨j, hj⟩ := exists_scalF_eq_diagF hga hg
  intro hfg
  have h1 := congrArg (fun σ : Equiv.Perm (Fin 64) => σ 1) hfg
  simp only [Equiv.Perm.mul_apply] at h1
  rw [hi, hj, hj, hi] at h1
  exact commutator_check i j h1

end CFSG.ComponentClassification.AS81.Hexa
